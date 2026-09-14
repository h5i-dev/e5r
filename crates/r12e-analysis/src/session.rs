//! Analysis on demand: a session that computes a part the first time it is
//! asked for, and remembers the answer.
//!
//! The eager [`analyze`](crate::analyze) shape made every caller decide, in
//! advance, what the command it was about to run would need. The CLI did that
//! by switching pieces off per command, which puts knowledge of the engine's
//! internals in the wrong place: a new command has to be told that it wants
//! strings but not cross references. A session turns it round. It owns the
//! object, and each of `functions`, `xrefs` and `strings` is computed on first
//! use and never twice, so a caller asks for what it wants and pays for that.
//!
//! Opening a session costs nothing: the loader has already parsed the header
//! and the symbol table, and nothing else runs until something asks.
//!
//! Dependencies between parts are the session's business rather than the
//! caller's. Cross references need functions, so asking for cross references
//! computes functions first. The no-return analysis is part of function
//! discovery rather than a stage after it, because it re-walks the callers it
//! affects and a caller asking for functions wants the corrected ones.
//!
//! With a [`Cache`] attached, each part is also looked up on disk before it is
//! computed and written back after. See [`crate::cache`] for what the key
//! covers and why a damaged file is a miss.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Mutex, OnceLock};

use r12e_core::Addr;
use r12e_format::Object;

use crate::cache::{Cache, ContentHash, Key, Lookup, Part};
use crate::codec;
use crate::data::{self, DataMap};
use crate::program::{self, Function, Options, Program};
use crate::progress::{Sink, Update};
use crate::strings::Found;
use crate::xref::XrefIndex;

/// Function discovery's whole answer, which the no-return pass produces in one
/// piece: the functions, which of them never return, and how many rounds it
/// took.
#[derive(Debug, Default)]
struct Core {
    functions: BTreeMap<Addr, Function>,
    noreturn: BTreeSet<Addr>,
    rounds: usize,
}

/// A binary open for analysis, with each part computed on first use.
pub struct Session {
    object: Object,
    opts: Options,
    /// Present only when the options name a thread count. Owning the pool here
    /// rather than building one per stage is what lets a lazy stage run on the
    /// same threads an eager analysis would have used.
    pool: Option<rayon::ThreadPool>,
    cache: Option<Cache>,
    content: Option<ContentHash>,
    /// Damaged cache files and unwritable cache directories. A library does
    /// not print; the caller decides whether a person sees these.
    warnings: Mutex<Vec<String>>,
    /// Where stage progress goes. `None` is the default and costs one branch
    /// per batch; see [`crate::progress`].
    progress: Option<Box<dyn Fn(Update) + Send + Sync>>,
    core: OnceLock<Core>,
    xrefs: OnceLock<XrefIndex>,
    strings: OnceLock<Vec<Found>>,
    /// Not cached, unlike the three above. It is derived from the functions
    /// and the container alone, so a cache hit on the functions would have to
    /// carry it or contradict it, and recomputing it costs one pass.
    data: OnceLock<DataMap>,
}

impl std::fmt::Debug for Session {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Session")
            .field("format", &self.object.format)
            .field("arch", &self.object.arch)
            .field("functions_computed", &self.core.get().is_some())
            .field("xrefs_computed", &self.xrefs.get().is_some())
            .field("strings_computed", &self.strings.get().is_some())
            .field("data_computed", &self.data.get().is_some())
            .finish()
    }
}

impl Session {
    /// Open a loaded object for analysis. Computes nothing.
    pub fn new(object: Object, opts: Options) -> Session {
        // A pool is built once here, not once per stage: rayon's default pool
        // is a global, and a session that asked for four threads must get four
        // threads for every part it later computes.
        let pool = match opts.threads {
            Some(n) if n > 0 => rayon::ThreadPoolBuilder::new().num_threads(n).build().ok(),
            _ => None,
        };
        Session {
            object,
            opts,
            pool,
            cache: None,
            content: None,
            warnings: Mutex::new(Vec::new()),
            progress: None,
            core: OnceLock::new(),
            xrefs: OnceLock::new(),
            strings: OnceLock::new(),
            data: OnceLock::new(),
        }
    }

    /// Read and write analysis parts through an on-disk cache.
    ///
    /// `content` identifies the bytes this object was loaded from. It is the
    /// caller's job to fold in anything else that changed the load, because
    /// the object cannot say what options produced it: see
    /// [`ContentHash::with`].
    pub fn with_cache(mut self, cache: Cache, content: ContentHash) -> Session {
        self.cache = Some(cache);
        self.content = Some(content);
        self
    }

    /// Be told which stage is running and how far through it is.
    ///
    /// The callback is entered from the sequential merge between parallel
    /// batches, so it is never called from two threads at once and never from
    /// inside an inner loop. It must still be `Send + Sync`, because which
    /// thread makes the call depends on the pool. A session with no callback
    /// pays one branch per batch; see [`crate::progress`] for the shape of an
    /// update and what a stage can and cannot say about its total.
    pub fn with_progress(mut self, f: impl Fn(Update) + Send + Sync + 'static) -> Session {
        self.progress = Some(Box::new(f));
        self
    }

    /// The sink the stages are handed.
    fn sink(&self) -> Sink<'_> {
        match &self.progress {
            Some(f) => Sink::new(f.as_ref()),
            None => Sink::none(),
        }
    }

    /// What the loader produced.
    pub fn object(&self) -> &Object {
        &self.object
    }

    /// The options this session analyzes under.
    pub fn options(&self) -> &Options {
        &self.opts
    }

    /// Anything worth telling a person about the cache. Empty in the ordinary
    /// case.
    pub fn warnings(&self) -> Vec<String> {
        self.warnings
            .lock()
            .map(|w| w.clone())
            .unwrap_or_else(|p| p.into_inner().clone())
    }

    /// True when that part has already been computed, so a caller can report
    /// what a run actually paid for.
    pub fn is_computed(&self, part: Part) -> bool {
        match part {
            Part::Functions => self.core.get().is_some(),
            Part::Xrefs => self.xrefs.get().is_some(),
            Part::Strings => self.strings.get().is_some(),
        }
    }

    /// Recovered functions by entry address, computing them if needed.
    pub fn functions(&self) -> &BTreeMap<Addr, Function> {
        &self.core().functions
    }

    /// Functions found never to return. Empty when the option is off.
    pub fn noreturn(&self) -> &BTreeSet<Addr> {
        &self.core().noreturn
    }

    /// Rounds of discovery it took.
    pub fn rounds(&self) -> usize {
        self.core().rounds
    }

    /// The cross reference index, computing it if needed. Empty when the
    /// option is off, which is the same answer the eager path gives.
    pub fn xrefs(&self) -> &XrefIndex {
        self.xrefs.get_or_init(|| {
            if !self.opts.xrefs {
                return XrefIndex::default();
            }
            if let Some((_, bytes)) = self.cached(Part::Xrefs)
                && let Some(index) = codec::decode_xrefs(&bytes)
            {
                return index;
            }
            // Reading the functions first keeps the borrow of the pool out of
            // the closure that runs on it.
            let functions = &self.core().functions;
            let object = &self.object;
            let sink = self.sink();
            let index = self.install(move || program::build_xrefs(object, functions, sink));
            self.store(Part::Xrefs, || codec::encode_xrefs(&index));
            index
        })
    }

    /// Strings, computing them if needed. Empty when the option is off.
    pub fn strings(&self) -> &[Found] {
        self.strings.get_or_init(|| {
            if !self.opts.strings {
                return Vec::new();
            }
            if let Some((_, bytes)) = self.cached(Part::Strings)
                && let Some(found) = codec::decode_strings(&bytes)
            {
                return found;
            }
            let object = &self.object;
            let opts = &self.opts.string_opts;
            let sink = self.sink();
            let found = self.install(move || program::scan_strings(object, opts, sink));
            self.store(Part::Strings, || codec::encode_strings(&found));
            found
        })
    }

    /// Regions that are provably data, computing them if needed. Empty when
    /// the option is off.
    ///
    /// Needs the functions, because a recovered jump table and a literal pool
    /// are both read off them, so asking for this computes those first.
    pub fn data(&self) -> &DataMap {
        self.data.get_or_init(|| {
            if !self.opts.data {
                return DataMap::default();
            }
            let functions = &self.core().functions;
            let object = &self.object;
            let sink = self.sink();
            self.install(move || {
                data::build(object, functions, data::Sources { pointers: true }, sink)
            })
        })
    }

    /// Force everything the options ask for and hand back the eager shape.
    ///
    /// This is what [`analyze`](crate::analyze) is: every caller in the
    /// workspace wants a `Program`, and a session that has computed all its
    /// parts is one.
    pub fn into_program(self) -> Program {
        // Order matters only for the cache: functions first means a run
        // interrupted after it writes the functions entry still leaves a
        // usable one.
        let _ = self.functions();
        let _ = self.xrefs();
        let _ = self.strings();
        // Not the data map: `Program` computes it on the first ask, so a
        // caller that never reads it does not pay a second decode of every
        // instruction. Off in the options still means empty, not deferred.
        if !self.opts.data {
            let _ = self.data();
        }
        let core = self.core.into_inner().unwrap_or_default();
        Program {
            object: self.object,
            functions: core.functions,
            xrefs: self.xrefs.into_inner().unwrap_or_default(),
            strings: self.strings.into_inner().unwrap_or_default(),
            rounds: core.rounds,
            noreturn: core.noreturn,
            data: self
                .data
                .into_inner()
                .map(OnceLock::from)
                .unwrap_or_default(),
        }
    }

    /// Discovery plus the no-return pass, memoized.
    fn core(&self) -> &Core {
        self.core.get_or_init(|| {
            if let Some((_, bytes)) = self.cached(Part::Functions)
                && let Some((functions, noreturn, rounds)) = codec::decode_functions(&bytes)
            {
                return Core {
                    functions,
                    noreturn,
                    rounds,
                };
            }
            let object = &self.object;
            let opts = &self.opts;
            let sink = self.sink();
            let core = self.install(move || {
                // One block table for the whole program: discovery and the
                // no-return re-walk share it, so a block the re-walk keeps is
                // the one every other function already names.
                let mut interner = crate::cfg::BlockInterner::default();
                let (mut functions, rounds) = program::discover(object, opts, &mut interner, sink);
                let noreturn =
                    program::refine_noreturn(object, &mut functions, opts, &mut interner, sink);
                program::publish_blocks(&mut functions, &mut interner);
                Core {
                    functions,
                    noreturn,
                    rounds,
                }
            });
            self.store(Part::Functions, || {
                codec::encode_functions(&core.functions, &core.noreturn, core.rounds)
            });
            core
        })
    }

    /// Run a stage on this session's threads.
    fn install<T: Send>(&self, f: impl FnOnce() -> T + Send) -> T {
        match &self.pool {
            Some(pool) => pool.install(f),
            None => f(),
        }
    }

    /// The key for one part, or `None` when no cache is attached.
    fn key(&self, part: Part) -> Option<Key> {
        let content = self.content.as_ref()?;
        self.cache.as_ref()?;
        Some(Key::derive(content, part, &self.opts.cache_bytes(part)))
    }

    /// Look one part up. A damaged file is recorded and then treated as a
    /// miss, and the file is removed so the next run does not trip over it.
    fn cached(&self, part: Part) -> Option<(Key, Vec<u8>)> {
        let cache = self.cache.as_ref()?;
        let key = self.key(part)?;
        match cache.get(part, &key) {
            Lookup::Hit(bytes) => Some((key, bytes)),
            Lookup::Miss => None,
            Lookup::Corrupt(why) => {
                self.warn(why);
                cache.remove(part, &key);
                None
            }
        }
    }

    /// Write one part back. The payload is only encoded when there is a cache
    /// to write it to.
    fn store(&self, part: Part, encode: impl FnOnce() -> Vec<u8>) {
        let (Some(cache), Some(key)) = (self.cache.as_ref(), self.key(part)) else {
            return;
        };
        if let Err(e) = cache.put(part, &key, &encode()) {
            self.warn(format!("could not write the analysis cache: {e}"));
        }
    }

    fn warn(&self, message: String) {
        match self.warnings.lock() {
            Ok(mut w) => w.push(message),
            Err(p) => p.into_inner().push(message),
        }
    }
}
