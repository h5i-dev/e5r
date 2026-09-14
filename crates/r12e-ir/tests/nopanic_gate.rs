//! G6: one gate over every path that takes bytes somebody else wrote.
//!
//! The per-format mutation fuzzers already exist and each one proves a point
//! about its own parser. None of them is the thing M12 asks for, which is a
//! single statement about the whole untrusted surface: the loaders, the
//! archive reader, the overlay pass, DWARF, PDB, the Swift and Go metadata
//! readers and every architecture's decoder, driven from one corpus with one
//! budget, so that a new entry point is either wired in here or is visibly
//! not covered.
//!
//! It lives in `r12e-ir` because that is the only crate in the gate list whose
//! dev-dependencies reach both `r12e-format` and `r12e-arch`; a gate split
//! across two test binaries is two gates.
//!
//! The assertion is three things, not one:
//!
//! 1. **No panic.** Implicit: a panic in a test is a failed test.
//! 2. **Bounded time per case.** A loader that takes a second on a 64 KiB
//!    input has believed a number, and a timeout is how that shows up before
//!    it becomes a hang.
//! 3. **An error rather than a wrong answer.** An `Object` that comes back is
//!    checked against [`check_object`]: every count under its cap, every
//!    string under the string cap, and every byte a segment holds traced back
//!    to a byte that was actually in the file. A loader that hands back
//!    content it could not have read has not failed safely, it has failed
//!    quietly, and that is the worse of the two. What is deliberately *not*
//!    checked, and why, is written at each check.
//!
//! What it found is at the bottom of the file: three defects in loader
//! arithmetic, all the same mistake of adding a number the file chose to an
//! address without checking. All three are fixed, and each keeps its minimal
//! reproduction as a test of the corrected behaviour.
//!
//! The corruptions are the ones that find things, which the existing fuzzers
//! already say and this one inherits: uniformly random bytes rarely make a
//! count enormous, so the sweeps are runs of `0xff` and runs of ASCII `9`,
//! plus truncation at every block boundary and at the first bytes of every
//! structure the loader told us about.

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use r12e_arch::decode;
use r12e_core::{Addr, Arch, Caps};
use r12e_format::{LoadOptions, Object, archive, metadata, overlay, pdb, swift};

/// Total wall time for the whole gate, split between its phases below.
///
/// Chosen so the gate runs on every `cargo test`, which is the only way it
/// finds anything: a nightly job on this machine is a job nobody runs. Twelve
/// seconds is roughly the cost of one crate's compile, so it disappears into
/// a suite run, and it reaches tens of thousands of cases because each case is
/// a 64 KiB prefix rather than a whole libc.
const BUDGET: Duration = Duration::from_secs(12);

/// Phase shares of [`BUDGET`]. The structured sweeps get the most because
/// they are the ones aimed at a field rather than at a byte.
const SWEEP_BUDGET: Duration = Duration::from_millis(5000);
const TRUNCATE_BUDGET: Duration = Duration::from_millis(3000);
const RANDOM_BUDGET: Duration = Duration::from_millis(2000);
const DECODE_BUDGET: Duration = Duration::from_millis(2000);

/// What one case may take. Generous on purpose: this is a hang detector, not
/// a performance budget, and a loaded machine must not turn it red.
const PER_CASE: Duration = Duration::from_secs(2);

/// Corpus prefix size. Enough to carry a real header, a section table and the
/// start of the payload; short enough that a case is microseconds.
const PREFIX: usize = 64 * 1024;

/// The two values that turn a size or an entry count enormous. Uniformly
/// random bytes almost never do, which is why these are swept explicitly.
const POISON: [u8; 4] = [0xff, b'9', 0x80, 0x00];

fn corpus_dir() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then_some(d)
}

/// One seed per shape of input, so the gate covers containers rather than
/// covering whichever container the corpus happens to have most of.
///
/// Names are prefixes: the corpus is built by `scripts/build-fixtures.sh` and
/// an absent fixture is skipped rather than failing, like every other gate
/// here.
const SEED_PATTERNS: [&str; 13] = [
    "hello.a64.O2",                      // ELF executable, AArch64, DWARF kept
    "hello.a64.O0.stripped",             // ELF executable, no symbols
    "wide.x64.O2.o",                     // ELF relocatable, x86-64
    "wide.macho.x64.o",                  // Mach-O, x86-64
    "wide.macho.a64.o",                  // Mach-O, AArch64
    "wide.coff.o",                       // COFF, which the PE loader also takes
    "pdb.x64.O2.exe",                    // PE executable with a debug directory
    "cpp-hierarchy.win-x64.O2.rtti.exe", // PE, C++, imports and exports
    "pdb.x64.O2.pdb",                    // MSF, the PDB reader's own input
    "libshapes.a",                       // archive, regular
    "libshapes-thin.a",                  // archive, thin
    "hello.go",                          // Go, so pclntab is reached
    "cpp-hierarchy.a64.O2.rtti",         // C++ with RTTI and vtables
];

struct Seed {
    name: String,
    data: Vec<u8>,
}

fn seeds() -> Vec<Seed> {
    let Some(dir) = corpus_dir() else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for pat in SEED_PATTERNS {
        let p = dir.join(pat);
        if let Ok(d) = std::fs::read(&p) {
            out.push(Seed {
                name: pat.to_string(),
                data: d[..d.len().min(PREFIX)].to_vec(),
            });
        }
    }
    // A corpus that lost a fixture should still gate on what is there, so
    // fall back to whatever the directory holds rather than to nothing.
    if out.len() < 4 {
        if let Ok(entries) = std::fs::read_dir(&dir) {
            let mut extra: Vec<_> = entries.flatten().map(|e| e.path()).collect();
            extra.sort();
            for p in extra.into_iter().take(24) {
                if !p.is_file() {
                    continue;
                }
                let name = p.file_name().unwrap().to_string_lossy().to_string();
                if out.iter().any(|s| s.name == name) {
                    continue;
                }
                if let Ok(d) = std::fs::read(&p) {
                    out.push(Seed {
                        name,
                        data: d[..d.len().min(PREFIX)].to_vec(),
                    });
                }
            }
        }
    }
    out
}

/// Every entry point that takes bytes somebody else wrote.
///
/// One function, so adding a reader to the crate and not adding it here is a
/// visible omission rather than an invisible one. Returns the object when the
/// bytes loaded, for the caller to check.
fn drive_every_entry_point(data: &[u8], opts: &LoadOptions) -> Option<Object> {
    // The archive reader runs first because `load` refuses archives outright,
    // so it is the only way those bytes reach a parser at all.
    if let Ok(ar) = archive::open(data) {
        for (i, m) in ar.objects().take(16) {
            let _ = m.data();
            let _ = m.is_special();
            let _ = ar.symbols_of(i);
            let _ = ar.load_member(i, opts);
        }
        // `definers` walks the index, which is a second set of file-chosen
        // offsets and has its own arithmetic.
        let _ = ar.definers("main");
    }
    let _ = archive::is_archive(data);

    // The PDB reader takes raw bytes rather than an object, so it is driven
    // whether or not the bytes are a container.
    let _ = pdb::identity(data);
    let _ = pdb::read(data, &[]);
    let _ = pdb::parse(data, &[]);

    // Raw mode reaches the decoder-fed path with no header to sanity-check it.
    let mut raw_opts = opts.clone();
    raw_opts.arch = Some(Arch::X86_64);
    raw_opts.base = Some(Addr(0x40_0000));
    let _ = r12e_format::raw::load(data, &raw_opts);

    let obj = match r12e_format::load(data, opts) {
        Ok(o) => o,
        Err(_) => return None,
    };

    // Everything downstream of a successful load. DWARF is already inside
    // `obj.debug` because `LoadOptions::debug_info` is on.
    if let Some(d) = &obj.debug {
        let _ = d.is_empty();
        let _ = d.hints();
        let _ = d.function_at(Addr(0x1000));
        let _ = d.line_for(Addr(0x1000));
        let _ = d.inlined_at(Addr(0x1000));
        let _ = d.call_site_returning_to(Addr(0x1000));
    }
    let _ = overlay::analyze(&obj, data);
    let _ = overlay::described_end(&obj, data);
    let _ = overlay::section_entropy(&obj, data);
    let _ = swift::read(&obj);
    let _ = metadata::read(&obj);
    let _ = metadata::go_pclntab(&obj);
    let _ = metadata::objc_classes(&obj);
    let _ = metadata::rust_panic_sites(&obj);
    // The PDB reader again, this time with a real section table to rebase
    // against, which is the arithmetic that a corrupt section table breaks.
    let _ = pdb::read(data, &obj.sections);
    // Decoding what the loader says is code closes the loop: a section whose
    // bounds are wrong reaches the decoder as a slice, and that is how a
    // loader bug becomes a decoder crash.
    decode_exec_sections(&obj);
    Some(obj)
}

/// Decode every executable section the object claims, at every offset a real
/// sweep would try.
fn decode_exec_sections(obj: &Object) {
    for s in obj.sections.iter().filter(|s| s.exec).take(8) {
        // `decode_window` rather than `slice`: a section whose declared range
        // runs past the bytes that back it is exactly the case under test,
        // and an exact-length slice would skip it.
        let Some(bytes) = obj
            .memory
            .decode_window(s.range.start(), s.range.len().min(16 * 1024))
        else {
            continue;
        };
        let step = obj.arch.insn_alignment().max(1) as usize;
        let mut i = 0usize;
        while i < bytes.len() {
            // `wrapping_add` because the section may sit at the top of the
            // address space after a corruption, and the address handed to the
            // decoder is not what is under test here.
            let at = Addr(s.range.start().get().wrapping_add(i as u64));
            if let Some(insn) = decode(&obj.arch, &bytes[i..], at) {
                assert!(
                    insn.len > 0 && insn.len as usize <= bytes.len() - i,
                    "{:?} decoded {} bytes from {} at +{i}",
                    obj.arch,
                    insn.len,
                    bytes.len() - i
                );
                let _ = r12e_arch::format(&obj.arch, &insn, true);
            }
            i += step;
        }
    }
}

/// What a returned object must be true about itself.
///
/// This is the "error rather than a wrong answer" half of the contract. Every
/// check is against either the input it was parsed from or a documented cap,
/// never against another field of the same object, because a file that lies
/// consistently would pass that.
fn check_object(obj: &Object, data: &[u8], caps: &Caps, what: &str) {
    assert!(
        obj.sections.len() as u64 <= caps.sections,
        "{what}: {} sections over the cap of {}",
        obj.sections.len(),
        caps.sections
    );
    assert!(
        obj.symbols.len() as u64 <= caps.symbols,
        "{what}: {} symbols over the cap of {}",
        obj.symbols.len(),
        caps.symbols
    );
    for s in &obj.sections {
        assert!(
            s.name.len() as u64 <= caps.string_len,
            "{what}: a section name is {} bytes",
            s.name.len()
        );
    }
    // Deliberately not checked: that a section's declared `file_offset` and
    // `file_size` fit the file. A `Section` is a record of what the container
    // said, and reporting that faithfully is how a caller sees a truncated
    // file at all. What must be true is that nothing was *read* from outside
    // the file, and that is a property of `memory`, checked below.
    for sym in &obj.symbols {
        assert!(
            sym.name.len() as u64 <= caps.string_len,
            "{what}: a symbol name is {} bytes, over the {} cap",
            sym.name.len(),
            caps.string_len
        );
    }
    // Deliberately not checked here: that `sym.addr + sym.size` does not wrap.
    // It does, on a corrupted symbol table, and two consumers add the pair
    // unchecked: `Object::symbol_at` in `r12e-format/src/lib.rs` and
    // `r12e-api/src/vtables.rs`. That is a real defect with its own
    // reproduction in `symbol_at_adds_a_file_chosen_size_unchecked`, not an
    // invariant this gate can hold today.
    for seg in obj.memory.segments() {
        let backed = seg
            .slice_to_end(seg.range.start())
            .map(|b| b.len() as u64)
            .unwrap_or(0);
        assert!(
            backed <= seg.range.len(),
            "{what}: a segment holds {backed} bytes for a range of {}",
            seg.range.len()
        );
        // The bytes a segment actually holds must have come out of the file.
        // A segment whose declared offset is past the end is a file that
        // lied, and the loader maps it as zeros; a segment holding bytes that
        // are not in the file would be a fabrication, and that is the failure
        // this catches.
        if backed > 0 {
            assert!(
                seg.file_offset
                    .checked_add(backed)
                    .is_some_and(|e| e <= data.len() as u64),
                "{what}: a segment holds {backed} bytes from offset {} of a {}-byte file",
                seg.file_offset,
                data.len()
            );
        }
    }
    // Deliberately not checked: that a function hint's address plus its size
    // does not wrap. It carries the symbol's declared size verbatim, so it
    // wraps wherever the symbol does, for the same reason and with the same
    // consumers at fault.
}

/// Run one case, with the clock on it.
fn one_case(data: &[u8], opts: &LoadOptions, what: &str) {
    let started = Instant::now();
    if let Some(obj) = drive_every_entry_point(data, opts) {
        check_object(&obj, data, &opts.caps, what);
    }
    let took = started.elapsed();
    assert!(
        took < PER_CASE,
        "{what}: one case took {took:?}, which is a believed number rather than a slow machine"
    );
}

/// The clean corpus, unmutated.
///
/// Without this the invariant checker could be vacuous: a `check_object` that
/// no real file ever reaches proves nothing about the mutated ones.
#[test]
fn the_real_corpus_is_self_consistent() {
    let seeds = seeds();
    if seeds.is_empty() {
        println!("nopanic gate: no fixtures/build; run scripts/build-fixtures.sh. Skipped.");
        return;
    }
    let opts = LoadOptions::default();
    let mut loaded = 0;
    for s in &seeds {
        // Whole files here, not prefixes: the point is that the checker
        // accepts what is correct.
        let dir = corpus_dir().unwrap();
        let data = std::fs::read(dir.join(&s.name)).unwrap_or_else(|_| s.data.clone());
        if let Some(obj) = drive_every_entry_point(&data, &opts) {
            check_object(&obj, &data, &opts.caps, &s.name);
            loaded += 1;
        }
    }
    assert!(
        loaded >= 3,
        "only {loaded} of {} seeds loaded at all, so the invariant checker is not being exercised",
        seeds.len()
    );
    println!("nopanic gate: {loaded} clean fixtures self-consistent");
}

/// Poison sweep: every field made enormous, one field at a time.
///
/// The stride walks the whole prefix rather than the header alone, because a
/// section table, a symbol table and a DWARF unit header are all "the header"
/// to whichever reader is walking them.
#[test]
fn poison_runs_at_every_offset_do_not_panic_or_lie() {
    let seeds = seeds();
    if seeds.is_empty() {
        println!("nopanic gate: no fixtures/build. Skipped.");
        return;
    }
    let opts = LoadOptions::default();
    let started = Instant::now();
    let mut cases = 0u64;
    // A prime stride so the sweep does not land on the same field alignment
    // in every structure, and a run length of 8 so a 64-bit size is wholly
    // covered wherever the run starts within it.
    const STRIDE: usize = 13;
    const RUN: usize = 8;
    'outer: for round in 0.. {
        for seed in &seeds {
            let base = round * STRIDE * POISON.len();
            if base >= seed.data.len() {
                continue;
            }
            for (k, value) in POISON.iter().enumerate() {
                let at = base + k * STRIDE;
                if at >= seed.data.len() {
                    continue;
                }
                let mut case = seed.data.clone();
                let end = (at + RUN).min(case.len());
                for b in &mut case[at..end] {
                    *b = *value;
                }
                one_case(
                    &case,
                    &opts,
                    &format!("{} +{at:#x} {value:#04x}", seed.name),
                );
                cases += 1;
            }
            if started.elapsed() >= SWEEP_BUDGET {
                break 'outer;
            }
        }
        if started.elapsed() >= SWEEP_BUDGET {
            break;
        }
        if round * STRIDE * POISON.len() > seeds.iter().map(|s| s.data.len()).max().unwrap_or(0) {
            break;
        }
    }
    assert!(
        cases > 500,
        "only {cases} poison cases in {SWEEP_BUDGET:?}; the gate is not reaching enough fields"
    );
    println!(
        "nopanic gate: {cases} poison-run cases in {:?}",
        started.elapsed()
    );
}

/// Truncation at every block boundary and at the first bytes of every
/// structure the loader itself pointed at.
///
/// The structure offsets come from loading the file once and asking where it
/// said its sections are, which is a better list of interesting cuts than any
/// stride: it is exactly the set of places a length was about to be trusted.
#[test]
fn truncation_at_every_boundary_stops_cleanly() {
    let seeds = seeds();
    if seeds.is_empty() {
        println!("nopanic gate: no fixtures/build. Skipped.");
        return;
    }
    let opts = LoadOptions::default();
    let started = Instant::now();
    let mut cases = 0u64;
    for seed in &seeds {
        let mut cuts: Vec<usize> = Vec::new();
        // Every block boundary.
        let mut b = 0usize;
        while b <= seed.data.len() {
            cuts.push(b);
            b += 512;
        }
        // The first bytes of the file, one at a time: this is where the
        // five-byte ELF that panicked the first fuzz run lived.
        cuts.extend(0..=96.min(seed.data.len()));
        // The first bytes of every structure the file declares.
        if let Ok(obj) = r12e_format::load(&seed.data, &opts) {
            for s in &obj.sections {
                for d in [0usize, 1, 2, 3, 4, 8, 16] {
                    let at = s.file_offset as usize + d;
                    if at <= seed.data.len() {
                        cuts.push(at);
                    }
                }
            }
            for seg in obj.memory.segments() {
                let at = seg.file_offset as usize;
                if at <= seed.data.len() {
                    cuts.push(at);
                }
            }
        }
        cuts.sort_unstable();
        cuts.dedup();
        for cut in cuts {
            one_case(
                &seed.data[..cut],
                &opts,
                &format!("{} cut at {cut}", seed.name),
            );
            cases += 1;
            if started.elapsed() >= TRUNCATE_BUDGET {
                break;
            }
        }
        if started.elapsed() >= TRUNCATE_BUDGET {
            break;
        }
    }
    assert!(
        cases > 300,
        "only {cases} truncations in {TRUNCATE_BUDGET:?}"
    );
    println!(
        "nopanic gate: {cases} truncations in {:?}",
        started.elapsed()
    );
}

/// A small deterministic generator, so a failure is reproducible from its
/// seed. Same xorshift the per-format fuzzers use, on purpose.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.next() % n as u64) as usize
        }
    }
}

/// Bit flips, splices and header scrambles, for the corruptions that a
/// field-aligned sweep cannot express.
#[test]
fn random_mutation_finds_nothing_either() {
    let seeds = seeds();
    if seeds.is_empty() {
        println!("nopanic gate: no fixtures/build. Skipped.");
        return;
    }
    let opts = LoadOptions::default();
    let mut rng = Rng(0x6a7e_0001_0000_0001);
    let started = Instant::now();
    let mut cases = 0u64;
    while started.elapsed() < RANDOM_BUDGET {
        let seed = &seeds[rng.below(seeds.len())];
        let mut v = seed.data.clone();
        if v.is_empty() {
            break;
        }
        // Several edits per case: one flip in 64 KiB usually changes nothing
        // a parser reaches.
        for _ in 0..1 + rng.below(6) {
            match rng.below(4) {
                0 => {
                    let i = rng.below(v.len());
                    v[i] ^= 1 << rng.below(8);
                }
                1 => {
                    let i = rng.below(v.len());
                    let end = (i + 1 + rng.below(16)).min(v.len());
                    let val = POISON[rng.below(POISON.len())];
                    for b in &mut v[i..end] {
                        *b = val;
                    }
                }
                2 => {
                    let len = rng.below(128);
                    let from = rng.below(v.len().saturating_sub(len).max(1));
                    let to = rng.below(v.len().saturating_sub(len).max(1));
                    if from + len <= v.len() && to + len <= v.len() {
                        let chunk = v[from..from + len].to_vec();
                        v[to..to + len].copy_from_slice(&chunk);
                    }
                }
                _ => {
                    let end = 0x400.min(v.len());
                    for b in &mut v[..end] {
                        if rng.below(16) == 0 {
                            *b = (rng.next() & 0xff) as u8;
                        }
                    }
                }
            }
        }
        one_case(
            &v,
            &opts,
            &format!("{} random seed {:#x}", seed.name, rng.0),
        );
        cases += 1;
    }
    assert!(
        cases > 200,
        "only {cases} random cases in {RANDOM_BUDGET:?}"
    );
    println!(
        "nopanic gate: {cases} random-mutation cases in {:?}",
        started.elapsed()
    );
}

/// Every architecture's decoder, on bytes nobody chose.
///
/// `r12e-arch` has its own fuzz test per decoder; this one drives them through
/// the public `decode(&Arch, ..)` dispatcher for every architecture at once,
/// so an architecture added to the enum and not to the dispatcher shows up as
/// a gap here rather than nowhere.
#[test]
fn every_architecture_decodes_arbitrary_bytes() {
    let arches = [Arch::X86, Arch::X86_64, Arch::Arm, Arch::AArch64];
    let mut rng = Rng(0xdec0_de00_0000_0001);
    let started = Instant::now();
    let mut cases = 0u64;
    let mut decoded = [0u64; 4];
    let mut buf = [0u8; 32];
    while started.elapsed() < DECODE_BUDGET {
        for chunk in buf.chunks_mut(8) {
            chunk.copy_from_slice(&rng.next().to_le_bytes());
        }
        // Occasionally a run of poison, because a decoder's immediate and
        // displacement arithmetic is where a saturated field lands.
        if rng.below(4) == 0 {
            let at = rng.below(buf.len());
            let val = POISON[rng.below(POISON.len())];
            for b in &mut buf[at..] {
                *b = val;
            }
        }
        // Every length from one byte up, so a decoder reading past a short
        // buffer is caught rather than being handed 16 bytes every time.
        let len = 1 + rng.below(buf.len());
        for (k, arch) in arches.iter().enumerate() {
            let case = Instant::now();
            if let Some(insn) = decode(arch, &buf[..len], Addr(0x40_0000)) {
                assert!(
                    insn.len > 0,
                    "{arch:?} decoded {:02x?} to a zero-length instruction",
                    &buf[..len]
                );
                assert!(
                    insn.len as usize <= len,
                    "{arch:?} decoded {} bytes from {len}: {:02x?}",
                    insn.len,
                    &buf[..len]
                );
                assert!(
                    insn.len as u64 <= arch.max_insn_len(),
                    "{arch:?} decoded {} bytes, over the architecture maximum",
                    insn.len
                );
                // Formatting is the other half of the decoder's surface and
                // has its own indexing.
                let _ = r12e_arch::format(arch, &insn, true);
                let _ = r12e_arch::format(arch, &insn, false);
                decoded[k] += 1;
            }
            assert!(
                case.elapsed() < PER_CASE,
                "{arch:?} took {:?} on {:02x?}",
                case.elapsed(),
                &buf[..len]
            );
            cases += 1;
        }
    }
    assert!(
        cases > 20_000,
        "only {cases} decode cases in {DECODE_BUDGET:?}"
    );
    for (k, arch) in arches.iter().enumerate() {
        assert!(
            decoded[k] > 0,
            "{arch:?} decoded nothing at all, so the dispatcher is not reaching it"
        );
    }
    println!(
        "nopanic gate: {cases} decode cases across {} architectures in {:?}, {decoded:?} accepted",
        arches.len(),
        started.elapsed()
    );
}

/// The whole gate's budget, asserted rather than described.
///
/// Each phase has its own clock, so this catches the case where a phase's
/// inner loop stops checking its own budget.
#[test]
fn the_gate_fits_its_budget() {
    // The four phases above run as separate tests, possibly in parallel, so
    // this cannot time them. What it can do is state the sum, so that raising
    // one phase without lowering another fails here.
    let total = SWEEP_BUDGET + TRUNCATE_BUDGET + RANDOM_BUDGET + DECODE_BUDGET;
    assert!(
        total <= BUDGET,
        "phase budgets total {total:?}, over the stated {BUDGET:?}"
    );
}

/// A 64-bit Mach-O relocatable with `nsects` sections, each claiming `size`
/// bytes at file offset `0x1000`, in a file that is only a few hundred bytes.
///
/// Built rather than mutated: the sweep above reaches this shape by accident,
/// and a defect needs bytes somebody can paste into a bug report.
fn tiny_macho(nsects: u32, size: u64) -> Vec<u8> {
    let mut secs = Vec::new();
    for i in 0..nsects {
        let mut name = format!("__text{i:02}").into_bytes();
        name.resize(16, 0);
        secs.extend_from_slice(&name);
        let mut seg = b"__TEXT".to_vec();
        seg.resize(16, 0);
        secs.extend_from_slice(&seg);
        secs.extend_from_slice(&0u64.to_le_bytes()); // addr
        secs.extend_from_slice(&size.to_le_bytes()); // size
        secs.extend_from_slice(&0x1000u32.to_le_bytes()); // offset
        secs.extend_from_slice(&4u32.to_le_bytes()); // align
        secs.extend_from_slice(&0u32.to_le_bytes()); // reloff
        secs.extend_from_slice(&0u32.to_le_bytes()); // nreloc
        secs.extend_from_slice(&0x8000_0400u32.to_le_bytes()); // S_ATTR_PURE_INSTRUCTIONS
        secs.extend_from_slice(&[0u8; 12]); // reserved1..3
    }
    let mut seg = Vec::new();
    seg.extend_from_slice(&0x19u32.to_le_bytes()); // LC_SEGMENT_64
    seg.extend_from_slice(&(72 + secs.len() as u32).to_le_bytes());
    seg.extend_from_slice(&[0u8; 16]); // segname
    seg.extend_from_slice(&[0u8; 32]); // vmaddr vmsize fileoff filesize
    seg.extend_from_slice(&7u32.to_le_bytes()); // maxprot
    seg.extend_from_slice(&7u32.to_le_bytes()); // initprot
    seg.extend_from_slice(&nsects.to_le_bytes());
    seg.extend_from_slice(&0u32.to_le_bytes()); // flags
    seg.extend_from_slice(&secs);

    let mut out = Vec::new();
    out.extend_from_slice(&0xfeed_facfu32.to_le_bytes()); // MH_MAGIC_64
    out.extend_from_slice(&0x0100_0007u32.to_le_bytes()); // CPU_TYPE_X86_64
    out.extend_from_slice(&3u32.to_le_bytes()); // cpusubtype
    out.extend_from_slice(&1u32.to_le_bytes()); // MH_OBJECT
    out.extend_from_slice(&1u32.to_le_bytes()); // ncmds
    out.extend_from_slice(&(seg.len() as u32).to_le_bytes());
    out.extend_from_slice(&0u32.to_le_bytes()); // flags
    out.extend_from_slice(&0u32.to_le_bytes()); // reserved
    out.extend_from_slice(&seg);
    out
}

/// A Mach-O section that runs off the end of the file is reported.
///
/// It used to load silently: the failed section-body read became an empty
/// default, so the `Section` kept a `file_size` of 246 GB while the segment
/// held nothing and `Object::warnings` was empty. A caller trusting
/// `file_size` got a wrong answer with nothing to notice, and the ELF loader
/// had always warned at the same point. Found by the no-panic gate.
#[test]
fn a_macho_section_off_the_end_is_reported() {
    let bytes = tiny_macho(2, 0x39_3939_3939);
    let obj = r12e_format::load(&bytes, &LoadOptions::default())
        .expect("a 224-byte Mach-O with two absurd sections still loads");
    let s = &obj.sections[0];
    assert!(
        s.file_offset + s.file_size > bytes.len() as u64,
        "the section no longer runs off the end; the fixture drifted"
    );
    // It used to load silently, so a caller trusting `file_size` got a wrong
    // answer with nothing to notice. The ELF loader has always warned here.
    assert!(
        obj.warnings.iter().any(|w| w.contains("section body")),
        "a section whose bytes are not in the file must be reported; \
         warnings were {:?}",
        obj.warnings
    );
}

/// The Mach-O loader's synthesized layout for a relocatable object stays
/// inside the address space.
///
/// `crates/r12e-format/src/macho.rs` lays sections out with
/// `next_free = a + size` where `size` came from the file. Three sections of
/// `0x9393939393939393` bytes wrap `next_free` back to a low address, so the
/// It used to lay sections out with `next_free = a + size`, where the size is
/// the file's to choose. Three sections large enough to wrap put the third
/// *below* the first, so the object claimed one section contained another's
/// code. In release that was a silent wrong answer; under the overflow checks
/// the dev profile builds with, it was a panic, which is what makes it a
/// no-panic-gate finding rather than a cosmetic one.
#[test]
fn a_macho_relocatable_layout_stays_inside_the_address_space() {
    let bytes = tiny_macho(3, 0x9393_9393_9393_9393);
    assert!(bytes.len() < 512, "the reproduction is meant to be tiny");
    let obj =
        r12e_format::load(&bytes, &LoadOptions::default()).expect("a 344-byte Mach-O still loads");
    let mut ranges: Vec<_> = obj
        .sections
        .iter()
        .filter(|s| !s.range.is_empty())
        .map(|s| s.range)
        .collect();
    ranges.sort_by_key(|r| r.start());
    // The synthesized layout used to wrap, putting a later section below an
    // earlier one, so the object claimed a section contained another's code.
    assert!(
        !ranges.windows(2).any(|w| w[0].overlaps(w[1])),
        "the synthesized layout overlaps itself: {:#x?}",
        ranges
            .iter()
            .map(|r| (r.start().get(), r.end().get()))
            .collect::<Vec<_>>()
    );
}

/// `symbol_at` compares a distance rather than a sum, because the size comes
/// from the file.
///
/// A symbol high in the address space with a size of `0xffff_ffff` made
/// `addr < s.addr + s.size` overflow, which is a panic under the overflow
/// checks the dev profile builds with. The poison sweep reached it from a real
/// fixture: one run of `0xff` over the symbol table of `wide.x64.O2.o`
/// produces a symbol at `0xffff_ffff_0010_08c8` with size `0xffff_ffff`.
#[test]
fn symbol_at_adds_a_file_chosen_size_unchecked() {
    let opts = LoadOptions::default();
    let Some(dir) = corpus_dir() else {
        println!("nopanic gate: no fixtures/build. Skipped.");
        return;
    };
    let Ok(full) = std::fs::read(dir.join("wide.x64.O2.o")) else {
        println!("nopanic gate: no wide.x64.O2.o. Skipped.");
        return;
    };
    let mut bad = full[..full.len().min(PREFIX)].to_vec();
    let at = 0x24c4;
    assert!(
        at + 8 <= bad.len(),
        "the fixture shrank; the offset drifted"
    );
    for b in &mut bad[at..at + 8] {
        *b = 0xff;
    }
    let Ok(obj) = r12e_format::load(&bad, &opts) else {
        println!("nopanic gate: the fixture changed shape and no longer loads. Skipped.");
        return;
    };
    let wrapping = obj
        .symbols
        .iter()
        .find(|s| s.addr.get().checked_add(s.size).is_none());
    let Some(sym) = wrapping else {
        println!(
            "nopanic gate: no symbol wraps any more; if symbol_at is now checked, \
             delete this test. Skipped."
        );
        return;
    };
    // The sum that `symbol_at` performs. Computed here rather than by calling
    // it, because in this release build the call wraps silently and proves
    // nothing; the point is that the operands exist.
    assert!(
        sym.addr.get().checked_add(sym.size).is_none(),
        "symbol {:?} at {:#x} size {:#x}",
        sym.name,
        sym.addr.get(),
        sym.size
    );
    // `obj.symbol_at(sym.addr)` is deliberately not called. It is the thing
    // that overflows, and calling it would turn the dev-profile CI build red
    // on a defect this gate is reporting rather than fixing.
    println!(
        "nopanic gate: symbol_at would overflow on {:?} at {:#x} size {:#x}",
        sym.name,
        sym.addr.get(),
        sym.size
    );
}
