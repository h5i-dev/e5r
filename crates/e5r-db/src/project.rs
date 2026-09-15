//! The project file: everything needed to reopen an analysis session.
//!
//! A session is worth reopening only if it reopens on the same binary with the
//! same configuration; a project that silently attaches to a different build
//! is worse than no project, because every annotation in it is then a lie. So
//! the file records the binary by content as well as by path, and opening one
//! starts with a verdict on whether the bytes are the bytes it was made for.
//!
//! What it holds is references, not copies: the annotation log, the signature
//! libraries and the patch sets stay in their own files, which are the ones
//! that merge. The project is `key = value` lines sorted by key, so a diff
//! shows what changed about a session rather than a reordering of it.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fmt::Write as _;

use e5r_core::{Addr, Arch, Error, Result};

use crate::anchor::Fnv;

/// Magic on the first line.
const TAG: &str = "e5r-project";
/// On-disk format version. A reader refuses a version it does not know rather
/// than guessing at a layout.
pub const VERSION: u32 = 1;

/// Content digest of a binary.
///
/// FNV-1a, the same fold the anchors use: a project needs a stable identity
/// for a file, not a defence against someone forging one.
pub fn digest(data: &[u8]) -> u64 {
    let mut h = Fnv::new();
    h.u64(data.len() as u64);
    h.slice(data);
    h.finish()
}

/// The binary a project is about.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Binary {
    /// Where it was when the project was made.
    pub path: String,
    /// How big it is, checked before the digest because it is free.
    pub size: u64,
    /// Its content digest.
    pub hash: u64,
}

/// How the binary was loaded. Mirrors the loader's options rather than sharing
/// them, because the loader sits above this crate.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Load {
    /// Base address for a raw image, or a rebase for a relocatable one.
    pub base: Option<Addr>,
    /// Architecture override. It names a decoder, so a name no native decoder
    /// answers to is kept as a SLEIGH language id.
    pub arch: Option<Arch>,
    /// Which optional readers were enabled, by name. A set: they are flags,
    /// and two of them in the other order is the same configuration.
    pub readers: BTreeSet<String>,
}

/// A saved analysis session.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Project {
    /// The binary, by path and by content.
    pub binary: Binary,
    /// The load configuration.
    pub load: Load,
    /// Analysis options, free-form because the analyzer that owns their names
    /// sits above this crate and a project must not go stale when it grows one.
    pub analysis: BTreeMap<String, String>,
    /// The annotation log, if the session has one.
    pub log: Option<String>,
    /// Signature libraries, in precedence order.
    pub signatures: Vec<String>,
    /// Patch sets, in the order they apply.
    pub patches: Vec<String>,
}

/// Whether a binary is the one a project was made for.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// The same bytes at the same path.
    Same,
    /// The same bytes somewhere else: the session is valid and the path is
    /// stale, which is what a moved or re-fetched binary looks like.
    Moved {
        /// Where the project says it lives.
        recorded: String,
        /// Where these bytes came from.
        found: String,
    },
    /// Not the binary the project was made for.
    Different {
        /// The size the project recorded.
        recorded_size: u64,
        /// The size of the bytes given.
        found_size: u64,
        /// The digest the project recorded.
        recorded_hash: u64,
        /// The digest of the bytes given.
        found_hash: u64,
    },
}

impl Verdict {
    /// True when the session can be opened on these bytes.
    pub fn is_usable(&self) -> bool {
        !matches!(self, Verdict::Different { .. })
    }
}

impl fmt::Display for Verdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Verdict::Same => f.write_str("the binary this project was made for"),
            Verdict::Moved { recorded, found } => write!(
                f,
                "the same binary, moved: the project records {recorded}, this is {found}"
            ),
            Verdict::Different {
                recorded_size,
                found_size,
                recorded_hash,
                found_hash,
            } => write!(
                f,
                "a different binary: the project was made for {recorded_size} bytes \
                 ({recorded_hash:016x}), this is {found_size} bytes ({found_hash:016x})"
            ),
        }
    }
}

impl Project {
    /// A project for a binary that has just been read.
    pub fn for_binary(path: &str, data: &[u8]) -> Project {
        Project {
            binary: Binary {
                path: path.to_string(),
                size: data.len() as u64,
                hash: digest(data),
            },
            ..Project::default()
        }
    }

    /// Whether these bytes are the binary the project was made for.
    ///
    /// Content only, so it can never report a move; use [`Project::verify_at`]
    /// when the caller knows where the bytes came from, which is the only way
    /// a binary that is identical but relocated is distinguishable from one
    /// that never moved.
    pub fn verify(&self, data: &[u8]) -> Verdict {
        self.verify_at(&self.binary.path, data)
    }

    /// The same check when the path the bytes were read from is known.
    pub fn verify_at(&self, path: &str, data: &[u8]) -> Verdict {
        let found_size = data.len() as u64;
        let found_hash = digest(data);
        if found_size != self.binary.size || found_hash != self.binary.hash {
            return Verdict::Different {
                recorded_size: self.binary.size,
                found_size,
                recorded_hash: self.binary.hash,
                found_hash,
            };
        }
        if path != self.binary.path {
            return Verdict::Moved {
                recorded: self.binary.path.clone(),
                found: path.to_string(),
            };
        }
        Verdict::Same
    }

    /// Serialize: one `key = value` per line, sorted by key.
    pub fn to_text(&self) -> String {
        let mut lines: Vec<(String, String)> = vec![
            ("binary.path".into(), self.binary.path.clone()),
            ("binary.size".into(), self.binary.size.to_string()),
            ("binary.hash".into(), format!("{:016x}", self.binary.hash)),
        ];
        if let Some(base) = self.load.base {
            lines.push(("load.base".into(), format!("{:x}", base.get())));
        }
        if let Some(arch) = &self.load.arch {
            lines.push(("load.arch".into(), arch.name().to_string()));
        }
        for r in &self.load.readers {
            lines.push(("load.reader".into(), r.clone()));
        }
        for (k, v) in &self.analysis {
            lines.push((format!("analysis.{k}"), v.clone()));
        }
        if let Some(log) = &self.log {
            lines.push(("log".into(), log.clone()));
        }
        for s in &self.signatures {
            lines.push(("signatures".into(), s.clone()));
        }
        for p in &self.patches {
            lines.push(("patches".into(), p.clone()));
        }
        // Stable sort on the key alone, so lists keep the order they were
        // declared in while the file still reviews as a sorted diff.
        lines.sort_by(|a, b| a.0.cmp(&b.0));

        let mut s = String::with_capacity(128 + lines.len() * 48);
        let _ = writeln!(s, "{TAG} {VERSION}");
        let _ = writeln!(
            s,
            "# One key = value per line, sorted by key. Everything the session needs to"
        );
        let _ = writeln!(
            s,
            "# reopen on the same binary; the annotations, signatures and patches live in"
        );
        let _ = writeln!(s, "# the files named here.");
        for (k, v) in lines {
            let _ = writeln!(s, "{k} = {v}");
        }
        s
    }

    /// Parse a serialized project.
    pub fn from_text(text: &str) -> Result<Project> {
        let mut lines = text.lines();
        let header = lines.next().unwrap_or_default();
        let mut parts = header.split_whitespace();
        if parts.next() != Some(TAG) {
            return Err(Error::NotRecognized {
                expected: "e5r project",
            });
        }
        let version: u32 = parts
            .next()
            .and_then(|v| v.parse().ok())
            .ok_or(Error::BadField {
                field: "format version",
                value: 0,
                reason: "is missing from the header line",
            })?;
        if version > VERSION {
            return Err(Error::unsupported(format!(
                "project format version {version}; this build knows {VERSION}"
            )));
        }

        let mut p = Project::default();
        let mut seen = BTreeSet::new();
        for (n, line) in lines.enumerate() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let (key, value) = line
                .split_once(" = ")
                .ok_or_else(|| malformed(n, line, "is not `key = value`"))?;
            let (key, value) = (key.trim(), value.trim());
            let number = |radix: u32| {
                u64::from_str_radix(value, radix)
                    .map_err(|_| malformed(n, line, "does not hold a number"))
            };
            match key {
                "binary.path" => p.binary.path = value.to_string(),
                "binary.size" => p.binary.size = number(10)?,
                "binary.hash" => p.binary.hash = number(16)?,
                "load.base" => p.load.base = Some(Addr(number(16)?)),
                // An override names a decoder; anything the native names do
                // not cover is a SLEIGH language id.
                "load.arch" => {
                    p.load.arch = Some(value.parse().unwrap_or_else(|_| Arch::Sleigh(value.into())))
                }
                "load.reader" => {
                    p.load.readers.insert(value.to_string());
                }
                "log" => p.log = Some(value.to_string()),
                "signatures" => p.signatures.push(value.to_string()),
                "patches" => p.patches.push(value.to_string()),
                other => match other.strip_prefix("analysis.") {
                    Some(opt) if !opt.is_empty() => {
                        p.analysis.insert(opt.to_string(), value.to_string());
                    }
                    // A key nobody understands is a typo or a truncation, and
                    // dropping it would silently change the configuration.
                    _ => return Err(malformed(n, line, "is not a key this version knows")),
                },
            }
            seen.insert(key.to_string());
        }
        for required in ["binary.path", "binary.size", "binary.hash"] {
            if !seen.contains(required) {
                return Err(Error::inconsistent(format!(
                    "project is missing {required}, so it cannot say what binary it is for"
                )));
            }
        }
        Ok(p)
    }
}

fn malformed(n: usize, line: &str, why: &str) -> Error {
    Error::inconsistent(format!("project line {} {why}: {line:?}", n + 2))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn project() -> Project {
        let mut p = Project::for_binary("/srv/bin/target.elf", b"the binary's bytes");
        p.load.base = Some(Addr(0x40_0000));
        p.load.arch = Some(Arch::X86_64);
        p.load.readers.insert("eh_frame".into());
        p.load.readers.insert("dwarf".into());
        p.analysis.insert("sweep".into(), "recursive".into());
        p.analysis.insert("follow-tail-calls".into(), "true".into());
        p.log = Some("target.e5r".into());
        p.signatures = vec!["libc.sig".into(), "openssl.sig".into()];
        p.patches = vec!["nop-check.e5r-patch".into()];
        p
    }

    #[test]
    fn the_text_form_round_trips() {
        let p = project();
        let text = p.to_text();
        let back = Project::from_text(&text).unwrap();
        assert_eq!(back, p);
        assert_eq!(back.to_text(), text);
    }

    #[test]
    fn lists_keep_their_order_and_keys_sort() {
        let text = project().to_text();
        let keys: Vec<&str> = text
            .lines()
            .filter(|l| l.contains(" = "))
            .map(|l| l.split_once(" = ").unwrap().0)
            .collect();
        let mut sorted = keys.clone();
        sorted.sort_unstable();
        assert_eq!(keys, sorted);
        let sigs: Vec<&str> = text
            .lines()
            .filter_map(|l| l.strip_prefix("signatures = "))
            .collect();
        assert_eq!(sigs, ["libc.sig", "openssl.sig"]);
    }

    #[test]
    fn verify_tells_the_three_cases_apart() {
        let p = project();
        assert_eq!(p.verify(b"the binary's bytes"), Verdict::Same);
        assert!(matches!(
            p.verify_at("/tmp/copy.elf", b"the binary's bytes"),
            Verdict::Moved { .. }
        ));
        let rebuilt = p.verify(b"the binary's byteS");
        assert!(matches!(rebuilt, Verdict::Different { .. }), "{rebuilt}");
        assert!(!rebuilt.is_usable());
        assert!(
            p.verify_at("/tmp/copy.elf", b"the binary's bytes")
                .is_usable()
        );
    }

    #[test]
    fn a_same_length_edit_is_still_a_different_binary() {
        // Size alone is what a cheap check would use, so it must not be all
        // that is checked.
        let p = Project::for_binary("a", b"aaaabbbb");
        assert!(matches!(p.verify(b"aaaabbbc"), Verdict::Different { .. }));
    }

    #[test]
    fn a_truncated_or_corrupt_file_is_an_error() {
        assert!(Project::from_text("").is_err());
        assert!(Project::from_text("not a project\n").is_err());
        assert!(Project::from_text(&format!("{TAG} 99\n")).is_err());
        // Truncated before the binary is named.
        let text = project().to_text();
        let head: Vec<&str> = text.lines().take(4).collect();
        assert!(Project::from_text(&head.join("\n")).is_err());
        // A field that is no longer a number.
        let broken = text.replace("binary.size = 18", "binary.size = eighteen");
        let e = Project::from_text(&broken).unwrap_err().to_string();
        assert!(e.contains("number"), "{e}");
        // A key from a future version, which would otherwise be dropped.
        assert!(Project::from_text(&format!("{text}load.wombat = 1\n")).is_err());
    }

    #[test]
    fn a_sleigh_language_survives_the_round_trip() {
        let mut p = Project::for_binary("a", b"a");
        p.load.arch = Some(Arch::Sleigh("MIPS:BE:32:default".into()));
        let back = Project::from_text(&p.to_text()).unwrap();
        assert_eq!(back.load.arch, p.load.arch);
    }

    #[test]
    fn the_digest_is_platform_fixed() {
        // A literal, so a change in the fold is a test failure rather than a
        // silent invalidation of every project file in existence.
        assert_eq!(digest(b"e5r"), 0x9ff5_21d2_3f42_96c2);
    }
}
