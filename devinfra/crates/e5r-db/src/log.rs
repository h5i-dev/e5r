//! The annotation log: an append-only list of assertions that git can merge.
//!
//! Each assertion is one line. The current state is a fold over the log, and
//! the fold depends only on each record's `(seq, id)`, never on where the line
//! sits in the file. Two analysts on separate branches therefore merge with
//! `git merge` alone: their assertions are distinct lines and the union folds
//! to a well-defined state whichever landed first.
//!
//! Lines are written sorted by content id rather than appended. Appending puts
//! every new line at the end of the file, which is exactly where git's
//! line-based merge conflicts; scattering them by a content hash spreads two
//! branches' additions across the file instead.
//!
//! Scattering is not enough on its own: two insertions into the same gap still
//! collide. The file is therefore declared `merge=union` in `.gitattributes`,
//! git's built-in driver that keeps both sides of a conflicting hunk. For an
//! append-only log whose fold ignores order, the union of both sides *is* the
//! correct merge, and duplicate lines are dropped on read. The header names
//! the rule so anyone who opens the file knows it needs to be there.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use e5r_core::{Addr, Error, Result};
use e5r_types::cdecl;
use e5r_types::ctype::{Signature, TypeId, Types};

use crate::anchor::{Anchor, AnchorIndex, Fnv, Resolution};

/// Magic on the first line.
const TAG: &str = "e5r-annotations";
/// On-disk format version. A reader refuses a version it does not know rather
/// than guessing at a layout.
const VERSION: u32 = 1;

/// Which single-valued attribute of a location an assertion sets.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Field {
    /// The name.
    Name,
    /// The type or prototype, as source text.
    Type,
    /// A free comment.
    Comment,
}

impl Field {
    /// The on-disk keyword.
    pub fn as_str(self) -> &'static str {
        match self {
            Field::Name => "name",
            Field::Type => "type",
            Field::Comment => "comment",
        }
    }

    fn tag(self) -> u8 {
        match self {
            Field::Name => 0,
            Field::Type => 1,
            Field::Comment => 2,
        }
    }

    /// Parse an on-disk keyword.
    pub fn parse(s: &str) -> Option<Field> {
        Some(match s {
            "name" => Field::Name,
            "type" => Field::Type,
            "comment" => Field::Comment,
            _ => return None,
        })
    }

    /// Check a value before it is written.
    ///
    /// The log stores a type as the source text a person typed, and this is
    /// the reason that is safe rather than sloppy. Two properties have to hold
    /// together and they pull in opposite directions:
    ///
    /// * **Reviewable.** The file is read in a pull request. A serialized type
    ///   graph is not something anybody reviews, and a parser that improves
    ///   would have to rewrite history to keep up with itself. Text does not.
    /// * **Not write-only.** A typed declaration that is never parsed is a
    ///   comment. Until this existed, `annotate type` wrote a line nothing
    ///   read, which is the failure this whole path exists to fix.
    ///
    /// So: parse on read, and validate on write. A typo is rejected at the
    /// moment it is typed, which is the only moment the person who made it is
    /// still there to fix it. Reading deliberately does not validate: a log
    /// written by a newer build must still fold, and refusing a whole file
    /// because one type no longer parses would throw away the names and
    /// comments beside it.
    pub fn validate(self, value: &str) -> std::result::Result<(), String> {
        match self {
            Field::Comment => Ok(()),
            Field::Name => {
                if value.trim().is_empty() {
                    return Err("a name cannot be blank; clear it instead".into());
                }
                // A demangled C++ name is full of spaces and punctuation, so
                // the only thing refused is what would not survive a listing.
                match value.chars().find(|c| c.is_control()) {
                    Some(c) => Err(format!("a name cannot contain {c:?}")),
                    None => Ok(()),
                }
            }
            Field::Type => {
                let mut types = Types::new();
                declared(&mut types, value)
                    .map(|_| ())
                    .map_err(|e| e.to_string())
            }
        }
    }
}

/// What a `type` assertion says, once it has been parsed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Declared {
    /// A function declaration: a prototype to lay over what recovery found.
    Function {
        /// The name the declaration gave, when it gave one.
        name: Option<String>,
        /// What it takes and returns.
        signature: Signature,
        /// The function type itself.
        ty: TypeId,
    },
    /// A type for a data object, or a bare type name.
    Object {
        /// The name the declaration gave, when it gave one.
        name: Option<String>,
        /// The type.
        ty: TypeId,
    },
}

impl Declared {
    /// The type, whichever kind it is.
    pub fn ty(&self) -> TypeId {
        match self {
            Declared::Function { ty, .. } | Declared::Object { ty, .. } => *ty,
        }
    }

    /// The name the declaration gave, when it gave one.
    pub fn name(&self) -> Option<&str> {
        match self {
            Declared::Function { name, .. } | Declared::Object { name, .. } => name.as_deref(),
        }
    }
}

/// Read a `type` assertion back into the type model.
///
/// Accepts both of the things an analyst writes: a declaration with a name,
/// which is what a prototype is, and a bare type name, which is what a data
/// object gets. Anything else comes back as an error naming what was not
/// understood, because a type the reader will believe and that is wrong is
/// worse than no type at all.
pub fn declared(
    types: &mut Types,
    value: &str,
) -> std::result::Result<Declared, cdecl::ParseError> {
    match cdecl::declaration(types, value) {
        Ok(d) => {
            let resolved = types.resolve(d.ty);
            match types.get(resolved) {
                Some(e5r_types::ctype::Type::Function(sig)) => Ok(Declared::Function {
                    name: d.name,
                    signature: sig.clone(),
                    ty: d.ty,
                }),
                _ => Ok(Declared::Object {
                    name: d.name,
                    ty: d.ty,
                }),
            }
        }
        // A bare type name declares nothing, which the declaration grammar
        // refuses and an annotation on a data object is written as.
        Err(first) => match cdecl::type_name(types, value) {
            Ok(ty) => Ok(Declared::Object { name: None, ty }),
            Err(second) => Err(if second.offset > first.offset {
                second
            } else {
                first
            }),
        },
    }
}

impl std::fmt::Display for Field {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// One assertion: a single edit to one field of one location.
///
/// Immutable once made. A later assertion to the same `(target, field)`
/// supersedes it under the fold; a `value` of `None` is a tombstone that
/// clears the field.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Assertion {
    /// Where it applies.
    pub target: Anchor,
    /// Which attribute it sets.
    pub field: Field,
    /// What it sets, or `None` to clear.
    pub value: Option<String>,
    /// Assignment order: the last-writer-wins clock.
    pub seq: u64,
    /// Content id, the tiebreak when two branches share a `seq` and the sort
    /// key that scatters new lines through the file.
    pub id: u64,
    /// Who wrote it.
    pub who: String,
}

impl Assertion {
    /// Derive the content id from every other field.
    fn content_id(target: &Anchor, field: Field, value: Option<&str>, seq: u64, who: &str) -> u64 {
        let mut h = Fnv::new();
        let (shape, bytes, insns, offset) = target.identity();
        h.u64(shape);
        h.u64(bytes);
        h.u64(insns as u64);
        h.u64(offset as u64);
        h.u64(target.abs.get());
        // Domain separators, so a name and a comment with the same text cannot
        // collide.
        h.byte(0xff);
        h.byte(field.tag());
        h.u64(seq);
        h.byte(0xfe);
        h.slice(who.as_bytes());
        h.byte(0xfd);
        match value {
            Some(v) => {
                h.byte(1);
                h.slice(v.as_bytes());
            }
            None => h.byte(0),
        }
        h.finish()
    }

    /// The key a fold groups by.
    fn key(&self) -> (u64, u64, u32, u32, Field) {
        let (shape, bytes, insns, offset) = self.target.identity();
        (shape, bytes, insns, offset, self.field)
    }
}

/// Everything an analyst has written about one binary.
#[derive(Debug, Clone, Default)]
pub struct Log {
    /// Sorted by `id`, which is the on-disk order.
    records: Vec<Assertion>,
    /// Next sequence number to hand out.
    next_seq: u64,
    /// Undone assertions, newest last. Cleared by any fresh assertion, which
    /// is the editor model everyone already knows.
    redo: Vec<Assertion>,
    /// The binary this log is about, as a hex digest, when known.
    pub binary: Option<String>,
}

impl Log {
    /// An empty log.
    pub fn new() -> Log {
        Log::default()
    }

    /// How many assertions it holds.
    pub fn len(&self) -> usize {
        self.records.len()
    }

    /// True when nothing has been written.
    pub fn is_empty(&self) -> bool {
        self.records.is_empty()
    }

    /// Every assertion, in file order.
    pub fn records(&self) -> &[Assertion] {
        &self.records
    }

    /// Record an assertion. `None` clears the field.
    pub fn assert(
        &mut self,
        target: Anchor,
        field: Field,
        value: Option<String>,
        who: &str,
    ) -> &Assertion {
        let seq = self.next_seq;
        self.next_seq += 1;
        let id = Assertion::content_id(&target, field, value.as_deref(), seq, who);
        let a = Assertion {
            target,
            field,
            value,
            seq,
            id,
            who: who.to_string(),
        };
        self.redo.clear();
        let at = self
            .records
            .partition_point(|r| (r.id, r.seq) < (a.id, a.seq));
        self.records.insert(at, a);
        &self.records[at]
    }

    /// Record an assertion, refusing a value the field cannot hold.
    ///
    /// The checked form of [`Log::assert`], and the one every command that
    /// takes a value from a person should use. See [`Field::validate`] for why
    /// writing checks and reading does not.
    pub fn assert_checked(
        &mut self,
        target: Anchor,
        field: Field,
        value: Option<String>,
        who: &str,
    ) -> Result<&Assertion> {
        if let Some(v) = &value {
            field.validate(v).map_err(|detail| Error::Inconsistent {
                detail: format!("{field} assertion is not valid: {detail}"),
            })?;
        }
        Ok(self.assert(target, field, value, who))
    }

    /// Undo the most recent assertion, returning it.
    pub fn undo(&mut self) -> Option<Assertion> {
        let at = self
            .records
            .iter()
            .enumerate()
            .max_by_key(|(_, r)| (r.seq, r.id))
            .map(|(i, _)| i)?;
        let a = self.records.remove(at);
        self.redo.push(a.clone());
        Some(a)
    }

    /// Put back the most recently undone assertion.
    pub fn redo(&mut self) -> Option<Assertion> {
        let a = self.redo.pop()?;
        let at = self
            .records
            .partition_point(|r| (r.id, r.seq) < (a.id, a.seq));
        self.records.insert(at, a.clone());
        Some(a)
    }

    /// The current state: the winning assertion for every `(location, field)`.
    ///
    /// Order-independent by construction, which is what lets two branches merge
    /// by concatenating lines.
    pub fn fold(&self) -> BTreeMap<(u64, u64, u32, u32, Field), &Assertion> {
        let mut out: BTreeMap<(u64, u64, u32, u32, Field), &Assertion> = BTreeMap::new();
        for r in &self.records {
            match out.get(&r.key()) {
                // Last writer wins; a shared seq breaks on the content id, so
                // two branches that both wrote at seq 7 still agree.
                Some(prev) if (prev.seq, prev.id) >= (r.seq, r.id) => {}
                _ => {
                    out.insert(r.key(), r);
                }
            }
        }
        out.retain(|_, r| r.value.is_some());
        out
    }

    /// Resolve the folded state against a freshly analyzed binary.
    ///
    /// Returns one entry per assertion that still points somewhere, with the
    /// address it landed on and how sure the match is.
    pub fn apply(&self, index: &AnchorIndex) -> Vec<Applied> {
        let mut out = Vec::new();
        for r in self.fold().values() {
            if let Some((found, how)) = index.resolve(&r.target) {
                out.push(Applied {
                    addr: found.target().wrapping_offset(r.target.offset as i64),
                    field: r.field,
                    value: r.value.clone().unwrap_or_default(),
                    resolution: how,
                    who: r.who.clone(),
                });
            }
        }
        out.sort_by_key(|a| (a.addr, a.field));
        out
    }

    /// Merge another log into this one. Used to fold in a file that changed
    /// under us; the result does not depend on which side is `other`.
    pub fn merge(&mut self, other: &Log) {
        for r in &other.records {
            if self.records.iter().any(|e| e.id == r.id && e.seq == r.seq) {
                continue;
            }
            let at = self
                .records
                .partition_point(|e| (e.id, e.seq) < (r.id, r.seq));
            self.records.insert(at, r.clone());
        }
        self.next_seq = self
            .records
            .iter()
            .map(|r| r.seq + 1)
            .max()
            .unwrap_or(0)
            .max(self.next_seq);
    }

    /// Serialize, sorted by content id so new lines scatter through the file.
    pub fn to_text(&self) -> String {
        let mut s = String::with_capacity(128 + self.records.len() * 96);
        let _ = writeln!(s, "{TAG} {VERSION}");
        if let Some(b) = &self.binary {
            let _ = writeln!(s, "binary {b}");
        }
        let _ = writeln!(
            s,
            "# One assertion per line, sorted by content id. Order does not affect the"
        );
        let _ = writeln!(
            s,
            "# result, so the union of two branches is the correct merge. Put this in"
        );
        let _ = writeln!(s, "# .gitattributes so git does that for you:");
        let _ = writeln!(s, "#     *.e5r merge=union");
        let _ = writeln!(s, "# Do not sort or reflow by hand.");
        for r in &self.records {
            let _ = writeln!(
                s,
                "{} shape={:016x} bytes={:016x} insns={} abs={:x} off={} seq={} id={:016x} by={} value={}",
                r.field,
                r.target.shape,
                r.target.bytes,
                r.target.insns,
                r.target.abs.get(),
                r.target.offset,
                r.seq,
                r.id,
                escape(&r.who),
                match &r.value {
                    Some(v) => escape(v),
                    None => "-".to_string(),
                }
            );
        }
        s
    }

    /// Parse a serialized log.
    pub fn from_text(text: &str) -> Result<Log> {
        let mut lines = text.lines();
        let header = lines.next().unwrap_or_default();
        let mut parts = header.split_whitespace();
        if parts.next() != Some(TAG) {
            return Err(Error::NotRecognized {
                expected: "e5r annotation log",
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
                "annotation format version {version}; this build knows {VERSION}"
            )));
        }

        let mut log = Log::new();
        for (n, line) in lines.enumerate() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            if let Some(rest) = line.strip_prefix("binary ") {
                log.binary = Some(rest.trim().to_string());
                continue;
            }
            match parse_record(line) {
                Some(r) => log.records.push(r),
                None => {
                    return Err(Error::inconsistent(format!(
                        "annotation line {} is malformed: {line:?}",
                        n + 2
                    )));
                }
            }
        }
        log.records.sort_by_key(|r| (r.id, r.seq));
        log.records.dedup_by_key(|r| (r.id, r.seq));
        log.next_seq = log.records.iter().map(|r| r.seq + 1).max().unwrap_or(0);
        Ok(log)
    }
}

/// One folded assertion placed on a freshly analyzed binary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Applied {
    /// Where it landed.
    pub addr: Addr,
    /// Which field it sets.
    pub field: Field,
    /// The value.
    pub value: String,
    /// How confident the match is.
    pub resolution: Resolution,
    /// Who wrote it.
    pub who: String,
}

/// Quote a value so it survives a round trip through a whitespace-split line.
fn escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn unescape(s: &str) -> Option<String> {
    let body = s.strip_prefix('"')?.strip_suffix('"')?;
    let mut out = String::with_capacity(body.len());
    let mut chars = body.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next()? {
            'n' => out.push('\n'),
            't' => out.push('\t'),
            '"' => out.push('"'),
            '\\' => out.push('\\'),
            other => out.push(other),
        }
    }
    Some(out)
}

fn parse_record(line: &str) -> Option<Assertion> {
    let (field_word, rest) = line.split_once(' ')?;
    let field = Field::parse(field_word)?;

    let mut shape = None;
    let mut bytes = None;
    let mut insns = None;
    let mut abs = None;
    let mut offset = 0u32;
    let mut seq = None;
    let mut id = None;
    let mut who = String::new();
    let mut value: Option<Option<String>> = None;

    // `value=` and `by=` are quoted and may hold spaces, so they are taken
    // whole rather than split on whitespace.
    let mut cursor = rest;
    while !cursor.is_empty() {
        let cursor_trim = cursor.trim_start();
        if cursor_trim.is_empty() {
            break;
        }
        let (key, after) = cursor_trim.split_once('=')?;
        if after.starts_with('"') {
            let end = find_quote_end(after)?;
            let (quoted, tail) = after.split_at(end + 1);
            let v = unescape(quoted)?;
            match key {
                "by" => who = v,
                "value" => value = Some(Some(v)),
                _ => return None,
            }
            cursor = tail;
            continue;
        }
        let (v, tail) = match after.find(' ') {
            Some(i) => after.split_at(i),
            None => (after, ""),
        };
        match key {
            "shape" => shape = u64::from_str_radix(v, 16).ok(),
            "bytes" => bytes = u64::from_str_radix(v, 16).ok(),
            "insns" => insns = v.parse().ok(),
            "abs" => abs = u64::from_str_radix(v, 16).ok(),
            "off" => offset = v.parse().ok()?,
            "seq" => seq = v.parse().ok(),
            "id" => id = u64::from_str_radix(v, 16).ok(),
            "value" if v == "-" => value = Some(None),
            _ => return None,
        }
        cursor = tail;
    }

    Some(Assertion {
        target: Anchor {
            shape: shape?,
            bytes: bytes?,
            insns: insns?,
            abs: Addr(abs?),
            offset,
        },
        field,
        value: value?,
        seq: seq?,
        id: id?,
        who,
    })
}

/// Index of the closing quote of a quoted value starting at index 0.
fn find_quote_end(s: &str) -> Option<usize> {
    let b = s.as_bytes();
    let mut i = 1;
    while i < b.len() {
        match b[i] {
            b'\\' => i += 2,
            b'"' => return Some(i),
            _ => i += 1,
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn anchor(shape: u64, bytes: u64) -> Anchor {
        Anchor {
            shape,
            bytes,
            insns: 4,
            abs: Addr(0x1000),
            offset: 0,
        }
    }

    #[test]
    fn the_last_writer_wins() {
        let mut log = Log::new();
        let a = anchor(1, 2);
        log.assert(a, Field::Name, Some("first".into()), "alice");
        log.assert(a, Field::Name, Some("second".into()), "alice");
        let folded = log.fold();
        assert_eq!(folded.len(), 1);
        assert_eq!(
            folded.values().next().unwrap().value.as_deref(),
            Some("second")
        );
    }

    #[test]
    fn a_tombstone_clears_the_field() {
        let mut log = Log::new();
        let a = anchor(1, 2);
        log.assert(a, Field::Comment, Some("note".into()), "alice");
        log.assert(a, Field::Comment, None, "alice");
        assert!(log.fold().is_empty());
        // The tombstone is still a record; clearing is not forgetting.
        assert_eq!(log.len(), 2);
    }

    #[test]
    fn fields_are_independent() {
        let mut log = Log::new();
        let a = anchor(1, 2);
        log.assert(a, Field::Name, Some("f".into()), "alice");
        log.assert(a, Field::Comment, Some("c".into()), "alice");
        log.assert(a, Field::Type, Some("int f(void)".into()), "alice");
        assert_eq!(log.fold().len(), 3);
    }

    #[test]
    fn round_trips_through_text() {
        let mut log = Log::new();
        log.binary = Some("sha256:abcd".into());
        log.assert(
            anchor(1, 2),
            Field::Name,
            Some("parse_header".into()),
            "alice",
        );
        log.assert(
            anchor(3, 4),
            Field::Comment,
            Some("handles the \"quoted\" case\nand a newline".into()),
            "bob",
        );
        log.assert(anchor(5, 6), Field::Name, None, "carol");
        let text = log.to_text();
        let back = Log::from_text(&text).unwrap();
        assert_eq!(back.records, log.records);
        assert_eq!(back.binary, log.binary);
        assert_eq!(back.to_text(), text);
    }

    #[test]
    fn two_branches_merge_to_the_same_state_either_way() {
        // The property the whole design exists for.
        let mut base = Log::new();
        base.assert(anchor(1, 2), Field::Name, Some("shared".into()), "alice");

        let mut left = base.clone();
        left.assert(anchor(3, 4), Field::Name, Some("from_left".into()), "alice");
        let mut right = base.clone();
        right.assert(anchor(5, 6), Field::Name, Some("from_right".into()), "bob");

        let mut a = left.clone();
        a.merge(&right);
        let mut b = right.clone();
        b.merge(&left);
        assert_eq!(a.to_text(), b.to_text());
        assert_eq!(a.fold().len(), 3);
    }

    #[test]
    fn concatenating_two_files_is_a_valid_merge() {
        // What git actually does to non-overlapping line insertions.
        let mut left = Log::new();
        left.assert(anchor(3, 4), Field::Name, Some("left".into()), "alice");
        let mut right = Log::new();
        right.assert(anchor(5, 6), Field::Name, Some("right".into()), "bob");

        let lt = left.to_text();
        let rt = right.to_text();
        let lines: Vec<&str> = lt
            .lines()
            .chain(rt.lines().filter(|l| !l.starts_with(TAG)))
            .collect();
        let merged = Log::from_text(&lines.join("\n")).unwrap();
        assert_eq!(merged.fold().len(), 2);
    }

    #[test]
    fn a_shared_sequence_number_breaks_on_content() {
        // Two branches both writing their first assertion get seq 0. The fold
        // must still pick one, and pick the same one on both machines.
        let a = anchor(1, 2);
        let mut left = Log::new();
        left.assert(a, Field::Name, Some("left".into()), "alice");
        let mut right = Log::new();
        right.assert(a, Field::Name, Some("right".into()), "bob");

        let mut m1 = left.clone();
        m1.merge(&right);
        let mut m2 = right.clone();
        m2.merge(&left);
        let v1 = m1.fold().values().next().unwrap().value.clone();
        let v2 = m2.fold().values().next().unwrap().value.clone();
        assert_eq!(v1, v2);
    }

    #[test]
    fn undo_and_redo_walk_the_log() {
        let mut log = Log::new();
        let a = anchor(1, 2);
        log.assert(a, Field::Name, Some("one".into()), "alice");
        log.assert(a, Field::Name, Some("two".into()), "alice");
        assert_eq!(log.undo().unwrap().value.as_deref(), Some("two"));
        assert_eq!(
            log.fold().values().next().unwrap().value.as_deref(),
            Some("one")
        );
        assert_eq!(log.redo().unwrap().value.as_deref(), Some("two"));
        assert_eq!(
            log.fold().values().next().unwrap().value.as_deref(),
            Some("two")
        );
        // A fresh assertion drops the redo stack, as an editor does.
        log.undo();
        log.assert(a, Field::Name, Some("three".into()), "alice");
        assert!(log.redo().is_none());
    }

    #[test]
    fn a_newer_format_version_is_refused_rather_than_guessed_at() {
        let text = format!("{TAG} 99\n");
        assert!(Log::from_text(&text).is_err());
        assert!(Log::from_text("not an annotation file\n").is_err());
    }

    #[test]
    fn a_malformed_line_names_itself() {
        let text = format!("{TAG} 1\nname shape=zz\n");
        let e = Log::from_text(&text).unwrap_err().to_string();
        assert!(e.contains("line 2"), "{e}");
    }

    #[test]
    fn on_disk_order_is_by_content_so_appends_scatter() {
        // The property that keeps git from conflicting: consecutive writes do
        // not land next to each other in the file.
        let mut log = Log::new();
        for i in 0..64u64 {
            log.assert(
                anchor(i, i * 7),
                Field::Name,
                Some(format!("f{i}")),
                "alice",
            );
        }
        let ids: Vec<u64> = log.records().iter().map(|r| r.id).collect();
        let mut sorted = ids.clone();
        sorted.sort_unstable();
        assert_eq!(ids, sorted);
        // The last assertion made is not the last line.
        let last_seq_pos = log.records().iter().position(|r| r.seq == 63).unwrap();
        assert!(last_seq_pos < 63, "newest assertion landed at the end");
    }
}
