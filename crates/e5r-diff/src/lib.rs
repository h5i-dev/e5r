//! Matching functions across two builds.
//!
//! The use case that has to work is patch diffing: given a vulnerable build and
//! a fixed one, say which function changed. That means the answer has to be
//! *ranked*, not just listed, because a compiler moves every function and a
//! report that says ten thousand things changed is a report nobody reads.
//!
//! Matching runs in passes, strongest evidence first, and each pass only
//! considers what earlier passes left over:
//!
//! 1. Exact body hash. The same bytes are the same function, whatever moved.
//! 2. Instruction-shape hash, which ignores branch targets and so survives
//!    relocation. A unique shape on both sides is a confident match.
//! 3. Name, for the functions a symbol table names.
//! 4. Call-graph neighbourhood: an unmatched function whose callers and callees
//!    are already matched, uniquely, to a function whose callers and callees
//!    are the same.
//!
//! Anything still unmatched is an addition or a removal, which is itself a
//! finding.
//!
//! [`align`] takes it one level down: inside a matched pair, which
//! instruction changed.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod align;

pub use align::{Edit, EditKind, FunctionDiff, compare_function, detail, mapping};

use std::collections::{BTreeMap, BTreeSet, HashMap};

use e5r_analysis::{Function, Program};
use e5r_core::Addr;
use e5r_db::Anchor;
use serde::Serialize;

/// How a pair of functions was matched.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum MatchKind {
    /// The same bytes.
    Identical,
    /// The same instruction shape, so the same code at a different address.
    Shape,
    /// The same name.
    Name,
    /// The same position in the call graph.
    CallGraph,
}

impl MatchKind {
    /// The word shown in output.
    pub fn as_str(self) -> &'static str {
        match self {
            MatchKind::Identical => "identical",
            MatchKind::Shape => "shape",
            MatchKind::Name => "name",
            MatchKind::CallGraph => "call graph",
        }
    }
}

/// One matched pair.
#[derive(Debug, Clone, Serialize)]
pub struct Match {
    /// Where it is in the old build.
    pub old: Addr,
    /// Where it is in the new build.
    pub new: Addr,
    /// The name to show, from whichever side has one.
    pub name: String,
    /// How the pair was found.
    pub kind: MatchKind,
    /// How alike the two are, from 0 to 1. Exactly 1 means byte-identical.
    pub similarity: f64,
    /// Instructions on each side, for the report.
    pub old_insns: u32,
    /// Instructions in the new build.
    pub new_insns: u32,
}

impl Match {
    /// True when the two sides differ at all.
    pub fn changed(&self) -> bool {
        self.similarity < 1.0
    }
}

/// The result of comparing two builds.
#[derive(Debug, Clone, Default, Serialize)]
pub struct Diff {
    /// Pairs, changed ones first and most changed at the top.
    pub matched: Vec<Match>,
    /// Functions only the old build has.
    pub removed: Vec<(Addr, String)>,
    /// Functions only the new build has.
    pub added: Vec<(Addr, String)>,
}

impl Diff {
    /// How many pairs differ.
    pub fn changed_count(&self) -> usize {
        self.matched.iter().filter(|m| m.changed()).count()
    }

    /// How many pairs are byte-identical.
    pub fn identical_count(&self) -> usize {
        self.matched.iter().filter(|m| !m.changed()).count()
    }

    /// The changed pairs, most changed first. This is the answer to "what did
    /// the patch touch".
    pub fn changed(&self) -> impl Iterator<Item = &Match> {
        self.matched.iter().filter(|m| m.changed())
    }
}

/// One side's functions, indexed the ways matching needs.
struct Side<'a> {
    program: &'a Program,
    anchors: BTreeMap<Addr, Anchor>,
    /// Mnemonic multiset per function, for scoring.
    profiles: BTreeMap<Addr, BTreeMap<&'static str, u32>>,
    by_bytes: HashMap<u64, Vec<Addr>>,
    by_shape: HashMap<u64, Vec<Addr>>,
    by_name: HashMap<String, Vec<Addr>>,
    /// Who calls whom, and who is called by whom.
    callees: BTreeMap<Addr, BTreeSet<Addr>>,
    callers: BTreeMap<Addr, BTreeSet<Addr>>,
}

impl<'a> Side<'a> {
    fn build(program: &'a Program) -> Side<'a> {
        let mut anchors = BTreeMap::new();
        let mut profiles = BTreeMap::new();
        let mut by_bytes: HashMap<u64, Vec<Addr>> = HashMap::new();
        let mut by_shape: HashMap<u64, Vec<Addr>> = HashMap::new();
        let mut by_name: HashMap<String, Vec<Addr>> = HashMap::new();
        let mut callees: BTreeMap<Addr, BTreeSet<Addr>> = BTreeMap::new();
        let mut callers: BTreeMap<Addr, BTreeSet<Addr>> = BTreeMap::new();

        for f in program.functions_by_address() {
            let insns = program.instructions(f);
            let mut body = Vec::with_capacity(f.cfg.covered_bytes() as usize);
            for b in f.cfg.blocks.values() {
                if let Some(bytes) = program.object.memory.slice(b.range.start(), b.range.len()) {
                    body.extend_from_slice(bytes);
                }
            }
            let anchor = Anchor::function(f.entry, &insns, &body);
            by_bytes.entry(anchor.bytes).or_default().push(f.entry);
            by_shape.entry(anchor.shape).or_default().push(f.entry);
            if let Some(n) = f.raw_name() {
                by_name.entry(n.to_string()).or_default().push(f.entry);
            }
            anchors.insert(f.entry, anchor);

            let mut profile: BTreeMap<&'static str, u32> = BTreeMap::new();
            for i in &insns {
                *profile.entry(i.mnemonic).or_default() += 1;
            }
            profiles.insert(f.entry, profile);

            let out: BTreeSet<Addr> = f.cfg.calls.iter().copied().collect();
            for c in &out {
                callers.entry(*c).or_default().insert(f.entry);
            }
            callees.insert(f.entry, out);
        }

        Side {
            program,
            anchors,
            profiles,
            by_bytes,
            by_shape,
            by_name,
            callees,
            callers,
        }
    }

    fn name(&self, at: Addr) -> String {
        self.program
            .function(at)
            .map(|f| f.display_name())
            .unwrap_or_else(|| format!("sub_{:x}", at.get()))
    }

    fn insns(&self, at: Addr) -> u32 {
        self.program
            .function(at)
            .map(|f| f.cfg.insns())
            .unwrap_or(0)
    }
}

/// How alike two functions are, by their mnemonic multisets.
///
/// A multiset rather than a sequence: a compiler reorders blocks freely between
/// builds, and a sequence comparison would call every function changed. It does
/// mean a pure reordering scores 1.0 on this measure, which is why an exact
/// byte match is what sets similarity to 1 rather than this score.
fn similarity(a: &BTreeMap<&'static str, u32>, b: &BTreeMap<&'static str, u32>) -> f64 {
    if a.is_empty() && b.is_empty() {
        return 1.0;
    }
    let mut shared = 0u32;
    let mut total = 0u32;
    for (m, n) in a {
        let other = b.get(m).copied().unwrap_or(0);
        shared += (*n).min(other);
        total += (*n).max(other);
    }
    for (m, n) in b {
        if !a.contains_key(m) {
            total += *n;
        }
    }
    if total == 0 {
        return 1.0;
    }
    shared as f64 / total as f64
}

/// Compare two analyzed builds.
pub fn compare(old: &Program, new: &Program) -> Diff {
    let a = Side::build(old);
    let b = Side::build(new);

    let mut pairs: Vec<Match> = Vec::new();
    let mut used_old: BTreeSet<Addr> = BTreeSet::new();
    let mut used_new: BTreeSet<Addr> = BTreeSet::new();

    // Pass 1 and 2: unique hashes on both sides.
    for (kind, index_a, index_b) in [
        (MatchKind::Identical, &a.by_bytes, &b.by_bytes),
        (MatchKind::Shape, &a.by_shape, &b.by_shape),
    ] {
        for (key, olds) in index_a {
            let Some(news) = index_b.get(key) else {
                continue;
            };
            // Only a one-to-one hash is evidence; several functions sharing a
            // hash means the hash did not identify anything.
            let olds: Vec<Addr> = olds
                .iter()
                .copied()
                .filter(|x| !used_old.contains(x))
                .collect();
            let news: Vec<Addr> = news
                .iter()
                .copied()
                .filter(|x| !used_new.contains(x))
                .collect();
            if olds.len() != 1 || news.len() != 1 {
                continue;
            }
            record(
                &a,
                &b,
                olds[0],
                news[0],
                kind,
                &mut pairs,
                &mut used_old,
                &mut used_new,
            );
        }
    }

    // Pass 3: names.
    for (name, olds) in &a.by_name {
        let Some(news) = b.by_name.get(name) else {
            continue;
        };
        let olds: Vec<Addr> = olds
            .iter()
            .copied()
            .filter(|x| !used_old.contains(x))
            .collect();
        let news: Vec<Addr> = news
            .iter()
            .copied()
            .filter(|x| !used_new.contains(x))
            .collect();
        if olds.len() != 1 || news.len() != 1 {
            continue;
        }
        record(
            &a,
            &b,
            olds[0],
            news[0],
            MatchKind::Name,
            &mut pairs,
            &mut used_old,
            &mut used_new,
        );
    }

    // Pass 4: call-graph position. Repeated, because each match makes more
    // neighbourhoods decidable.
    for _ in 0..4 {
        let mapping: BTreeMap<Addr, Addr> = pairs.iter().map(|m| (m.old, m.new)).collect();
        let mut found = Vec::new();
        for f in a.program.functions_by_address() {
            if used_old.contains(&f.entry) {
                continue;
            }
            let Some(candidate) = neighbourhood_match(&a, &b, f, &mapping, &used_new) else {
                continue;
            };
            found.push((f.entry, candidate));
        }
        if found.is_empty() {
            break;
        }
        for (o, n) in found {
            if used_old.contains(&o) || used_new.contains(&n) {
                continue;
            }
            record(
                &a,
                &b,
                o,
                n,
                MatchKind::CallGraph,
                &mut pairs,
                &mut used_old,
                &mut used_new,
            );
        }
    }

    // Most changed first: that is the order a patch diff is read in.
    pairs.sort_by(|x, y| {
        x.similarity
            .partial_cmp(&y.similarity)
            .unwrap_or(std::cmp::Ordering::Equal)
            .then(x.old.cmp(&y.old))
    });

    let removed = a
        .program
        .functions_by_address()
        .filter(|f| !used_old.contains(&f.entry))
        .map(|f| (f.entry, f.display_name()))
        .collect();
    let added = b
        .program
        .functions_by_address()
        .filter(|f| !used_new.contains(&f.entry))
        .map(|f| (f.entry, f.display_name()))
        .collect();

    Diff {
        matched: pairs,
        removed,
        added,
    }
}

#[allow(clippy::too_many_arguments)]
fn record(
    a: &Side<'_>,
    b: &Side<'_>,
    old: Addr,
    new: Addr,
    kind: MatchKind,
    pairs: &mut Vec<Match>,
    used_old: &mut BTreeSet<Addr>,
    used_new: &mut BTreeSet<Addr>,
) {
    let identical = a.anchors.get(&old).map(|x| x.bytes) == b.anchors.get(&new).map(|x| x.bytes);
    let score = if identical {
        1.0
    } else {
        // Never report a non-identical pair as a perfect match: the multiset
        // score cannot see a reordering, and claiming no change when the bytes
        // differ is exactly the mistake a patch diff must not make.
        similarity(&a.profiles[&old], &b.profiles[&new]).min(0.999)
    };
    used_old.insert(old);
    used_new.insert(new);
    pairs.push(Match {
        old,
        new,
        name: {
            let n = a.name(old);
            if n.starts_with("sub_") {
                b.name(new)
            } else {
                n
            }
        },
        kind,
        similarity: score,
        old_insns: a.insns(old),
        new_insns: b.insns(new),
    });
}

/// The one new-build function whose neighbours are the images of this one's.
fn neighbourhood_match(
    a: &Side<'_>,
    b: &Side<'_>,
    f: &Function,
    mapping: &BTreeMap<Addr, Addr>,
    used_new: &BTreeSet<Addr>,
) -> Option<Addr> {
    // Project the known callers and callees into the new build.
    let want_callees: BTreeSet<Addr> = a
        .callees
        .get(&f.entry)?
        .iter()
        .filter_map(|c| mapping.get(c).copied())
        .collect();
    let want_callers: BTreeSet<Addr> = a
        .callers
        .get(&f.entry)
        .into_iter()
        .flatten()
        .filter_map(|c| mapping.get(c).copied())
        .collect();
    // Too little context to be evidence of anything.
    if want_callees.len() + want_callers.len() < 2 {
        return None;
    }

    // A candidate is any unmatched function called by one of the projected
    // callers, or calling one of the projected callees.
    let mut candidates: BTreeSet<Addr> = BTreeSet::new();
    for caller in &want_callers {
        if let Some(cs) = b.callees.get(caller) {
            candidates.extend(cs.iter().filter(|x| !used_new.contains(x)));
        }
    }
    for callee in &want_callees {
        if let Some(cs) = b.callers.get(callee) {
            candidates.extend(cs.iter().filter(|x| !used_new.contains(x)));
        }
    }

    let mut best: Option<(Addr, usize)> = None;
    let mut tied = false;
    for c in candidates {
        let has_callees = b.callees.get(&c).cloned().unwrap_or_default();
        let has_callers = b.callers.get(&c).cloned().unwrap_or_default();
        let score = want_callees.intersection(&has_callees).count()
            + want_callers.intersection(&has_callers).count();
        if score < 2 {
            continue;
        }
        match best {
            Some((_, s)) if s > score => {}
            Some((_, s)) if s == score => tied = true,
            _ => {
                best = Some((c, score));
                tied = false;
            }
        }
    }
    // A tie is not evidence.
    if tied { None } else { best.map(|(c, _)| c) }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn profile(pairs: &[(&'static str, u32)]) -> BTreeMap<&'static str, u32> {
        pairs.iter().copied().collect()
    }

    #[test]
    fn identical_profiles_score_one() {
        let p = profile(&[("mov", 3), ("add", 1)]);
        assert_eq!(similarity(&p, &p), 1.0);
    }

    #[test]
    fn disjoint_profiles_score_zero() {
        let a = profile(&[("mov", 3)]);
        let b = profile(&[("add", 3)]);
        assert_eq!(similarity(&a, &b), 0.0);
    }

    #[test]
    fn one_extra_instruction_scores_close_to_one() {
        let a = profile(&[("mov", 10), ("add", 10)]);
        let b = profile(&[("mov", 10), ("add", 10), ("cmp", 1)]);
        let s = similarity(&a, &b);
        assert!(s > 0.9 && s < 1.0, "{s}");
    }

    #[test]
    fn the_empty_case_is_not_a_division_by_zero() {
        let empty = BTreeMap::new();
        assert_eq!(similarity(&empty, &empty), 1.0);
        assert_eq!(similarity(&profile(&[("mov", 1)]), &empty), 0.0);
    }
}
