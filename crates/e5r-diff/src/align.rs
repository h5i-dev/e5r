//! Diffing two instruction streams, so the answer is the line that changed.
//!
//! Function matching says *which* function a patch touched. This says which
//! instruction, which is the question a patch diff is actually asking.
//!
//! The thing that makes this hard is that inserting one instruction shifts
//! every address after it and changes every relative displacement, so a naive
//! comparison of two streams reports the whole tail of the function as
//! changed. The way out is to align on what does not move. That is exactly
//! what [`e5r_db::anchor::shape_token`] computes: everything about an
//! instruction except the addresses it names.
//!
//! Alignment is patience diff over those tokens. Tokens that occur exactly
//! once on each side are unambiguous correspondences, the longest increasing
//! subsequence of them fixes an order-preserving skeleton, and the gaps
//! between them are aligned the same way recursively. Where a gap has no
//! unique token left it falls back to a bounded longest-common-subsequence,
//! and a gap too large for that is reported as a wholesale replacement rather
//! than aligned badly.
//!
//! An aligned pair whose tokens agree still has to be classified, because the
//! tokens deliberately left the addresses out:
//!
//! - the addresses agree, so nothing happened;
//! - they differ, and the difference is exactly what the alignment says the
//!   code moved by, so the instruction did not change, its target was pushed
//!   along by an edit before it ([`EditKind::Displaced`]);
//! - they differ and nothing available accounts for it, which is a real
//!   retarget and is reported as one rather than folded into either bucket.

use std::collections::{BTreeMap, HashMap};

use e5r_analysis::Program;
use e5r_arch::Insn;
use e5r_core::Addr;
use e5r_db::anchor::{addresses, shape_token};
use serde::Serialize;

/// What happened at one position in the stream.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum EditKind {
    /// The new build has an instruction here the old one does not.
    Insert,
    /// The old build has an instruction here the new one does not.
    Delete,
    /// Both builds have an instruction here and they are different.
    Replace,
    /// The same instruction, naming an address that moved by exactly as much
    /// as the code it points at moved. Not a change: it is the shadow of a
    /// change somewhere before it.
    Displaced,
    /// The same instruction, naming a different address, where nothing in
    /// either build accounts for the difference as a displacement. A claim
    /// about the program rather than about the layout.
    Retargeted,
}

impl EditKind {
    /// The word shown in output.
    pub fn as_str(self) -> &'static str {
        match self {
            EditKind::Insert => "insert",
            EditKind::Delete => "delete",
            EditKind::Replace => "replace",
            EditKind::Displaced => "displaced",
            EditKind::Retargeted => "retargeted",
        }
    }

    /// True when this is a change to the program rather than to the layout.
    pub fn is_change(self) -> bool {
        !matches!(self, EditKind::Displaced)
    }
}

/// One instruction-level edit.
#[derive(Debug, Clone, Serialize)]
pub struct Edit {
    /// What happened.
    pub kind: EditKind,
    /// Where it was in the old build, absent for an insertion.
    pub old: Option<Addr>,
    /// Where it is in the new build, absent for a deletion.
    pub new: Option<Addr>,
    /// The old instruction as a listing shows it, empty for an insertion.
    pub old_text: String,
    /// The new instruction, empty for a deletion.
    pub new_text: String,
}

/// What changed inside one matched pair of functions.
#[derive(Debug, Clone, Serialize)]
pub struct FunctionDiff {
    /// Entry in the old build.
    pub old: Addr,
    /// Entry in the new build.
    pub new: Addr,
    /// The name to show.
    pub name: String,
    /// The edits, in stream order. Includes the displaced ones, which are
    /// evidence that the alignment held rather than findings in themselves.
    pub edits: Vec<Edit>,
    /// Instructions that aligned and are identical down to their addresses.
    pub same: u32,
    /// Instructions in the old build.
    pub old_insns: u32,
    /// Instructions in the new build.
    pub new_insns: u32,
    /// True when a gap was too large to align and was reported as a wholesale
    /// replacement. The edit list is then a bound on the change rather than
    /// the change itself, and saying so is cheaper than being believed.
    pub truncated: bool,
}

impl FunctionDiff {
    /// The edits that are changes, which is what a report shows.
    pub fn changes(&self) -> impl Iterator<Item = &Edit> {
        self.edits.iter().filter(|e| e.kind.is_change())
    }

    /// How many edits are changes.
    pub fn change_count(&self) -> usize {
        self.changes().count()
    }

    /// How many instructions moved without changing.
    pub fn displaced_count(&self) -> usize {
        self.edits
            .iter()
            .filter(|e| e.kind == EditKind::Displaced)
            .count()
    }

    /// True when anything at all changed.
    pub fn changed(&self) -> bool {
        self.edits.iter().any(|e| e.kind.is_change())
    }
}

/// Diff the instructions of one matched pair.
///
/// `functions` maps old function entries to new ones, which is what lets a
/// call whose callee moved be told apart from a call that now goes somewhere
/// else. [`crate::Diff`] supplies one through [`mapping`]; an empty map is
/// valid and only costs precision, since an unexplained target is reported as
/// retargeted rather than guessed at.
pub fn compare_function(
    old: &Program,
    old_entry: Addr,
    new: &Program,
    new_entry: Addr,
    functions: &BTreeMap<Addr, Addr>,
) -> Option<FunctionDiff> {
    let fa = old.function(old_entry)?;
    let fb = new.function(new_entry)?;
    let ia = old.instructions(fa);
    let ib = new.instructions(fb);
    let ta: Vec<u64> = ia.iter().map(shape_token).collect();
    let tb: Vec<u64> = ib.iter().map(shape_token).collect();

    let (steps, truncated) = align(&ta, &tb);

    // Where each old instruction ended up, so a branch target inside the
    // function can be followed through the alignment.
    let mut moved: HashMap<Addr, Addr> = HashMap::with_capacity(steps.len());
    for s in &steps {
        if let Step::Pair(i, j) = *s {
            moved.insert(ia[i].addr, ib[j].addr);
        }
    }

    let name = {
        let n = fa.display_name();
        if n.starts_with("sub_") {
            fb.display_name()
        } else {
            n
        }
    };
    let mut out = FunctionDiff {
        old: old_entry,
        new: new_entry,
        name,
        edits: Vec::new(),
        same: 0,
        old_insns: ia.len() as u32,
        new_insns: ib.len() as u32,
        truncated,
    };

    let render = |p: &Program, i: &Insn| e5r_arch::format(&p.object.arch, i, false);

    // Unpaired steps come out of the alignment as separate deletions and
    // insertions. A run of them next to each other is what a person reads as
    // one modification, so the run is paired up positionally and only the
    // overhang stays a pure insertion or deletion.
    let mut group_old: Vec<usize> = Vec::new();
    let mut group_new: Vec<usize> = Vec::new();
    let flush = |out: &mut FunctionDiff, go: &mut Vec<usize>, gn: &mut Vec<usize>| {
        for n in 0..go.len().max(gn.len()) {
            match (go.get(n), gn.get(n)) {
                (Some(i), Some(j)) => {
                    let (a, b) = (&ia[*i], &ib[*j]);
                    // The alignment declined to pair these, but if the tokens
                    // agree after all then only the addresses differ and the
                    // honest answer is the same one a pair would get.
                    let kind = if ta[*i] == tb[*j] {
                        match classify(a, b, &moved, functions) {
                            Verdict::Same => {
                                out.same += 1;
                                continue;
                            }
                            Verdict::Displaced => EditKind::Displaced,
                            Verdict::Retargeted => EditKind::Retargeted,
                        }
                    } else {
                        EditKind::Replace
                    };
                    out.edits.push(Edit {
                        kind,
                        old: Some(a.addr),
                        new: Some(b.addr),
                        old_text: render(old, a),
                        new_text: render(new, b),
                    });
                }
                (Some(i), None) => out.edits.push(Edit {
                    kind: EditKind::Delete,
                    old: Some(ia[*i].addr),
                    new: None,
                    old_text: render(old, &ia[*i]),
                    new_text: String::new(),
                }),
                (None, Some(j)) => out.edits.push(Edit {
                    kind: EditKind::Insert,
                    old: None,
                    new: Some(ib[*j].addr),
                    old_text: String::new(),
                    new_text: render(new, &ib[*j]),
                }),
                (None, None) => {}
            }
        }
        go.clear();
        gn.clear();
    };

    for s in steps {
        match s {
            Step::Old(i) => group_old.push(i),
            Step::New(j) => group_new.push(j),
            Step::Pair(i, j) => {
                flush(&mut out, &mut group_old, &mut group_new);
                let (a, b) = (&ia[i], &ib[j]);
                let kind = match classify(a, b, &moved, functions) {
                    Verdict::Same => {
                        out.same += 1;
                        continue;
                    }
                    Verdict::Displaced => EditKind::Displaced,
                    Verdict::Retargeted => EditKind::Retargeted,
                };
                out.edits.push(Edit {
                    kind,
                    old: Some(a.addr),
                    new: Some(b.addr),
                    old_text: render(old, a),
                    new_text: render(new, b),
                });
            }
        }
    }
    flush(&mut out, &mut group_old, &mut group_new);

    Some(out)
}

/// The old-to-new function map a whole-program diff already worked out.
pub fn mapping(d: &crate::Diff) -> BTreeMap<Addr, Addr> {
    d.matched.iter().map(|m| (m.old, m.new)).collect()
}

/// Instruction-level diffs for every pair the whole-program diff calls changed.
pub fn detail(old: &Program, new: &Program, d: &crate::Diff) -> Vec<FunctionDiff> {
    let map = mapping(d);
    d.changed()
        .filter_map(|m| compare_function(old, m.old, new, m.new, &map))
        .collect()
}

/// What an aligned pair with equal tokens turned out to be.
enum Verdict {
    Same,
    Displaced,
    Retargeted,
}

fn classify(
    a: &Insn,
    b: &Insn,
    moved: &HashMap<Addr, Addr>,
    functions: &BTreeMap<Addr, Addr>,
) -> Verdict {
    let (aa, ba) = (addresses(a), addresses(b));
    // Equal tokens guarantee equal length; a mismatch would mean the token
    // folded something the address list does not depend on, so refuse to
    // guess rather than compare ragged lists.
    if aa.len() != ba.len() {
        return Verdict::Retargeted;
    }
    let mut shifted = false;
    for (x, y) in aa.iter().zip(&ba) {
        if x == y {
            continue;
        }
        // Inside the function the alignment itself says where the target
        // went; outside it, the function matcher does.
        let explained = moved.get(x) == Some(y) || functions.get(x) == Some(y);
        if !explained {
            return Verdict::Retargeted;
        }
        shifted = true;
    }
    if shifted {
        Verdict::Displaced
    } else {
        Verdict::Same
    }
}

/// One step of an alignment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Step {
    /// Old index and new index correspond.
    Pair(usize, usize),
    /// The old build has this index and the new one has nothing for it.
    Old(usize),
    /// The new build has this index and the old one has nothing for it.
    New(usize),
}

/// How deep the patience recursion goes before it stops splitting.
///
/// Each level strips at least one common instruction or one anchor, so a
/// bound here is what keeps the work linear in the worst case rather than
/// quadratic in the number of anchors.
const MAX_DEPTH: u32 = 32;

/// The largest rectangle the fallback will fill in, in cells.
///
/// A million cells is four megabytes of table and a few milliseconds. Beyond
/// it the region is reported as replaced wholesale, which is a worse answer
/// but a bounded one.
const MAX_AREA: usize = 1 << 20;

/// Align two token streams. The flag says whether any region was too large to
/// align and had to be reported as a wholesale replacement.
fn align(a: &[u64], b: &[u64]) -> (Vec<Step>, bool) {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let mut truncated = false;
    patience(a, b, 0, a.len(), 0, b.len(), 0, &mut out, &mut truncated);
    (out, truncated)
}

#[allow(clippy::too_many_arguments)]
fn patience(
    a: &[u64],
    b: &[u64],
    mut alo: usize,
    mut ahi: usize,
    mut blo: usize,
    mut bhi: usize,
    depth: u32,
    out: &mut Vec<Step>,
    truncated: &mut bool,
) {
    // Common ends first. They are the cheapest correspondences there are and
    // stripping them is what keeps the recursion shallow on a small edit.
    while alo < ahi && blo < bhi && a[alo] == b[blo] {
        out.push(Step::Pair(alo, blo));
        alo += 1;
        blo += 1;
    }
    let mut suffix = 0usize;
    while alo < ahi && blo < bhi && a[ahi - 1] == b[bhi - 1] {
        ahi -= 1;
        bhi -= 1;
        suffix += 1;
    }

    if alo == ahi || blo == bhi {
        out.extend((alo..ahi).map(Step::Old));
        out.extend((blo..bhi).map(Step::New));
    } else {
        let anchors = if depth < MAX_DEPTH {
            unique_common(a, b, alo, ahi, blo, bhi)
        } else {
            Vec::new()
        };
        if anchors.is_empty() {
            fallback(a, b, alo, ahi, blo, bhi, out, truncated);
        } else {
            let (mut pa, mut pb) = (alo, blo);
            for (ia, ib) in anchors {
                patience(a, b, pa, ia, pb, ib, depth + 1, out, truncated);
                out.push(Step::Pair(ia, ib));
                pa = ia + 1;
                pb = ib + 1;
            }
            patience(a, b, pa, ahi, pb, bhi, depth + 1, out, truncated);
        }
    }

    for k in 0..suffix {
        out.push(Step::Pair(ahi + k, bhi + k));
    }
}

/// Tokens that occur exactly once on each side, paired and put in an order
/// both streams agree on.
///
/// A token appearing once in each stream is the only kind of correspondence
/// that needs no further evidence: there is nothing else it could be. The
/// longest increasing subsequence then throws away the pairs that would ask
/// for a reordering, because a diff that crosses itself is not a diff.
fn unique_common(
    a: &[u64],
    b: &[u64],
    alo: usize,
    ahi: usize,
    blo: usize,
    bhi: usize,
) -> Vec<(usize, usize)> {
    let mut counts: HashMap<u64, (u32, u32, usize, usize)> = HashMap::with_capacity(ahi - alo);
    for (i, t) in a[alo..ahi].iter().enumerate() {
        let e = counts.entry(*t).or_insert((0, 0, 0, 0));
        e.0 += 1;
        e.2 = alo + i;
    }
    for (j, t) in b[blo..bhi].iter().enumerate() {
        let Some(e) = counts.get_mut(t) else {
            continue;
        };
        e.1 += 1;
        e.3 = blo + j;
    }
    let mut pairs: Vec<(usize, usize)> = counts
        .values()
        .filter(|(ca, cb, _, _)| *ca == 1 && *cb == 1)
        .map(|(_, _, i, j)| (*i, *j))
        .collect();
    pairs.sort_unstable();
    longest_increasing(&pairs)
}

/// The longest subsequence of pairs whose second components also increase.
fn longest_increasing(pairs: &[(usize, usize)]) -> Vec<(usize, usize)> {
    if pairs.is_empty() {
        return Vec::new();
    }
    // Patience sorting: `tails[k]` is the index into `pairs` of the smallest
    // possible tail of an increasing run of length k + 1.
    let mut tails: Vec<usize> = Vec::new();
    let mut back: Vec<Option<usize>> = vec![None; pairs.len()];
    for (n, p) in pairs.iter().enumerate() {
        let at = tails.partition_point(|t| pairs[*t].1 < p.1);
        back[n] = (at > 0).then(|| tails[at - 1]);
        if at == tails.len() {
            tails.push(n);
        } else {
            tails[at] = n;
        }
    }
    let mut chain = Vec::with_capacity(tails.len());
    let mut cur = tails.last().copied();
    while let Some(n) = cur {
        chain.push(pairs[n]);
        cur = back[n];
    }
    chain.reverse();
    chain
}

/// A region with no unique token left in it.
#[allow(clippy::too_many_arguments)]
fn fallback(
    a: &[u64],
    b: &[u64],
    alo: usize,
    ahi: usize,
    blo: usize,
    bhi: usize,
    out: &mut Vec<Step>,
    truncated: &mut bool,
) {
    let (n, m) = (ahi - alo, bhi - blo);
    if n.saturating_mul(m) > MAX_AREA {
        *truncated = true;
        out.extend((alo..ahi).map(Step::Old));
        out.extend((blo..bhi).map(Step::New));
        return;
    }
    // Longest common subsequence, which is the right answer here and is only
    // affordable because the region is bounded.
    let mut len = vec![0u32; (n + 1) * (m + 1)];
    for i in (0..n).rev() {
        for j in (0..m).rev() {
            len[i * (m + 1) + j] = if a[alo + i] == b[blo + j] {
                len[(i + 1) * (m + 1) + j + 1] + 1
            } else {
                len[(i + 1) * (m + 1) + j].max(len[i * (m + 1) + j + 1])
            };
        }
    }
    let (mut i, mut j) = (0, 0);
    while i < n && j < m {
        if a[alo + i] == b[blo + j] {
            out.push(Step::Pair(alo + i, blo + j));
            i += 1;
            j += 1;
        } else if len[(i + 1) * (m + 1) + j] >= len[i * (m + 1) + j + 1] {
            out.push(Step::Old(alo + i));
            i += 1;
        } else {
            out.push(Step::New(blo + j));
            j += 1;
        }
    }
    out.extend((alo + i..ahi).map(Step::Old));
    out.extend((blo + j..bhi).map(Step::New));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn steps(a: &[u64], b: &[u64]) -> Vec<Step> {
        let (s, truncated) = align(a, b);
        assert!(!truncated);
        // An alignment must consume each side exactly once, in order.
        let mut ia: Vec<usize> = Vec::new();
        let mut ib: Vec<usize> = Vec::new();
        for st in &s {
            match *st {
                Step::Pair(i, j) => {
                    ia.push(i);
                    ib.push(j);
                }
                Step::Old(i) => ia.push(i),
                Step::New(j) => ib.push(j),
            }
        }
        assert_eq!(ia, (0..a.len()).collect::<Vec<_>>(), "old side {s:?}");
        assert_eq!(ib, (0..b.len()).collect::<Vec<_>>(), "new side {s:?}");
        s
    }

    #[test]
    fn identical_streams_align_completely() {
        let a = [1, 2, 3, 4, 5];
        assert!(steps(&a, &a).iter().all(|s| matches!(s, Step::Pair(..))));
    }

    #[test]
    fn an_insertion_is_one_step_and_the_rest_still_lines_up() {
        let a = [1u64, 2, 3, 4, 5];
        let b = [1u64, 2, 9, 3, 4, 5];
        let s = steps(&a, &b);
        assert_eq!(
            s.iter().filter(|x| matches!(x, Step::New(_))).count(),
            1,
            "{s:?}"
        );
        assert_eq!(s.iter().filter(|x| matches!(x, Step::Old(_))).count(), 0);
    }

    #[test]
    fn a_deletion_is_one_step() {
        let a = [1u64, 2, 9, 3, 4, 5];
        let b = [1u64, 2, 3, 4, 5];
        let s = steps(&a, &b);
        assert_eq!(s.iter().filter(|x| matches!(x, Step::Old(_))).count(), 1);
        assert_eq!(s.iter().filter(|x| matches!(x, Step::New(_))).count(), 0);
    }

    #[test]
    fn a_substitution_pairs_one_against_one() {
        let a = [1u64, 2, 3, 4, 5];
        let b = [1u64, 2, 9, 4, 5];
        let s = steps(&a, &b);
        assert_eq!(s.iter().filter(|x| matches!(x, Step::Old(_))).count(), 1);
        assert_eq!(s.iter().filter(|x| matches!(x, Step::New(_))).count(), 1);
    }

    #[test]
    fn a_repeated_token_does_not_stop_the_alignment() {
        // Nothing here is unique, so the whole thing goes through the
        // fallback. It still has to find the one inserted token.
        let a = [7u64, 7, 7, 7, 7, 7];
        let b = [7u64, 7, 7, 8, 7, 7, 7];
        let s = steps(&a, &b);
        assert_eq!(s.iter().filter(|x| matches!(x, Step::Old(_))).count(), 0);
        assert_eq!(s.iter().filter(|x| matches!(x, Step::New(_))).count(), 1);
    }

    #[test]
    fn an_insertion_in_the_middle_of_a_long_run_keeps_the_tail() {
        // The shape the whole thing exists for: everything after the edit
        // moved, and none of it is a change.
        let a: Vec<u64> = (0..500).collect();
        let mut b = a.clone();
        b.insert(200, 9999);
        let s = steps(&a, &b);
        assert_eq!(s.iter().filter(|x| matches!(x, Step::New(_))).count(), 1);
        assert_eq!(s.iter().filter(|x| matches!(x, Step::Old(_))).count(), 0);
    }

    #[test]
    fn an_empty_side_is_all_insertion() {
        let s = steps(&[], &[1, 2, 3]);
        assert_eq!(s.len(), 3);
        assert!(s.iter().all(|x| matches!(x, Step::New(_))));
        assert!(steps(&[], &[]).is_empty());
    }

    #[test]
    fn a_reordering_is_reported_rather_than_crossed() {
        // Two blocks swapped. A diff that crossed itself would claim both
        // sides matched; this has to spend real edits on it.
        let a = [1u64, 2, 3, 10, 11, 12];
        let b = [10u64, 11, 12, 1, 2, 3];
        let s = steps(&a, &b);
        let edits = s.iter().filter(|x| !matches!(x, Step::Pair(..))).count();
        assert_eq!(edits, 6, "{s:?}");
    }

    #[test]
    fn a_region_too_large_to_align_says_so() {
        // Every token identical means no anchor anywhere, and a region this
        // wide is past the fallback's budget.
        let a: Vec<u64> = (0..1200).map(|n| 1 + (n % 2)).collect();
        let b: Vec<u64> = (0..1200).map(|n| 2 - (n % 2)).collect();
        let (_, truncated) = align(&a, &b);
        assert!(truncated);
    }
}
