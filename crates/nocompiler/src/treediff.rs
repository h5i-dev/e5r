//! The diff of two block/loop trees (spec-v1-refine.md item 5;
//! docs/isa/refine.md): which intervals of a function changed between A and
//! B, as the data the Lean refinement proof is built from.
//!
//! The two functions' words are aligned (longest common subsequence of
//! identical words). Runs of identical words are lockstep pairs; the gaps
//! between them are the changed intervals. A gap is then grown until it is a
//! region C's `RRegion` can describe (lean/NoCompiler/RefineRegion.lean):
//!
//! * every branch or jump in a paired instruction targets a pair or a
//!   region's entry (otherwise the branch joins the region);
//! * a region has one entry: nothing outside it branches into its interior,
//!   on either side;
//! * a region has one exit: everything leaving it goes to the instruction
//!   just past it, on both sides;
//! * a region does not cut a block or loop of either tree: it lies inside a
//!   node or covers it whole.
//!
//! Live sets come from a backward liveness analysis of each side, with the
//! uses and defs of lean/NoCompiler/RefineCongr.lean; a pair's set is the
//! union of the two sides'. None of this is trusted: the Lean side checks
//! the certificate (`Lockstep.check`) and proves each region (`RRegion.Ok`).

use crate::isa::{self, Instr, Reg};
use crate::profile::Node;
use std::collections::BTreeSet;
use std::fmt::Write as _;

/// One side of the diff: a function's words, its entry and its tree.
pub struct Side<'a> {
    pub entry: u64,
    pub words: &'a [u32],
    pub nodes: &'a [Node],
}

/// A changed interval, as instruction indices `[a0, a1)` in A and `[b0, b1)` in B.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Region {
    pub a0: usize,
    pub a1: usize,
    pub b0: usize,
    pub b1: usize,
    pub live_in: Vec<u8>,
    pub live_out: Vec<u8>,
    /// Both sides are register instructions only (`RRegion.ok_of_seqEquiv` applies).
    pub straight: bool,
    /// A straight-line region whose two sides differ on a live-out register
    /// when run from the same registers (random tests): the register. Its
    /// `Ok` is not attempted; B is likely wrong there (or the live set too
    /// large).
    pub differs: Option<u8>,
}

/// Run a sequence of register instructions on a register file.
fn run_alu(is: &[Instr], g: &mut [u64; 32]) {
    for i in is {
        let r = *g;
        if let Some((rd, v)) =
            crate::sim::alu(i, &|x: Reg| if x.0 == 0 { 0 } else { r[x.0 as usize] })
            && rd.0 != 0
        {
            g[rd.0 as usize] = v;
        }
    }
}

/// A live-out register on which the two sequences differ from equal
/// registers, by random (and edge-value) tests; deterministic.
fn differs(a: &[u32], b: &[u32], out: &[u8]) -> Option<u8> {
    let dec = |w: &[u32]| -> Vec<Instr> { w.iter().filter_map(|x| isa::decode(*x)).collect() };
    let (ia, ib) = (dec(a), dec(b));
    let mut seed: u64 = 0x9e37_79b9_7f4a_7c15;
    let edges = [
        0u64,
        1,
        2,
        u64::MAX,
        1 << 63,
        (1 << 63) - 1,
        0xff,
        0x8000_0000,
        0xffff_ffff,
    ];
    for t in 0..256 {
        let mut g = [0u64; 32];
        for v in g.iter_mut().skip(1) {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            *v = if t % 4 == 0 {
                edges[(seed % edges.len() as u64) as usize]
            } else if t % 4 == 1 {
                seed & 0xff
            } else {
                seed
            };
        }
        let (mut ga, mut gb) = (g, g);
        run_alu(&ia, &mut ga);
        run_alu(&ib, &mut gb);
        if let Some(&r) = out
            .iter()
            .find(|&&r| r != 0 && ga[r as usize] != gb[r as usize])
        {
            return Some(r);
        }
    }
    None
}

/// The result: lockstep pairs (A index, B index, live registers) and regions.
#[derive(Clone, Debug)]
pub struct Diff {
    pub pairs: Vec<(usize, usize, Vec<u8>)>,
    pub regions: Vec<Region>,
}

fn uses(i: &Instr) -> Vec<u8> {
    match *i {
        Instr::Lui(..) | Instr::Auipc(..) | Instr::Jal(..) => vec![],
        Instr::Jalr(_, a, _)
        | Instr::Load(_, _, a, _)
        | Instr::IOp(_, _, a, _)
        | Instr::Addiw(_, a, _)
        | Instr::Shift(_, _, a, _)
        | Instr::ShiftW(_, _, a, _)
        | Instr::UOp(_, _, a) => vec![a.0],
        Instr::Branch(_, a, b, _)
        | Instr::Store(_, a, b, _)
        | Instr::ROp(_, _, a, b)
        | Instr::RWOp(_, _, a, b) => {
            vec![a.0, b.0]
        }
        Instr::Ecall => vec![17, 10, 11, 12],
    }
}

fn defs(i: &Instr) -> Vec<u8> {
    match *i {
        Instr::Branch(..) | Instr::Store(..) => vec![],
        Instr::Ecall => vec![10],
        _ => i.dest().map(|r| vec![r.0]).unwrap_or_default(),
    }
}

/// The registers a caller observes at a return, and ra (`Lockstep.obsRegs`).
fn obs_regs() -> Vec<u8> {
    vec![
        1, 10, 11, 2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27,
    ]
}

fn is_ret(i: &Instr) -> bool {
    matches!(*i, Instr::Jalr(Reg(0), Reg(1), off) if off.signed() == 0)
}

/// Successor instruction indices (None: leaves the function).
fn succs(w: &[u32], k: usize) -> Vec<Option<usize>> {
    let Some(i) = isa::decode(w[k]) else {
        return vec![];
    };
    let at = |off: i64| -> Option<usize> {
        let t = k as i64 + off / 4;
        (0..w.len() as i64).contains(&t).then_some(t as usize)
    };
    match i {
        Instr::Branch(_, _, _, off) => vec![at(4), at(off.signed())],
        Instr::Jal(Reg(0), off) => vec![at(off.signed())],
        Instr::Jalr(..) if is_ret(&i) => vec![],
        Instr::Jalr(..) | Instr::Jal(..) => vec![None],
        _ => vec![at(4)],
    }
}

/// `xor rd, rs, rs` / `sub rd, rs, rs`: writes 0 whatever rs holds.
fn zero_idiom(i: &Instr) -> bool {
    use isa::ROp;
    matches!(*i, Instr::ROp(ROp::Xor | ROp::Sub, _, a, b) if a == b)
}

/// Backward liveness: the live registers at each instruction's entry. An
/// instruction `inside` a region is not checked against `Instr.uses` (its
/// region has its own proof), so a zeroing idiom there reads nothing.
fn liveness(w: &[u32], inside: &dyn Fn(usize) -> bool) -> Vec<BTreeSet<u8>> {
    let n = w.len();
    let mut live = vec![BTreeSet::new(); n];
    loop {
        let mut changed = false;
        for k in (0..n).rev() {
            let Some(i) = isa::decode(w[k]) else { continue };
            let mut out: BTreeSet<u8> = BTreeSet::new();
            if is_ret(&i) {
                out.extend(obs_regs());
            }
            for s in succs(w, k) {
                match s {
                    Some(t) => out.extend(live[t].iter().copied()),
                    None => out.extend(obs_regs()), // leaving the function: be conservative
                }
            }
            for d in defs(&i) {
                out.remove(&d);
            }
            if !(inside(k) && zero_idiom(&i)) {
                out.extend(uses(&i));
            }
            out.insert(0); // x0 reads 0 on both sides; the check wants every use live
            if out != live[k] {
                live[k] = out;
                changed = true;
            }
        }
        if !changed {
            return live;
        }
    }
}

/// What the alignment compares: the word, except that a conditional branch
/// and a `jal zero` are compared without their offsets (C's jump pairs: the
/// same branch on both sides, each with its own offset; the diff then requires
/// the two targets to correspond).
fn key(w: u32) -> u32 {
    match w & 0x7f {
        0x63 => w & 0x01ff_f07f,
        0x6f if (w >> 7) & 0x1f == 0 => w & 0xfff,
        _ => w,
    }
}

/// Longest common subsequence of the words' keys: matched index pairs.
fn lcs(a: &[u32], b: &[u32]) -> Vec<(usize, usize)> {
    let a: Vec<u32> = a.iter().map(|&w| key(w)).collect();
    let b: Vec<u32> = b.iter().map(|&w| key(w)).collect();
    let (n, m) = (a.len(), b.len());
    let mut t = vec![vec![0u32; m + 1]; n + 1];
    for i in (0..n).rev() {
        for j in (0..m).rev() {
            t[i][j] = if a[i] == b[j] {
                t[i + 1][j + 1] + 1
            } else {
                t[i + 1][j].max(t[i][j + 1])
            };
        }
    }
    let (mut i, mut j, mut out) = (0, 0, Vec::new());
    while i < n && j < m {
        if a[i] == b[j] {
            out.push((i, j));
            i += 1;
            j += 1;
        } else if t[i + 1][j] >= t[i][j + 1] {
            i += 1;
        } else {
            j += 1;
        }
    }
    out
}

/// The nodes' intervals as instruction indices.
fn spans(nodes: &[Node], entry: u64, out: &mut Vec<(usize, usize)>) {
    for n in nodes {
        out.push((
            ((n.start - entry) / 4) as usize,
            ((n.end - entry) / 4) as usize,
        ));
        spans(&n.children, entry, out);
    }
}

/// Diff two functions. `Err` when the changed intervals cannot be made
/// single-entry, single-exit regions (e.g. a `ret` inside a change).
pub fn diff(a: &Side, b: &Side) -> Result<Diff, String> {
    let (na, nb) = (a.words.len(), b.words.len());
    let matched = lcs(a.words, b.words);
    // Changed-ness per instruction; regions are maximal changed runs, kept in step.
    let mut ca = vec![true; na];
    let mut cb = vec![true; nb];
    for &(i, j) in &matched {
        ca[i] = false;
        cb[j] = false;
    }
    let mut pairs: Vec<(usize, usize)> = matched.clone();
    let mut sa = Vec::new();
    spans(a.nodes, a.entry, &mut sa);
    let mut sb = Vec::new();
    spans(b.nodes, b.entry, &mut sb);
    // Regions from the current marking: between consecutive pairs.
    let regions_of = |pairs: &[(usize, usize)]| -> Vec<(usize, usize, usize, usize)> {
        let mut rs = Vec::new();
        let (mut pi, mut pj) = (0usize, 0usize);
        for &(i, j) in pairs.iter().chain(std::iter::once(&(na, nb))) {
            if i > pi || j > pj {
                rs.push((pi, i, pj, j));
            }
            pi = i + 1;
            pj = j + 1;
        }
        rs
    };
    for _round in 0..(na + nb + 4) {
        let rs = regions_of(&pairs);
        let entry_of = |i: usize, j: usize| rs.iter().any(|r| r.0 == i && r.2 == j);
        let paired = |i: usize, j: usize| pairs.binary_search(&(i, j)).is_ok();
        let mut drop: BTreeSet<(usize, usize)> = BTreeSet::new();
        // 1. Branch targets of pairs must be pairs or region entries.
        for &(i, j) in &pairs {
            let (s1, s2) = (succs(a.words, i), succs(b.words, j));
            for (x, y) in s1.iter().zip(&s2) {
                if let (Some(x), Some(y)) = (x, y) {
                    if !paired(*x, *y) && !entry_of(*x, *y) {
                        drop.insert((i, j));
                    }
                }
            }
        }
        // 2. A region is non-empty on both sides (A must move; an interval
        // has words): a pure insertion or deletion takes in a neighbour pair,
        // the one after it if that is a register instruction, else the one
        // before.
        for &(a0, a1, b0, b1) in &rs {
            if a0 < a1 && b0 < b1 {
                continue;
            }
            let after = (a1 < na && b1 < nb).then_some((a1, b1));
            let before = (a0 > 0 && b0 > 0).then_some((a0 - 1, b0 - 1));
            let simple = |p: (usize, usize)| {
                isa::decode(a.words[p.0]).is_some_and(|i| {
                    !matches!(i, Instr::Branch(..) | Instr::Jal(..) | Instr::Jalr(..))
                })
            };
            let pick = match (after, before) {
                (Some(x), _) if simple(x) => Some(x),
                (_, Some(y)) => Some(y),
                (x, None) => x,
            };
            match pick {
                Some(p) => {
                    drop.insert(p);
                }
                None => return Err("a change with no neighbour to anchor it".into()),
            }
        }
        // 3-5. Each region: single entry, single exit, no node cut. A
        // violation grows the region just enough on the side it is on: to
        // the source of a jump into it, to the target of a jump out of it,
        // to the bounds of a node it cuts.
        for &(a0, a1, b0, b1) in &rs {
            let mut grow = [(a0, a1), (b0, b1)];
            for (side, (w, spans_)) in [(a.words, &sa), (b.words, &sb)].into_iter().enumerate() {
                let (lo, hi) = grow[side];
                let (mut nlo, mut nhi) = (lo, hi);
                for k in 0..w.len() {
                    let in_r = k >= lo && k < hi;
                    if in_r && t_is_ret(w, k) {
                        return Err(format!(
                            "a return inside the changed interval at {:#x}: a region has one exit",
                            if side == 0 { a.entry } else { b.entry } + 4 * k as u64
                        ));
                    }
                    for t in succs(w, k) {
                        match t {
                            Some(t) if !in_r && t > lo && t < hi => {
                                nlo = nlo.min(k);
                                nhi = nhi.max(k + 1);
                            }
                            Some(t) if in_r && t < lo => nlo = nlo.min(t),
                            Some(t) if in_r && t > hi => nhi = nhi.max(t),
                            None if in_r => {
                                return Err(
                                    "a call or jump out of the function inside a change".into()
                                );
                            }
                            _ => {}
                        }
                    }
                }
                for &(s0, e0) in spans_.iter() {
                    if (s0 > lo && s0 < hi && e0 > hi) || (e0 > lo && e0 < hi && s0 < lo) {
                        nlo = nlo.min(s0);
                        nhi = nhi.max(e0);
                    }
                }
                grow[side] = (nlo, nhi);
            }
            let ((alo, ahi), (blo, bhi)) = (grow[0], grow[1]);
            if (alo, ahi, blo, bhi) != (a0, a1, b0, b1) {
                for &p in &pairs {
                    if (p.0 >= alo && p.0 < ahi) || (p.1 >= blo && p.1 < bhi) {
                        drop.insert(p);
                    }
                }
            }
        }
        if drop.is_empty() {
            let live_a = liveness(a.words, &|k| rs.iter().any(|r| k >= r.0 && k < r.1));
            let live_b = liveness(b.words, &|k| rs.iter().any(|r| k >= r.2 && k < r.3));
            let un = |i: usize, j: usize| -> Vec<u8> {
                let mut s: BTreeSet<u8> = live_a.get(i).cloned().unwrap_or_default();
                s.extend(live_b.get(j).cloned().unwrap_or_default());
                s.into_iter().collect()
            };
            let at_exit = |i: usize, j: usize| -> Vec<u8> {
                if i >= na || j >= nb {
                    obs_regs()
                } else {
                    un(i, j)
                }
            };
            let alu = |w: &[u32], lo: usize, hi: usize| {
                w[lo..hi].iter().all(|x| {
                    isa::decode(*x).is_some_and(|i| {
                        matches!(
                            i,
                            Instr::Lui(..)
                                | Instr::IOp(..)
                                | Instr::Addiw(..)
                                | Instr::Shift(..)
                                | Instr::ShiftW(..)
                                | Instr::ROp(..)
                                | Instr::RWOp(..)
                                | Instr::UOp(..)
                        )
                    })
                })
            };
            let regions = rs
                .iter()
                .map(|&(a0, a1, b0, b1)| Region {
                    a0,
                    a1,
                    b0,
                    b1,
                    live_in: un(a0, b0),
                    live_out: at_exit(a1, b1),
                    straight: alu(a.words, a0, a1) && alu(b.words, b0, b1),
                    differs: None,
                })
                .collect::<Vec<Region>>();
            // A straight-line region whose sides differ at its exit may agree
            // further on (`xor; sltiu` against `sub; sltiu`: a4 differs after
            // the first instruction, not after the second): take in the next
            // pair while it is a register instruction, and settle again.
            let mut regions = regions;
            let mut grown = false;
            for r in regions.iter_mut().filter(|r| r.straight) {
                r.differs = differs(&a.words[r.a0..r.a1], &b.words[r.b0..r.b1], &r.live_out);
                if r.differs.is_some()
                    && r.a1 < na
                    && r.b1 < nb
                    && paired(r.a1, r.b1)
                    && alu(a.words, r.a1, r.a1 + 1)
                {
                    drop.insert((r.a1, r.b1));
                    grown = true;
                }
            }
            if grown {
                pairs.retain(|p| !drop.contains(p));
                continue;
            }
            let pairs = pairs.iter().map(|&(i, j)| (i, j, un(i, j))).collect();
            return Ok(Diff { pairs, regions });
        }
        pairs.retain(|p| !drop.contains(p));
        if pairs.is_empty() {
            return Err("no structured correspondence: the whole function changed".into());
        }
    }
    Err("the diff did not settle".into())
}

fn t_is_ret(w: &[u32], k: usize) -> bool {
    isa::decode(w[k]).is_some_and(|i| is_ret(&i))
}

/// The diff as Lean definitions: the certificate's pairs (`Lockstep.Cert`),
/// the regions (`RRegion`), and for each straight-line region its two
/// instruction lists (for `RRegion.ok_of_seqEquiv`).
/// With the images (`nocompiler export`'s modules, namespaced as their
/// module names), `lean` also writes the proofs C's automation
/// (NoCompiler/RefineAuto.lean) gives: `region<k>_ok` for each straight-line
/// region, and `refines`, with the other regions' `Ok` as hypotheses.
pub struct Proofs<'a> {
    pub img_a: &'a str,
    pub img_b: &'a str,
    /// The function's identifier in each image (`lean::ident`).
    pub id_a: String,
    pub id_b: String,
    /// Close straight-line regions with `nocompiler_region_bv` (the
    /// bv_decide tier) instead of the kernel tier.
    pub bv: bool,
}

pub fn lean(
    d: &Diff,
    a: &Side,
    b: &Side,
    ns: &str,
    title: &str,
    proofs: Option<&Proofs>,
) -> String {
    let mut o = String::new();
    let regs = |r: &[u8]| {
        r.iter()
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(", ")
    };
    let pa = |i: usize| a.entry + 4 * i as u64;
    let pb = |j: usize| b.entry + 4 * j as u64;
    let _ = writeln!(
        o,
        "/-\nGenerated by `nocompiler refine` {}; do not edit.\n{title}\n-/",
        env!("CARGO_PKG_VERSION")
    );
    let _ = writeln!(
        o,
        "import NoCompiler.RefineStraightRegion\nimport NoCompiler.RefineLockstep"
    );
    if let Some(p) = proofs {
        let _ = writeln!(
            o,
            "import NoCompiler.RefineAuto\nimport {}\nimport {}",
            p.img_a, p.img_b
        );
    }
    let _ = writeln!(o, "\nnamespace {ns}\nopen NoCompiler\n");
    for (k, r) in d.regions.iter().enumerate() {
        let dom = |p: u64, n: usize| format!("[(0x{p:x}#64, {})]", 4 * n);
        let kind = if r.straight {
            "straight-line"
        } else {
            "structured"
        };
        let _ = writeln!(
            o,
            "/-- Changed interval {k} ({kind}). -/\ndef region{k} : RRegion where\n  pa := 0x{:x}#64\n  pb := 0x{:x}#64\n  paExit := 0x{:x}#64\n  pbExit := 0x{:x}#64\n  domA := {}\n  domB := {}\n  liveIn := [{}]\n  liveOut := [{}]\n",
            pa(r.a0),
            pb(r.b0),
            pa(r.a1),
            pb(r.b1),
            dom(pa(r.a0), r.a1 - r.a0),
            dom(pb(r.b0), r.b1 - r.b0),
            regs(&r.live_in),
            regs(&r.live_out)
        );
    }
    let names: Vec<String> = (0..d.regions.len()).map(|k| format!("region{k}")).collect();
    let _ = writeln!(
        o,
        "/-- The certificate: the unchanged instructions as pairs (B at `pb` in step"
    );
    let _ = writeln!(
        o,
        "    with A at `pa`), and the changed intervals as regions. -/"
    );
    let _ = writeln!(o, "def cert : Lockstep.Cert where\n  pairs := [");
    for (k, (i, j, l)) in d.pairs.iter().enumerate() {
        let sep = if k + 1 < d.pairs.len() { "," } else { "" };
        let _ = writeln!(
            o,
            "    ⟨0x{:x}#64, 0x{:x}#64, [{}]⟩{sep}",
            pb(*j),
            pa(*i),
            regs(l)
        );
    }
    let _ = writeln!(o, "  ]\n  regions := [{}]", names.join(", "));
    for (k, r) in d.regions.iter().enumerate() {
        if !r.straight {
            continue;
        }
        let list = |w: &[u32]| {
            w.iter()
                .map(|x| isa::decode(*x).unwrap().lean())
                .collect::<Vec<_>>()
                .join(", ")
        };
        let _ = writeln!(
            o,
            "\n/-- Region {k}, straight-line: A's and B's instructions. -/"
        );
        let _ = writeln!(
            o,
            "def region{k}_as : List Instr := [{}]",
            list(&a.words[r.a0..r.a1])
        );
        let _ = writeln!(
            o,
            "def region{k}_bs : List Instr := [{}]",
            list(&b.words[r.b0..r.b1])
        );
    }
    if let Some(p) = proofs {
        let (ca, cb) = (format!("{}.code", p.img_a), format!("{}.code", p.img_b));
        let tac = if p.bv {
            "nocompiler_region_bv"
        } else {
            "nocompiler_region"
        };
        let list = |w: &[u32]| {
            w.iter()
                .map(|x| isa::decode(*x).unwrap().lean())
                .collect::<Vec<_>>()
                .join(", ")
        };
        let (mut hyps, mut uses) = (Vec::new(), Vec::new());
        for (k, r) in d.regions.iter().enumerate() {
            if r.straight && r.differs.is_none() {
                let _ = writeln!(
                    o,
                    "\ntheorem region{k}_ok : region{k}.Ok {ca} {cb} := by\n  {tac} region{k} [{}]\n    [{}]",
                    list(&a.words[r.a0..r.a1]),
                    list(&b.words[r.b0..r.b1])
                );
                uses.push(format!("region{k}_ok"));
            } else {
                hyps.push(format!(" (h{k} : region{k}.Ok {ca} {cb})"));
                uses.push(format!("h{k}"));
            }
        }
        let _ = writeln!(
            o,
            "\n/-- B refines A, for every specification A runs under (`hA`){}. -/",
            if hyps.is_empty() {
                ""
            } else {
                ", given the structured regions' proofs"
            }
        );
        let body = if uses.is_empty() {
            "\n  Refines.of_cert (k := cert) hA (by decide +kernel) (by intro r h; simp [cert] at h)"
                .to_string()
        } else {
            format!(" by\n  nocompiler_refine cert [{}]", uses.join(", "))
        };
        let _ = writeln!(
            o,
            "theorem refines {{α : Type}} (sp : Spec α)\n    (hA : ARuns sp {ca} {ia}.{}_dom {ia}.{}_entry){} :\n    Refines sp {ca} {ia}.{}_dom {ia}.{}_entry\n      {cb} {ib}.{}_dom {ib}.{}_entry :={body}",
            p.id_a,
            p.id_a,
            hyps.concat(),
            p.id_a,
            p.id_a,
            p.id_b,
            p.id_b,
            ia = p.img_a,
            ib = p.img_b,
        );
    }
    let _ = writeln!(o, "\nend {ns}");
    o
}

/// A human summary of the diff.
pub fn summary(d: &Diff, a: &Side, b: &Side) -> String {
    let mut o = String::new();
    let _ = writeln!(
        o,
        "{} instructions paired; {} changed interval(s)",
        d.pairs.len(),
        d.regions.len()
    );
    for (k, r) in d.regions.iter().enumerate() {
        let _ = writeln!(
            o,
            "  region {k}: A [{:#x}, {:#x}) {} instr  <->  B [{:#x}, {:#x}) {} instr  {}  live in [{}] out [{}]",
            a.entry + 4 * r.a0 as u64,
            a.entry + 4 * r.a1 as u64,
            r.a1 - r.a0,
            b.entry + 4 * r.b0 as u64,
            b.entry + 4 * r.b1 as u64,
            r.b1 - r.b0,
            match (r.straight, r.differs) {
                (true, None) => "straight-line".to_string(),
                (true, Some(x)) => format!(
                    "straight-line, DIFFERS on {} from equal registers",
                    crate::text::reg_name(x)
                ),
                _ => "structured (subtree)".to_string(),
            },
            r.live_in
                .iter()
                .map(|x| crate::text::reg_name(*x))
                .collect::<Vec<_>>()
                .join(" "),
            r.live_out
                .iter()
                .map(|x| crate::text::reg_name(*x))
                .collect::<Vec<_>>()
                .join(" "),
        );
    }
    o
}
