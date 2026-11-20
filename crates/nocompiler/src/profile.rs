//! The structural rules of the nocompiler profile (docs/isa/profile.md, section 4)
//! and the recovery of the block/loop tree a conforming function has.
//!
//! `recover` builds the tree from the control-flow graph; `check` verifies a
//! function against a tree, wherever the tree came from (`recover`, or the
//! `.nocompiler.struct` section a compiler wrote). The checker is what decides
//! conformance; `recover` is only a way to produce something for it to check.

use crate::frame;
use crate::isa::{self, Instr};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Kind {
    Block,
    Loop,
}

/// A `block` or `loop` covering the instructions in `[start, end)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Node {
    pub kind: Kind,
    pub start: u64,
    pub end: u64,
    /// The label (`$done`), if the writer gave one; `disasm` names the rest.
    pub label: Option<String>,
    pub children: Vec<Node>,
}

/// The conformance level of a function (docs/isa/v1.md): L0 decodes (R1),
/// L1 is structured (R1 to R3), L2 also keeps the register, stack and frame
/// rules (R4 to R6).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Level {
    L0,
    L1,
    L2,
}

/// What an 8-byte frame slot holds (rule 6b).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SlotKind {
    /// The entry value of a callee-saved register, or of `ra` (rule 6e).
    Save(isa::Reg),
    /// A spilled value.
    Spill,
}

/// An 8-byte, 8-aligned frame slot, at `off` bytes above the bottom of the frame.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Slot {
    pub off: u64,
    pub kind: SlotKind,
}

/// Where the length of an address-taken range came from (v1 decision 5).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RangeSource {
    /// Written by whoever produced the code (the structured form, a compiler).
    Declared,
    /// The size of the variable in the DWARF debug information.
    Dwarf,
    /// No debug information: the gap up to the next slot or range.
    Heuristic,
}

/// An address-taken range of the frame: `len` bytes from `off` above its bottom.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Range {
    pub off: u64,
    pub len: u64,
    pub source: RangeSource,
}

/// What `.nocompiler.struct` records for one function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FuncMeta {
    pub name: String,
    pub entry: u64,
    pub size: u64,
    /// The level the checker reached.
    pub level: Level,
    /// Bytes of stack below the entry sp the function uses (its own frame).
    pub frame: u64,
    /// The frame plus the deepest callee's `depth` (theorem T4); `None` when a
    /// callee's depth is not known (it is not in the same table).
    pub depth: Option<u64>,
    /// Entries of the functions it calls or tail-calls, sorted.
    pub callees: Vec<u64>,
    /// Top-level nodes; the function body itself is the implicit root.
    pub nodes: Vec<Node>,
    /// The frame's partition (rule 6b), by offset; bytes in neither are unused.
    pub slots: Vec<Slot>,
    pub ranges: Vec<Range>,
    /// Reserved for proof hints; carried through unchanged.
    pub ext: Vec<u8>,
}

/// A function's code, as found in the binary.
#[derive(Clone, Debug)]
pub struct Func {
    pub name: String,
    pub entry: u64,
    pub words: Vec<u32>,
}

impl Func {
    pub fn end(&self) -> u64 {
        self.entry + 4 * self.words.len() as u64
    }
    pub fn contains(&self, a: u64) -> bool {
        a >= self.entry && a < self.end() && (a - self.entry) % 4 == 0
    }
    /// The decoded instruction at `a` (an address of the function).
    pub fn instr(&self, a: u64) -> Option<Instr> {
        self.at(a)
    }
    fn at(&self, a: u64) -> Option<Instr> {
        isa::decode(self.words[((a - self.entry) / 4) as usize])
    }
    fn addrs(&self) -> impl Iterator<Item = u64> + '_ {
        (0..self.words.len() as u64).map(|i| self.entry + 4 * i)
    }
}

/// A violation, at an address.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Violation {
    pub addr: u64,
    pub rule: &'static str,
    pub detail: String,
}

impl fmt::Display for Violation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:#x}: [{}] {}", self.addr, self.rule, self.detail)
    }
}

fn v(addr: u64, rule: &'static str, detail: impl Into<String>) -> Violation {
    Violation {
        addr,
        rule,
        detail: detail.into(),
    }
}

/// How control leaves one instruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Flow {
    Next,
    /// Conditional: the target or the next instruction.
    Branch(u64),
    /// `jal x0` inside the function.
    Jump(u64),
    /// A call returning to the next instruction (`jal ra`, or `auipc ra; jalr ra`).
    Call(u64),
    /// A jump to another function's entry that does not return here.
    Tail(u64),
    Ret,
}

fn target(pc: u64, i: isa::Imm) -> u64 {
    pc.wrapping_add(i.signed() as u64)
}

/// The control flow of the instruction at `pc`, or why it is not allowed.
/// `entries` are the entries of every function in the binary.
pub fn flow(f: &Func, pc: u64, entries: &BTreeSet<u64>) -> Result<Flow, Violation> {
    let Some(i) = f.at(pc) else {
        return Err(v(
            pc,
            "R1 decode",
            format!(
                "{:#010x} is not in the profile",
                f.words[((pc - f.entry) / 4) as usize]
            ),
        ));
    };
    let prev = if pc > f.entry { f.at(pc - 4) } else { None };
    Ok(match i {
        Instr::Branch(_, _, _, off) => {
            let t = target(pc, off);
            if !f.contains(t) {
                return Err(v(
                    pc,
                    "R2 control",
                    format!("branch to {t:#x} leaves the function"),
                ));
            }
            Flow::Branch(t)
        }
        Instr::Jal(rd, off) => {
            let t = target(pc, off);
            if rd == isa::ZERO {
                if f.contains(t) {
                    Flow::Jump(t)
                } else if entries.contains(&t) {
                    Flow::Tail(t)
                } else {
                    return Err(v(
                        pc,
                        "R2 control",
                        format!("jump to {t:#x}, neither in the function nor a function entry"),
                    ));
                }
            } else if rd == isa::RA {
                if !entries.contains(&t) {
                    return Err(v(
                        pc,
                        "R2 control",
                        format!("call to {t:#x}, which is not a function entry"),
                    ));
                }
                Flow::Call(t)
            } else {
                return Err(v(
                    pc,
                    "R2 control",
                    format!("jal links {rd}; only ra or zero"),
                ));
            }
        }
        Instr::Jalr(rd, rs1, off) => {
            if rd == isa::ZERO && rs1 == isa::RA && off.value == 0 {
                Flow::Ret
            } else if let Some(Instr::Auipc(ar, hi)) = prev {
                // auipc r, hi; jalr rd, lo(r): a direct call or tail call the
                // linker did not relax to jal.
                if ar != rs1 {
                    return Err(v(
                        pc,
                        "R2 control",
                        "jalr not paired with the auipc before it",
                    ));
                }
                let base = (pc - 4).wrapping_add(((hi.value as i32) << 12) as i64 as u64);
                let t = base.wrapping_add(off.signed() as u64) & !1;
                if !entries.contains(&t) {
                    return Err(v(
                        pc,
                        "R2 control",
                        format!("auipc/jalr to {t:#x}, which is not a function entry"),
                    ));
                }
                if rd == isa::RA && rs1 == isa::RA {
                    Flow::Call(t)
                } else if rd == isa::ZERO && rs1 == isa::T1 {
                    Flow::Tail(t)
                } else {
                    return Err(v(
                        pc,
                        "R2 control",
                        "auipc/jalr pair must be ra,ra (call) or zero,t1 (tail)",
                    ));
                }
            } else {
                return Err(v(
                    pc,
                    "R2 control",
                    "indirect jump; only ret and auipc/jalr calls are in the profile",
                ));
            }
        }
        _ => Flow::Next,
    })
}

fn succs(pc: u64, fl: Flow) -> Vec<u64> {
    match fl {
        Flow::Next | Flow::Call(_) => vec![pc + 4],
        Flow::Branch(t) => vec![pc + 4, t],
        Flow::Jump(t) => vec![t],
        Flow::Tail(_) | Flow::Ret => vec![],
    }
}

/// The block/loop tree of a function, from its control flow. Fails on
/// control flow that has no such tree (a jump into the middle of a loop).
pub fn recover(f: &Func, entries: &BTreeSet<u64>) -> Result<Vec<Node>, Violation> {
    let mut loops: BTreeMap<u64, u64> = BTreeMap::new(); // header -> end
    let mut blocks: BTreeMap<u64, u64> = BTreeMap::new(); // end (target) -> start
    for pc in f.addrs() {
        let fl = flow(f, pc, entries)?;
        let t = match fl {
            Flow::Branch(t) | Flow::Jump(t) => t,
            _ => continue,
        };
        if t <= pc {
            let e = loops.entry(t).or_insert(pc + 4);
            *e = (*e).max(pc + 4);
        } else if t > pc + 4 {
            let s = blocks.entry(t).or_insert(pc);
            *s = (*s).min(pc);
        }
    }
    // (start, end, kind). Blocks may grow left and loops right without
    // changing what any branch means; repeat until no two intervals cross.
    let mut iv: Vec<(u64, u64, Kind)> = loops
        .iter()
        .map(|(&h, &e)| (h, e, Kind::Loop))
        .chain(blocks.iter().map(|(&t, &s)| (s, t, Kind::Block)))
        .collect();
    loop {
        let mut changed = false;
        for i in 0..iv.len() {
            for j in 0..iv.len() {
                let (x, y) = (iv[i], iv[j]);
                // x = [x1, x2) and y = [y1, y2) cross: x1 < y1 < x2 < y2.
                if !(x.0 < y.0 && y.0 < x.1 && x.1 < y.1) {
                    continue;
                }
                if y.2 == Kind::Block {
                    iv[j].0 = x.0;
                } else if x.2 == Kind::Loop {
                    iv[i].1 = y.1;
                } else {
                    return Err(v(
                        x.1,
                        "R3 structure",
                        format!(
                            "forward jump from {:#x} into the loop at {:#x}: no structured form",
                            x.0, y.0
                        ),
                    ));
                }
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    iv.sort_by(|a, b| a.0.cmp(&b.0).then(b.1.cmp(&a.1)).then(a.2.cmp(&b.2)));
    iv.dedup();
    Ok(nest(&iv))
}

fn nest(iv: &[(u64, u64, Kind)]) -> Vec<Node> {
    let mut out: Vec<Node> = Vec::new();
    let mut i = 0;
    while i < iv.len() {
        let (s, e, k) = iv[i];
        let mut j = i + 1;
        while j < iv.len() && iv[j].1 <= e && iv[j].0 >= s {
            j += 1;
        }
        out.push(Node {
            kind: k,
            start: s,
            end: e,
            label: None,
            children: nest(&iv[i + 1..j]),
        });
        i = j;
    }
    out
}

/// The nodes enclosing `pc`, innermost last.
fn enclosing<'n>(nodes: &'n [Node], pc: u64, acc: &mut Vec<&'n Node>) {
    for n in nodes {
        if n.start <= pc && pc < n.end {
            acc.push(n);
            enclosing(&n.children, pc, acc);
        }
    }
}

fn check_tree(f: &Func, nodes: &[Node], lo: u64, hi: u64, out: &mut Vec<Violation>) {
    let mut last = lo;
    for n in nodes {
        if n.start >= n.end
            || n.start < last
            || n.end > hi
            || n.start % 4 != 0
            || n.end % 4 != 0
            || !f.contains(n.start)
        {
            out.push(v(
                n.start,
                "R3 structure",
                format!(
                    "{:?} [{:#x}, {:#x}) is not nested inside [{:#x}, {:#x}) after {:#x}",
                    n.kind, n.start, n.end, lo, hi, last
                ),
            ));
        }
        check_tree(f, &n.children, n.start, n.end, out);
        last = n.end;
    }
}

/// The outcome of checking one function that reaches L1: its metadata (the
/// level it reached, the frame partition used) and, below L2, why it missed
/// L2.
#[derive(Clone, Debug)]
pub struct Checked {
    pub meta: FuncMeta,
    pub missed: Vec<Violation>,
    /// At L2: the certificate the Lean checker checks (frame::certificate).
    pub cert: Vec<frame::CertFact>,
}

/// Why a function is below L1: `level` is L0 when it decodes (R1) but breaks
/// R2 or R3, `None` when it does not decode.
#[derive(Clone, Debug)]
pub struct Failed {
    pub level: Option<Level>,
    pub violations: Vec<Violation>,
}

/// Check one function against a tree, inferring the frame partition (no
/// debug information). See `check_with`.
pub fn check(
    f: &Func,
    nodes: &[Node],
    entries: &BTreeSet<u64>,
) -> Result<FuncMeta, Vec<Violation>> {
    check_with(f, nodes, None, None, entries)
        .map(|c| c.meta)
        .map_err(|e| e.violations)
}

fn sorted(mut out: Vec<Violation>) -> Vec<Violation> {
    out.sort_by(|a, b| {
        a.addr
            .cmp(&b.addr)
            .then(a.rule.cmp(b.rule))
            .then(a.detail.cmp(&b.detail))
    });
    out.dedup();
    out
}

/// Check one function against a tree and a frame partition (`None`: infer
/// one, with range lengths from `dwarf` where it has them). Reaching L1 is
/// `Ok`, with the level and, below L2, the rules L2 needs that failed.
pub fn check_with(
    f: &Func,
    nodes: &[Node],
    part: Option<&frame::Partition>,
    dwarf: Option<&BTreeMap<u64, u64>>,
    entries: &BTreeSet<u64>,
) -> Result<Checked, Failed> {
    // L1: R1 to R3.
    let mut l1 = Vec::new();
    check_tree(f, nodes, f.entry, f.end(), &mut l1);
    let mut flows = BTreeMap::new();
    let mut decodes = true;
    for pc in f.addrs() {
        match flow(f, pc, entries) {
            Ok(fl) => {
                flows.insert(pc, fl);
            }
            Err(e) => {
                decodes &= e.rule != "R1 decode";
                l1.push(e)
            }
        }
    }
    // The jalr of an auipc/jalr pair takes its target from the register the
    // auipc set, so it may only be reached from that auipc.
    let pair_jalrs: BTreeSet<u64> = flows
        .iter()
        .filter(|(pc, fl)| {
            matches!(fl, Flow::Call(_) | Flow::Tail(_))
                && matches!(f.at(**pc), Some(Instr::Jalr(..)))
        })
        .map(|(&pc, _)| pc)
        .collect();
    let mut callees = BTreeSet::new();
    let mut l2 = Vec::new();
    for (&pc, &fl) in &flows {
        if let Flow::Branch(t) | Flow::Jump(t) = fl {
            if pair_jalrs.contains(&t) {
                l1.push(v(
                    pc,
                    "R2 control",
                    format!("branch to {t:#x}, the jalr of an auipc/jalr pair"),
                ));
            }
        }
        let i = f.at(pc).expect("decoded above");
        match fl {
            Flow::Branch(t) | Flow::Jump(t) if t != pc + 4 => {
                let mut enc = Vec::new();
                enclosing(nodes, pc, &mut enc);
                let ok = enc.iter().any(|n| match n.kind {
                    Kind::Block => n.end == t,
                    Kind::Loop => n.start == t,
                });
                if !ok {
                    l1.push(v(
                        pc,
                        "R3 structure",
                        format!("target {t:#x} is neither the end of an enclosing block nor the head of an enclosing loop"),
                    ));
                }
            }
            Flow::Call(t) | Flow::Tail(t) => {
                callees.insert(t);
            }
            _ => {}
        }
        if let Some(rd) = i.dest() {
            if rd == isa::GP || rd == isa::TP {
                l2.push(v(pc, "R4 registers", format!("writes {rd}")));
            }
            if rd == isa::SP && !matches!(i, Instr::IOp(isa::IOp::Addi, _, isa::SP, _)) {
                l2.push(v(pc, "R5 stack", "sp written other than by addi sp, sp, k"));
            }
        }
    }
    if let Some((&last, &fl)) = flows.iter().next_back() {
        if !matches!(fl, Flow::Ret | Flow::Jump(_) | Flow::Tail(_)) {
            l1.push(v(
                last,
                "R2 control",
                "the last instruction falls through past the function",
            ));
        }
    }
    if !l1.is_empty() {
        return Err(Failed {
            level: decodes.then_some(Level::L0),
            violations: sorted(l1),
        });
    }
    // R5: sp offset from the entry sp, the same along every path.
    let mut off: BTreeMap<u64, i64> = BTreeMap::new();
    let mut work = vec![f.entry];
    off.insert(f.entry, 0);
    let mut min = 0i64;
    while let Some(pc) = work.pop() {
        let Some(&fl) = flows.get(&pc) else { continue };
        let mut o = off[&pc];
        if let Some(Instr::IOp(isa::IOp::Addi, isa::SP, isa::SP, k)) = f.at(pc) {
            if k.signed() % 16 != 0 {
                l2.push(v(
                    pc,
                    "R5 stack",
                    format!("sp adjusted by {}, not a multiple of 16", k.signed()),
                ));
            }
            o += k.signed();
            min = min.min(o);
        }
        match fl {
            Flow::Ret | Flow::Tail(_) if o != 0 => {
                l2.push(v(
                    pc,
                    "R5 stack",
                    format!("leaves with sp {o} from its entry value"),
                ));
            }
            Flow::Call(_) if o % 16 != 0 => {
                l2.push(v(pc, "R5 stack", format!("calls with sp misaligned ({o})")));
            }
            _ => {}
        }
        for s in succs(pc, fl) {
            if !f.contains(s) {
                continue;
            }
            match off.get(&s) {
                None => {
                    off.insert(s, o);
                    work.push(s);
                }
                Some(&p) if p != o => {
                    l2.push(v(
                        s,
                        "R5 stack",
                        format!("sp offset {p} on one path, {o} on another"),
                    ));
                }
                _ => {}
            }
        }
    }
    let frame = (-min) as u64;
    // R6 and R4's ra, against the partition (given or inferred). Only with
    // R5's offsets well defined.
    let r5_ok = !l2.iter().any(|x| x.rule == "R5 stack");
    let part = match part {
        Some(p) => p.clone(),
        None if r5_ok => frame::infer(f, &flows, &off, frame, dwarf),
        None => frame::Partition::default(),
    };
    if r5_ok {
        l2.extend(frame::check(f, &flows, &off, frame, &part));
    }
    let l2 = sorted(l2);
    let cert = if l2.is_empty() {
        frame::certificate(f, &flows, &off, frame, &part)
    } else {
        vec![]
    };
    Ok(Checked {
        cert,
        meta: FuncMeta {
            name: f.name.clone(),
            entry: f.entry,
            size: 4 * f.words.len() as u64,
            level: if l2.is_empty() { Level::L2 } else { Level::L1 },
            frame,
            depth: None,
            callees: callees.into_iter().collect(),
            nodes: nodes.to_vec(),
            slots: part.slots,
            ranges: part.ranges,
            ext: vec![],
        },
        missed: l2,
    })
}
