//! The frame rule R6 and the `ra` half of R4 (docs/isa/v1.md, "R6 frame"),
//! and the inference of a frame's partition for code that comes without one
//! (clang's output through `nocompiler annotate`).
//!
//! Offsets in a partition count from the bottom of the frame: the entry `sp`
//! minus `frame`. An access `k(sp)` at an instruction where `sp` is `off`
//! bytes from its entry value (rule R5, `off <= 0`) is at frame offset
//! `frame + off + k`.
//!
//! Nothing here is trusted: the Lean checker decides the same rules, and a
//! wrong partition only makes a function miss L2 (or a proof fail).

use crate::isa::{self, Instr, Reg};
use crate::profile::{Flow, Func, Range, RangeSource, Slot, SlotKind, Violation};
use std::collections::{BTreeMap, BTreeSet};

/// Registers whose entry value a function must give back (rule 6e): `ra`, and
/// the callee-saved `s0` to `s11`. (`sp` is R5's; `gp` and `tp` are never
/// written, R4.)
pub const SAVED: [u8; 13] = [1, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27];

fn saved(r: Reg) -> bool {
    SAVED.contains(&r.0)
}

fn v(addr: u64, rule: &'static str, detail: impl Into<String>) -> Violation {
    Violation {
        addr,
        rule,
        detail: detail.into(),
    }
}

/// A frame's partition into slots and address-taken ranges (rule 6b).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Partition {
    pub slots: Vec<Slot>,
    pub ranges: Vec<Range>,
}

impl Partition {
    fn slot_at(&self, off: u64) -> Option<&Slot> {
        self.slots.iter().find(|s| s.off == off)
    }
    fn save_slot(&self, r: Reg) -> Option<&Slot> {
        self.slots.iter().find(|s| s.kind == SlotKind::Save(r))
    }
    fn range_of(&self, off: u64, w: u64) -> Option<&Range> {
        self.ranges
            .iter()
            .find(|r| r.off <= off && off + w <= r.off + r.len)
    }
}

/// An `sp`-based access: frame offset (may be outside the frame), width,
/// and whether it is an `ld`/`sd`.
#[derive(Clone, Copy, Debug)]
struct Access {
    fo: i64,
    w: u64,
    ldsd: bool,
}

fn access(i: &Instr, off: i64, frame: u64) -> Option<Access> {
    let (w, k, ldsd) = match *i {
        Instr::Load(op, _, isa::SP, k) => (op.width(), k, op == isa::LdOp::Ld),
        Instr::Store(op, isa::SP, _, k) => (op.width(), k, op == isa::StOp::Sd),
        _ => return None,
    };
    Some(Access {
        fo: frame as i64 + off + k.signed(),
        w,
        ldsd,
    })
}

/// The address `addi rd, sp, k` takes, as a frame offset.
fn taken(i: &Instr, off: i64, frame: u64) -> Option<i64> {
    match *i {
        Instr::IOp(isa::IOp::Addi, rd, isa::SP, k) if rd != isa::SP => {
            Some(frame as i64 + off + k.signed())
        }
        _ => None,
    }
}

/// 6a: the forms in which `sp` may be an operand.
fn sp_form_ok(i: &Instr) -> bool {
    match *i {
        Instr::IOp(isa::IOp::Addi, _, isa::SP, _) => true,
        Instr::Load(_, _, isa::SP, _) => true,
        Instr::Store(_, base, src, _) => {
            src != isa::SP && (base == isa::SP || !i.srcs().contains(&isa::SP))
        }
        _ => !i.srcs().contains(&isa::SP),
    }
}

/// The dataflow fact before an instruction (rule 6e): which saved registers
/// hold their entry value, and which slots hold the entry value of which
/// register.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Fact {
    keep: BTreeSet<u8>,
    slots: BTreeMap<u64, Reg>,
}

impl Fact {
    fn entry() -> Fact {
        Fact {
            keep: SAVED.iter().copied().collect(),
            slots: BTreeMap::new(),
        }
    }
    fn meet(&self, o: &Fact) -> Fact {
        Fact {
            keep: self.keep.intersection(&o.keep).copied().collect(),
            slots: self
                .slots
                .iter()
                .filter(|(k, r)| o.slots.get(k) == Some(r))
                .map(|(&k, &r)| (k, r))
                .collect(),
        }
    }
}

/// What one instruction does to the fact. `store_note` receives every `sd`
/// to a frame slot offset with its source register and whether that register
/// then held its entry value.
fn transfer(
    i: &Instr,
    a: Option<Access>,
    f: &Fact,
    part: &Partition,
    note: &mut dyn FnMut(u64, Reg, bool),
) -> Fact {
    let mut g = f.clone();
    match (*i, a) {
        (Instr::Store(isa::StOp::Sd, isa::SP, src, _), Some(a)) if a.fo >= 0 => {
            let fo = a.fo as u64;
            let entry_val = saved(src) && f.keep.contains(&src.0);
            note(fo, src, entry_val);
            match part.slot_at(fo).map(|s| s.kind) {
                Some(SlotKind::Save(r)) if r == src && entry_val => {
                    g.slots.insert(fo, src);
                }
                _ => {
                    g.slots.remove(&fo);
                }
            }
            // A store into a range or unused bytes overlapping a slot is 6c's.
        }
        (Instr::Load(isa::LdOp::Ld, rd, isa::SP, _), Some(a)) if a.fo >= 0 => {
            let fo = a.fo as u64;
            if g.slots.get(&fo) == Some(&rd) {
                g.keep.insert(rd.0);
            } else {
                g.keep.remove(&rd.0);
            }
        }
        _ => {
            if let Some(rd) = i.dest() {
                g.keep.remove(&rd.0);
            }
        }
    }
    g
}

fn succs(pc: u64, fl: Flow) -> Vec<u64> {
    match fl {
        Flow::Next | Flow::Call(_) => vec![pc + 4],
        Flow::Branch(t) => vec![pc + 4, t],
        Flow::Jump(t) => vec![t],
        Flow::Tail(_) | Flow::Ret => vec![],
    }
}

/// The 6e facts before every reachable instruction.
fn facts(
    f: &Func,
    flows: &BTreeMap<u64, Flow>,
    offs: &BTreeMap<u64, i64>,
    frame: u64,
    part: &Partition,
    note: &mut dyn FnMut(u64, u64, Reg, bool),
) -> BTreeMap<u64, Fact> {
    let mut at: BTreeMap<u64, Fact> = BTreeMap::new();
    at.insert(f.entry, Fact::entry());
    let mut work = vec![f.entry];
    while let Some(pc) = work.pop() {
        let (Some(&fl), Some(&off), Some(i)) = (flows.get(&pc), offs.get(&pc), f.instr(pc)) else {
            continue;
        };
        let before = at[&pc].clone();
        let after = transfer(
            &i,
            access(&i, off, frame),
            &before,
            part,
            &mut |fo, r, e| note(pc, fo, r, e),
        );
        for s in succs(pc, fl) {
            if !f.contains(s) {
                continue;
            }
            let merged = match at.get(&s) {
                None => after.clone(),
                Some(old) => old.meet(&after),
            };
            if at.get(&s) != Some(&merged) {
                at.insert(s, merged);
                work.push(s);
            }
        }
    }
    at
}

/// Infer a partition for a function whose writer gave none (v1 decision 5).
///
/// - Save slots: aligned 8-byte offsets every `sd` to which stores the entry
///   value of one saved register (the first such slot per register).
/// - Address-taken ranges start where `addi rd, sp, k` points. A range's
///   length is the variable's size from `dwarf` (frame offset to size) when
///   the debug information has it; otherwise it runs to the next taken
///   address, the next save slot or the end of the frame, so the fields of a
///   struct or the rest of an array that the code also touches with `ld`/`sd`
///   stay in the range a callee may be given.
/// - Other accessed bytes: the remaining aligned 8-byte `ld`/`sd` offsets are
///   spill slots; any other access gets a range of its own up to the next slot.
pub fn infer(
    f: &Func,
    flows: &BTreeMap<u64, Flow>,
    offs: &BTreeMap<u64, i64>,
    frame: u64,
    dwarf: Option<&BTreeMap<u64, u64>>,
) -> Partition {
    let mut seeds: BTreeSet<u64> = BTreeSet::new();
    let mut other: Vec<(u64, u64)> = Vec::new();
    let mut cands: BTreeSet<u64> = BTreeSet::new();
    for (&pc, &off) in offs {
        let Some(i) = f.instr(pc) else { continue };
        if let Some(t) = taken(&i, off, frame) {
            if t >= 0 && (t as u64) < frame {
                seeds.insert(t as u64);
            }
        }
        if let Some(a) = access(&i, off, frame) {
            if a.fo < 0 || a.fo as u64 + a.w > frame {
                continue;
            }
            let fo = a.fo as u64;
            if a.ldsd && fo % 8 == 0 {
                cands.insert(fo);
            } else {
                other.push((fo, a.w));
            }
        }
    }
    // Save slots, from what each sd stores (every candidate a spill for now).
    let spills = Partition {
        slots: cands
            .iter()
            .map(|&off| Slot {
                off,
                kind: SlotKind::Spill,
            })
            .collect(),
        ranges: vec![],
    };
    let mut stores: BTreeMap<u64, Vec<(u64, Reg, bool)>> = BTreeMap::new();
    facts(f, flows, offs, frame, &spills, &mut |pc, fo, r, e| {
        stores.entry(fo).or_default().push((pc, r, e));
    });
    let mut first_save: BTreeMap<u8, (u64, u64)> = BTreeMap::new(); // reg -> (pc, slot)
    for (&fo, ss) in &stores {
        let r = ss[0].1;
        if !seeds.contains(&fo) && saved(r) && ss.iter().all(|&(_, q, e)| q == r && e) {
            let pc = ss.iter().map(|s| s.0).min().unwrap();
            let e = first_save.entry(r.0).or_insert((pc, fo));
            if pc < e.0 {
                *e = (pc, fo);
            }
        }
    }
    let saves: BTreeMap<u64, Reg> = first_save
        .iter()
        .map(|(&r, &(_, fo))| (fo, Reg(r)))
        .collect();
    // Ranges from the taken addresses.
    let mut ranges: Vec<Range> = Vec::new();
    for &s in &seeds {
        let bound = [
            seeds.range(s + 1..).next().copied(),
            saves.range(s + 1..).next().map(|(&k, _)| k),
            Some(frame),
        ]
        .into_iter()
        .flatten()
        .min()
        .unwrap();
        let (len, source) = match dwarf.and_then(|d| d.get(&s)) {
            Some(&len) => (len.min(frame - s), RangeSource::Dwarf),
            None => (bound - s, RangeSource::Heuristic),
        };
        if len > 0 {
            ranges.push(Range {
                off: s,
                len,
                source,
            });
        }
    }
    let in_range = |ranges: &[Range], fo: u64, w: u64| {
        ranges.iter().any(|r| fo < r.off + r.len && r.off < fo + w)
    };
    // Slots: save slots and the other aligned ld/sd offsets outside ranges.
    let slots: Vec<Slot> = cands
        .iter()
        .filter(|&&fo| !in_range(&ranges, fo, 8))
        .map(|&off| Slot {
            off,
            kind: saves
                .get(&off)
                .map_or(SlotKind::Spill, |&r| SlotKind::Save(r)),
        })
        .collect();
    // Accesses of other widths outside every range: a range up to the next slot.
    other.sort();
    for (fo, w) in other {
        let touches = |a: u64, b: u64| slots.iter().any(|s| a < s.off + 8 && s.off < b);
        if ranges
            .iter()
            .any(|r| r.off <= fo && fo + w <= r.off + r.len)
            || touches(fo, fo + w)
        {
            // In a range already; or it touches a slot, which is 6c's to report.
            continue;
        }
        let next = slots
            .iter()
            .map(|s| s.off)
            .filter(|&o| o > fo)
            .min()
            .unwrap_or(frame)
            .max(fo + w);
        let next = ranges
            .iter()
            .map(|r| r.off)
            .filter(|&o| o > fo)
            .fold(next, u64::min)
            .max(fo + w);
        if !in_range(&ranges, fo, next - fo) && !touches(fo, next) {
            ranges.push(Range {
                off: fo,
                len: next - fo,
                source: RangeSource::Heuristic,
            });
        }
    }
    ranges.sort();
    Partition { slots, ranges }
}

/// One fact of the certificate `lean/NoCompiler/Frame.lean` checks: before
/// an instruction, `sp` is `depth` bytes below its entry value, the saved
/// registers in `keep` hold their entry value, and each `(k, r)` in `held` is
/// a slot at frame offset `k` holding the entry value of `r`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertFact {
    pub depth: u64,
    pub keep: Vec<u8>,
    pub held: Vec<(u64, u8)>,
}

/// The certificate: the fact before every instruction (the entry fact for an
/// instruction no path reaches).
pub fn certificate(
    f: &Func,
    flows: &BTreeMap<u64, Flow>,
    offs: &BTreeMap<u64, i64>,
    frame: u64,
    part: &Partition,
) -> Vec<CertFact> {
    let at = facts(f, flows, offs, frame, part, &mut |_, _, _, _| {});
    (0..f.words.len() as u64)
        .map(|i| f.entry + 4 * i)
        .map(|pc| match (at.get(&pc), offs.get(&pc)) {
            (Some(fact), Some(&off)) => CertFact {
                depth: (-off) as u64,
                keep: fact.keep.iter().copied().collect(),
                held: fact.slots.iter().map(|(&k, r)| (k, r.0)).collect(),
            },
            _ => CertFact {
                depth: 0,
                keep: SAVED.to_vec(),
                held: vec![],
            },
        })
        .collect()
}

/// R6 (6a to 6e) and the `ra` part of R4, against a partition. `offs` are
/// R5's offsets (every reachable instruction), `frame` the frame size.
pub fn check(
    f: &Func,
    flows: &BTreeMap<u64, Flow>,
    offs: &BTreeMap<u64, i64>,
    frame: u64,
    part: &Partition,
) -> Vec<Violation> {
    let mut out = Vec::new();
    // 6b: the partition itself.
    let mut spans: Vec<(u64, u64, String)> = Vec::new();
    let mut saves: BTreeMap<u8, u64> = BTreeMap::new();
    for s in &part.slots {
        if s.off % 8 != 0 || s.off + 8 > frame {
            out.push(v(
                f.entry,
                "R6b partition",
                format!(
                    "slot at {} is not an aligned 8 bytes inside the {frame}-byte frame",
                    s.off
                ),
            ));
        }
        if let SlotKind::Save(r) = s.kind {
            if !saved(r) {
                out.push(v(
                    f.entry,
                    "R6b partition",
                    format!("slot at {} saves {r}, which is not ra or s0 to s11", s.off),
                ));
            }
            if saves.insert(r.0, s.off).is_some() {
                out.push(v(
                    f.entry,
                    "R6b partition",
                    format!("two save slots for {r}"),
                ));
            }
        }
        spans.push((s.off, s.off + 8, format!("slot at {}", s.off)));
    }
    for r in &part.ranges {
        if r.len == 0 || r.off + r.len > frame {
            out.push(v(
                f.entry,
                "R6b partition",
                format!(
                    "range [{}, {}) is not inside the {frame}-byte frame",
                    r.off,
                    r.off + r.len
                ),
            ));
        }
        spans.push((r.off, r.off + r.len, format!("range at {}", r.off)));
    }
    spans.sort();
    for w in spans.windows(2) {
        if w[1].0 < w[0].1 {
            out.push(v(
                f.entry,
                "R6b partition",
                format!("{} overlaps {}", w[0].2, w[1].2),
            ));
        }
    }
    // 6a, 6c, 6d and R4's ra, instruction by instruction.
    let calls = flows.values().any(|fl| matches!(fl, Flow::Call(_)));
    for (&pc, &off) in offs {
        let Some(i) = f.instr(pc) else { continue };
        if !sp_form_ok(&i) {
            out.push(v(
                pc,
                "R6a sp",
                "sp used other than as addi sp, sp, k, a load/store base, or addi rd, sp, k",
            ));
        }
        if let Some(a) = access(&i, off, frame) {
            let kind = if a.ldsd { "ld/sd" } else { "access" };
            if a.fo < 0 || a.fo as u64 + a.w > frame {
                out.push(v(
                    pc,
                    "R6c sp access",
                    format!(
                        "{}-byte {kind} at frame offset {} is outside the {frame}-byte frame",
                        a.w, a.fo
                    ),
                ));
            } else {
                let fo = a.fo as u64;
                let slot = part.slot_at(fo);
                let ok = (a.ldsd && slot.is_some()) || part.range_of(fo, a.w).is_some();
                if !ok {
                    let what = match part
                        .slots
                        .iter()
                        .find(|s| fo < s.off + 8 && s.off < fo + a.w)
                    {
                        Some(s) => format!(
                            "touches the slot at {} other than by ld/sd at its offset",
                            s.off
                        ),
                        None => "is in no slot and no single range".into(),
                    };
                    out.push(v(
                        pc,
                        "R6c sp access",
                        format!("{}-byte {kind} at frame offset {fo} {what}", a.w),
                    ));
                }
            }
        }
        if let Some(t) = taken(&i, off, frame) {
            let ok = t >= 0
                && part
                    .ranges
                    .iter()
                    .any(|r| r.off as i64 <= t && t <= (r.off + r.len) as i64);
            if !ok {
                let what = match part
                    .slots
                    .iter()
                    .find(|s| t >= s.off as i64 && t < (s.off + 8) as i64)
                {
                    Some(s) => format!("the address of the slot at {}", s.off),
                    None => "an address in no range".into(),
                };
                out.push(v(
                    pc,
                    "R6d address",
                    format!("addi takes {what} (frame offset {t})"),
                ));
            }
        }
        if i.dest() == Some(isa::RA) {
            let fl = flows.get(&pc).copied();
            let call_half = matches!(fl, Some(Flow::Call(_)))
                || (matches!(i, Instr::Auipc(..))
                    && matches!(flows.get(&(pc + 4)), Some(Flow::Call(_))));
            let from_slot = matches!(i, Instr::Load(isa::LdOp::Ld, _, isa::SP, _))
                && access(&i, off, frame).is_some_and(|a| {
                    a.fo >= 0
                        && part
                            .save_slot(isa::RA)
                            .is_some_and(|s| s.off == a.fo as u64)
                });
            if !call_half && !from_slot {
                out.push(v(
                    pc,
                    "R4 registers",
                    "ra written other than by a call or a reload from its save slot",
                ));
            }
        }
    }
    // 6e: a save slot for every saved register the function writes (ra if it
    // calls); entry values back at every return and tail call.
    let mut written: BTreeSet<u8> = BTreeSet::new();
    for &pc in offs.keys() {
        if let Some(rd) = f.instr(pc).and_then(|i| i.dest()) {
            if saved(rd) && rd != isa::RA {
                written.insert(rd.0);
            }
        }
    }
    if calls {
        written.insert(isa::RA.0);
    }
    for &r in &written {
        if part.save_slot(Reg(r)).is_none() {
            out.push(v(
                f.entry,
                "R6e save",
                format!("writes {} but has no save slot for it", Reg(r)),
            ));
        }
    }
    let mut bad_saves = Vec::new();
    let at = facts(f, flows, offs, frame, part, &mut |pc, fo, r, e| {
        if let Some(Slot {
            kind: SlotKind::Save(q),
            ..
        }) = part.slot_at(fo)
        {
            if *q != r || !e {
                bad_saves.push((pc, fo, *q, r));
            }
        }
    });
    bad_saves.sort();
    bad_saves.dedup();
    for (pc, fo, q, r) in bad_saves {
        out.push(v(
            pc,
            "R6e save",
            format!("writes the save slot of {q} (at {fo}) with {r}, not {q}'s entry value"),
        ));
    }
    for (&pc, &fl) in flows {
        if !matches!(fl, Flow::Ret | Flow::Tail(_)) {
            continue;
        }
        let Some(fact) = at.get(&pc) else { continue };
        let lost: Vec<String> = SAVED
            .iter()
            .filter(|r| !fact.keep.contains(r))
            .map(|&r| Reg(r).to_string())
            .collect();
        if !lost.is_empty() {
            let how = if matches!(fl, Flow::Ret) {
                "returns"
            } else {
                "tail-calls"
            };
            out.push(v(
                pc,
                "R6e save",
                format!("{how} without the entry value of {}", lost.join(", ")),
            ));
        }
    }
    out
}
