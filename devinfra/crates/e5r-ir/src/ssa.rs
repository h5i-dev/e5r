//! Static single assignment form, and the dataflow that needs it.
//!
//! Every value gets one definition, so "where did this come from" is a lookup
//! rather than a search. That is what makes constant propagation, dead code
//! elimination and eventually expression rebuilding tractable.
//!
//! The complication is that machine registers overlap: `w0` is the low half of
//! `x0`, and a naive renaming would treat them as unrelated and lose the
//! dependency. Locations are therefore canonical whole registers, and a narrow
//! access is made explicit: a narrow read becomes a `SubPiece` of the whole
//! register, and a narrow write becomes a masked merge with it. After that
//! every definition covers a whole location and the renaming is ordinary.

use std::collections::{BTreeMap, BTreeSet};

use e5r_core::Addr;

use crate::func::Function;
use crate::op::{IrOp, Op, Space, Varnode};

/// A storage location, at the granularity SSA versions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Location {
    /// Which space.
    pub space: Space,
    /// The canonical offset: the start of the whole register or temporary.
    pub offset: u64,
    /// The whole location's size.
    pub size: u8,
}

/// The canonical location a varnode touches, or `None` for constants and
/// memory, which are not versioned.
///
/// Registers are canonicalized to eight-byte boundaries, which is how the
/// AArch64 register file is laid out and what makes `w0` and `x0` one location.
/// The one-byte flags sit above the registers and are their own locations.
pub fn location(v: Varnode) -> Option<Location> {
    match v.space {
        Space::Const | Space::Ram => None,
        Space::Unique | Space::Stack => Some(Location {
            space: v.space,
            offset: v.offset,
            size: v.size,
        }),
        Space::Register => {
            // The flags are single bytes and are not part of an eight-byte
            // register; anything a byte wide is treated as its own location.
            if v.size == 1 {
                return Some(Location {
                    space: Space::Register,
                    offset: v.offset,
                    size: 1,
                });
            }
            // An access that crosses an eight-byte boundary is not one
            // location, and pretending it is would let a write to the upper
            // half clobber the lower. Such an access has no canonical location
            // and the builder treats it as opaque.
            if v.offset % 8 + v.size as u64 > 8 {
                return None;
            }
            Some(Location {
                space: Space::Register,
                offset: v.offset & !7,
                size: 8,
            })
        }
    }
}

impl Location {
    /// The varnode naming the whole location.
    pub fn whole(self) -> Varnode {
        Varnode {
            space: self.space,
            offset: self.offset,
            size: self.size,
        }
    }
}

/// A versioned value: a location and which definition of it this is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Value {
    /// Which location.
    pub location: Location,
    /// Which definition, counting from zero at the function's entry.
    pub version: u32,
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let space = match self.location.space {
            Space::Register => "r",
            Space::Unique => "u",
            Space::Ram => "m",
            Space::Const => "c",
            Space::Stack => "s",
        };
        write!(f, "{space}{:x}_{}", self.location.offset, self.version)
    }
}

/// One operation in SSA form.
#[derive(Debug, Clone)]
pub struct SsaOp {
    /// The machine address it came from.
    pub addr: Addr,
    /// Which operation, or a phi.
    pub kind: SsaKind,
    /// Where the result goes.
    pub out: Option<Value>,
    /// The inputs, each either a versioned value or a constant.
    pub inputs: Vec<Operand>,
    /// The size the operation works at, in bytes.
    pub size: u8,
}

/// A phi or an ordinary operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SsaKind {
    /// A merge of one value per incoming edge.
    Phi,
    /// An ordinary IR operation.
    Op(Op),
}

/// An SSA operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Operand {
    /// A versioned value.
    Value(Value),
    /// A literal.
    Const(u64, u8),
    /// A location nothing in this function defined: an argument, or memory.
    Undefined(Location),
}

impl Operand {
    /// The width of an operand in bytes.
    pub fn size(self) -> u8 {
        match self {
            Operand::Const(_, size) => size,
            Operand::Value(v) => v.location.size,
            Operand::Undefined(l) => l.size,
        }
    }

    /// The literal, if this is one.
    pub fn as_const(self) -> Option<u64> {
        match self {
            Operand::Const(v, _) => Some(v),
            _ => None,
        }
    }

    /// The value, if this is one.
    pub fn as_value(self) -> Option<Value> {
        match self {
            Operand::Value(v) => Some(v),
            _ => None,
        }
    }
}

impl std::fmt::Display for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operand::Value(v) => write!(f, "{v}"),
            Operand::Const(v, _) => write!(f, "{v:#x}"),
            Operand::Undefined(l) => write!(f, "{}_in", l.whole()),
        }
    }
}

/// One block in SSA form.
#[derive(Debug, Clone, Default)]
pub struct SsaBlock {
    /// The operations, phis first.
    pub ops: Vec<SsaOp>,
    /// Successors, in the order the phis expect their inputs.
    pub successors: Vec<Addr>,
    /// Predecessors, in the order the phis take their inputs.
    pub predecessors: Vec<Addr>,
}

/// A function in SSA form.
#[derive(Debug, Clone)]
pub struct SsaFunction {
    /// Which architecture the code came from.
    pub arch: e5r_core::Arch,
    /// Where it starts.
    pub entry: Addr,
    /// Blocks by start address.
    pub blocks: BTreeMap<Addr, SsaBlock>,
}

impl SsaFunction {
    /// How many operations there are.
    pub fn op_count(&self) -> usize {
        self.blocks.values().map(|b| b.ops.len()).sum()
    }

    /// How many phis were needed.
    pub fn phi_count(&self) -> usize {
        self.blocks
            .values()
            .flat_map(|b| b.ops.iter())
            .filter(|o| o.kind == SsaKind::Phi)
            .count()
    }

    /// The single definition of each value.
    pub fn definitions(&self) -> BTreeMap<Value, (Addr, usize)> {
        let mut out = BTreeMap::new();
        for (addr, b) in &self.blocks {
            for (i, op) in b.ops.iter().enumerate() {
                if let Some(v) = op.out {
                    out.insert(v, (*addr, i));
                }
            }
        }
        out
    }
}

/// Immediate dominators, by the iterative algorithm.
///
/// Chosen over Lengauer-Tarjan because it is twenty lines, its correctness is
/// visible, and the functions here have hundreds of blocks rather than
/// millions.
fn dominators(f: &Function, order: &[Addr]) -> BTreeMap<Addr, Addr> {
    let index: BTreeMap<Addr, usize> = order.iter().enumerate().map(|(i, a)| (*a, i)).collect();
    let mut idom: BTreeMap<Addr, Addr> = BTreeMap::new();
    idom.insert(f.entry, f.entry);

    let mut changed = true;
    let mut rounds = 0;
    while changed && rounds < 1000 {
        changed = false;
        rounds += 1;
        for at in order.iter().skip(1) {
            let Some(b) = f.blocks.get(at) else { continue };
            let mut new: Option<Addr> = None;
            for p in &b.predecessors {
                if !idom.contains_key(p) {
                    continue;
                }
                new = Some(match new {
                    None => *p,
                    Some(cur) => intersect(&idom, &index, cur, *p),
                });
            }
            if let Some(n) = new {
                if idom.get(at) != Some(&n) {
                    idom.insert(*at, n);
                    changed = true;
                }
            }
        }
    }
    idom
}

/// Walk up the dominator tree until two blocks meet.
fn intersect(
    idom: &BTreeMap<Addr, Addr>,
    index: &BTreeMap<Addr, usize>,
    mut a: Addr,
    mut b: Addr,
) -> Addr {
    let mut guard = 0;
    while a != b && guard < 10_000 {
        guard += 1;
        let (ia, ib) = (
            index.get(&a).copied().unwrap_or(0),
            index.get(&b).copied().unwrap_or(0),
        );
        if ia > ib {
            a = idom.get(&a).copied().unwrap_or(a);
        } else {
            b = idom.get(&b).copied().unwrap_or(b);
        }
        if idom.get(&a) == Some(&a) && idom.get(&b) == Some(&b) && a != b {
            break;
        }
    }
    a
}

/// Dominance frontiers, which is where phis go.
fn frontiers(f: &Function, idom: &BTreeMap<Addr, Addr>) -> BTreeMap<Addr, BTreeSet<Addr>> {
    let mut df: BTreeMap<Addr, BTreeSet<Addr>> = BTreeMap::new();
    for (at, b) in &f.blocks {
        if b.predecessors.len() < 2 {
            continue;
        }
        for p in &b.predecessors {
            let mut runner = *p;
            let mut guard = 0;
            while runner != idom.get(at).copied().unwrap_or(*at) && guard < 10_000 {
                guard += 1;
                df.entry(runner).or_default().insert(*at);
                let next = idom.get(&runner).copied().unwrap_or(runner);
                if next == runner {
                    break;
                }
                runner = next;
            }
        }
    }
    df
}

/// Convert a function to SSA form.
pub fn build(f: &Function) -> SsaFunction {
    let order = f.reverse_postorder();
    let idom = dominators(f, &order);
    let df = frontiers(f, &idom);

    // Which locations each block defines, and which are defined anywhere.
    let mut defined_in: BTreeMap<Addr, BTreeSet<Location>> = BTreeMap::new();
    let mut all: BTreeSet<Location> = BTreeSet::new();
    for (at, b) in &f.blocks {
        let set = defined_in.entry(*at).or_default();
        for op in &b.ops {
            if let Some(l) = op.out.and_then(location) {
                set.insert(l);
                all.insert(l);
            }
        }
    }

    // Phi placement: the iterated dominance frontier of each location's
    // definition sites.
    let mut phis: BTreeMap<Addr, BTreeSet<Location>> = BTreeMap::new();
    for loc in &all {
        let mut work: Vec<Addr> = defined_in
            .iter()
            .filter(|(_, s)| s.contains(loc))
            .map(|(a, _)| *a)
            .collect();
        let mut placed: BTreeSet<Addr> = BTreeSet::new();
        while let Some(at) = work.pop() {
            for target in df.get(&at).into_iter().flatten() {
                if placed.insert(*target) {
                    phis.entry(*target).or_default().insert(*loc);
                    work.push(*target);
                }
            }
        }
    }

    // Renaming, walking the dominator tree so each block starts from the
    // versions its dominator ended with.
    let children = dominator_children(&idom, f.entry);
    let mut counters: BTreeMap<Location, u32> = BTreeMap::new();
    let mut out: BTreeMap<Addr, SsaBlock> = BTreeMap::new();
    let mut incoming: BTreeMap<Addr, BTreeMap<Location, Operand>> = BTreeMap::new();
    incoming.insert(f.entry, BTreeMap::new());
    // What reaches the end of each block, for filling the phis. Not the same
    // as what the block defines: a location a block never touches still has a
    // value there, inherited from the block that dominates it, and a phi
    // reading only the predecessor's own definitions loses it.
    let mut exit_state: BTreeMap<Addr, BTreeMap<Location, Operand>> = BTreeMap::new();

    // Explicit stack rather than recursion.
    let mut stack = vec![f.entry];
    let mut visited: BTreeSet<Addr> = BTreeSet::new();
    while let Some(at) = stack.pop() {
        if !visited.insert(at) {
            continue;
        }
        let Some(block) = f.blocks.get(&at) else {
            continue;
        };
        let mut current = incoming.get(&at).cloned().unwrap_or_default();
        let mut ops: Vec<SsaOp> = Vec::new();

        // Phis first, one per location that needs one here.
        for loc in phis.get(&at).into_iter().flatten() {
            let version = bump(&mut counters, *loc);
            let value = Value {
                location: *loc,
                version,
            };
            ops.push(SsaOp {
                addr: at,
                kind: SsaKind::Phi,
                out: Some(value),
                // Filled in once every predecessor has been renamed.
                inputs: Vec::new(),
                size: loc.size,
            });
            current.insert(*loc, Operand::Value(value));
        }

        for op in &block.ops {
            let (converted, updates) = convert(op, &current, &mut counters);
            ops.extend(converted);
            for (l, v) in updates {
                current.insert(l, v);
            }
        }

        out.insert(
            at,
            SsaBlock {
                ops,
                successors: block.successors.clone(),
                predecessors: block.predecessors.clone(),
            },
        );
        exit_state.insert(at, current.clone());

        // Every successor inherits this block's final versions for its phis,
        // and every dominator child inherits them wholesale.
        for s in &block.successors {
            incoming.entry(*s).or_default();
            let entry = incoming.get_mut(s).unwrap();
            for (l, v) in &current {
                entry.entry(*l).or_insert(*v);
            }
        }
        for c in children.get(&at).into_iter().flatten() {
            incoming.insert(*c, current.clone());
            stack.push(*c);
        }
        // Blocks the dominator tree does not reach from here still need doing.
        for s in &block.successors {
            if !visited.contains(s) && f.blocks.contains_key(s) {
                stack.push(*s);
            }
        }
    }

    // Fill the phi inputs, one per predecessor in order.
    let final_versions = exit_state;
    for (at, b) in out.iter_mut() {
        let preds = b.predecessors.clone();
        for op in b.ops.iter_mut() {
            if op.kind != SsaKind::Phi {
                continue;
            }
            let Some(v) = op.out else { continue };
            op.inputs = preds
                .iter()
                .map(|p| {
                    final_versions
                        .get(p)
                        .and_then(|m| m.get(&v.location))
                        .copied()
                        .unwrap_or(Operand::Undefined(v.location))
                })
                .collect();
            let _ = at;
        }
    }

    SsaFunction {
        arch: f.arch.clone(),
        entry: f.entry,
        blocks: out,
    }
}

fn bump(counters: &mut BTreeMap<Location, u32>, loc: Location) -> u32 {
    let c = counters.entry(loc).or_insert(0);
    let v = *c;
    *c += 1;
    v
}

/// The blocks each block immediately dominates.
fn dominator_children(idom: &BTreeMap<Addr, Addr>, entry: Addr) -> BTreeMap<Addr, Vec<Addr>> {
    let mut out: BTreeMap<Addr, Vec<Addr>> = BTreeMap::new();
    for (block, parent) in idom {
        if *block == entry || block == parent {
            continue;
        }
        out.entry(*parent).or_default().push(*block);
    }
    out
}

/// Convert one IR operation, making narrow accesses explicit.
///
/// Returns the operations to emit and the location versions they define.
fn convert(
    op: &IrOp,
    current: &BTreeMap<Location, Operand>,
    counters: &mut BTreeMap<Location, u32>,
) -> (Vec<SsaOp>, Vec<(Location, Operand)>) {
    let mut emitted = Vec::new();
    let mut updates = Vec::new();
    let mut extra_temp = 0u64;

    // Read each input, extracting from the whole location when the access is
    // narrower than it.
    let mut inputs = Vec::new();
    for v in op.inputs() {
        inputs.push(read(
            *v,
            current,
            counters,
            &mut emitted,
            &mut updates,
            op.addr,
            &mut extra_temp,
        ));
    }

    // A memory address is an input; a load's size comes from its output.
    let size = op
        .out
        .map(|o| o.size)
        .or_else(|| op.input(0).map(|i| i.size))
        .unwrap_or(8);

    match op.out.and_then(|o| location(o).map(|l| (o, l))) {
        // A write that covers the whole location: an ordinary definition.
        Some((o, loc)) if o.size == loc.size && o.offset == loc.offset => {
            let version = bump(counters, loc);
            let value = Value {
                location: loc,
                version,
            };
            emitted.push(SsaOp {
                addr: op.addr,
                kind: SsaKind::Op(op.op),
                out: Some(value),
                inputs,
                size,
            });
            updates.push((loc, Operand::Value(value)));
        }
        // A narrow write: compute into a temporary, then merge it with the old
        // whole value. Making this explicit is what keeps the dependency on the
        // untouched bits visible to dataflow.
        Some((o, loc)) => {
            let temp_loc = Location {
                space: Space::Unique,
                offset: 1 << 40 | o.offset << 8 | extra_temp,
                size: o.size,
            };
            extra_temp += 1;
            let tv = Value {
                location: temp_loc,
                version: bump(counters, temp_loc),
            };
            emitted.push(SsaOp {
                addr: op.addr,
                kind: SsaKind::Op(op.op),
                out: Some(tv),
                inputs,
                size,
            });

            let old = current
                .get(&loc)
                .copied()
                .unwrap_or(Operand::Undefined(loc));
            let shift = (o.offset - loc.offset) * 8;
            let field = if o.size as u64 * 8 >= 64 {
                u64::MAX
            } else {
                ((1u64 << (o.size as u32 * 8)) - 1) << shift
            };

            // old & !field
            let cleared_loc = Location {
                space: Space::Unique,
                offset: 1 << 41 | o.offset << 8 | extra_temp,
                size: loc.size,
            };
            extra_temp += 1;
            let cleared = Value {
                location: cleared_loc,
                version: bump(counters, cleared_loc),
            };
            emitted.push(SsaOp {
                addr: op.addr,
                kind: SsaKind::Op(Op::IntAnd),
                out: Some(cleared),
                inputs: vec![old, Operand::Const(!field, loc.size)],
                size: loc.size,
            });

            // widen(temp) << shift
            let widened_loc = Location {
                space: Space::Unique,
                offset: 1 << 42 | o.offset << 8 | extra_temp,
                size: loc.size,
            };
            extra_temp += 1;
            let widened = Value {
                location: widened_loc,
                version: bump(counters, widened_loc),
            };
            emitted.push(SsaOp {
                addr: op.addr,
                kind: SsaKind::Op(Op::IntZExt),
                out: Some(widened),
                inputs: vec![Operand::Value(tv)],
                size: loc.size,
            });
            let placed = if shift == 0 {
                widened
            } else {
                let placed_loc = Location {
                    space: Space::Unique,
                    offset: 1 << 43 | o.offset << 8 | extra_temp,
                    size: loc.size,
                };
                let p = Value {
                    location: placed_loc,
                    version: bump(counters, placed_loc),
                };
                emitted.push(SsaOp {
                    addr: op.addr,
                    kind: SsaKind::Op(Op::IntLeft),
                    out: Some(p),
                    inputs: vec![Operand::Value(widened), Operand::Const(shift, 1)],
                    size: loc.size,
                });
                p
            };
            // extra_temp is not read again in this arm; the merge below needs
            // no further temporaries.
            let _ = extra_temp;

            let version = bump(counters, loc);
            let merged = Value {
                location: loc,
                version,
            };
            emitted.push(SsaOp {
                addr: op.addr,
                kind: SsaKind::Op(Op::IntOr),
                out: Some(merged),
                inputs: vec![Operand::Value(cleared), Operand::Value(placed)],
                size: loc.size,
            });
            updates.push((loc, Operand::Value(merged)));
        }
        // No output, or an output in memory: emitted as it is.
        None => {
            emitted.push(SsaOp {
                addr: op.addr,
                kind: SsaKind::Op(op.op),
                out: None,
                inputs,
                size,
            });
        }
    }

    (emitted, updates)
}

/// Read a varnode, extracting from its whole location when it is narrower.
#[allow(clippy::too_many_arguments)]
fn read(
    v: Varnode,
    current: &BTreeMap<Location, Operand>,
    counters: &mut BTreeMap<Location, u32>,
    emitted: &mut Vec<SsaOp>,
    _updates: &mut Vec<(Location, Operand)>,
    addr: Addr,
    extra_temp: &mut u64,
) -> Operand {
    if v.space == Space::Const {
        return Operand::Const(v.offset, v.size);
    }
    let Some(loc) = location(v) else {
        // Memory: not versioned, so it reads as undefined storage.
        return Operand::Undefined(Location {
            space: Space::Ram,
            offset: v.offset,
            size: v.size,
        });
    };
    let whole = current
        .get(&loc)
        .copied()
        .unwrap_or(Operand::Undefined(loc));
    if v.size == loc.size && v.offset == loc.offset {
        return whole;
    }
    // Narrower than the location: extract the bytes.
    let shift = v.offset - loc.offset;
    let out_loc = Location {
        space: Space::Unique,
        offset: 1 << 44 | v.offset << 8 | *extra_temp,
        size: v.size,
    };
    *extra_temp += 1;
    let out = Value {
        location: out_loc,
        version: bump(counters, out_loc),
    };
    emitted.push(SsaOp {
        addr,
        kind: SsaKind::Op(Op::SubPiece),
        out: Some(out),
        inputs: vec![whole, Operand::Const(shift, 1)],
        size: v.size,
    });
    Operand::Value(out)
}
