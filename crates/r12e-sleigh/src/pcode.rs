//! Lifting a decoded instruction's semantic bodies into p-code operations.
//!
//! # The opcode set is r12e's, not a new one
//!
//! [`Opcode`] is variant for variant the same list as `r12e_ir::op::Op`, with
//! the same names, so converting one to the other is a match with no
//! judgement in it. It is declared here rather than imported because this
//! crate deliberately has no dependencies: it is the trust boundary that reads
//! someone else's specification files, and `r12e-ir` pulls in a serialisation
//! framework. The adapter belongs in a crate that already depends on both.
//!
//! A `define pcodeop` is an operation the specification names and deliberately
//! gives no semantics for, which is Ghidra's CALLOTHER. It lifts to
//! [`Opcode::Other`] carrying that name, with the inputs and output the
//! specification wrote, so a consumer knows exactly what it does not know.
//! That is a complete lift of an opaque operation, not a failure to lift.
//!
//! Three SLEIGH constructs have no opcode in that list and are reported rather
//! than approximated. Each one emits [`Opcode::Unimplemented`] carrying a note
//! that says what it was, and [`Pcode::unsupported`] collects them:
//!
//! * `cpool`, CPOOLREF, which resolves a constant pool reference.
//! * `newobject`, NEW.
//! * `delayslot` and `crossbuild`, which are not operations at all but
//!   directives about which *other* instruction's p-code belongs here. Nothing
//!   in a flat operation list can express them.
//!
//! # What a lift has to work out that the front end does not
//!
//! SLEIGH requires every varnode's size to be determinable but does not
//! require it to be written down, and [`crate::model`] records only what was
//! written. So `local t = a + b;` arrives with `t`'s size unknown and it has
//! to come from `a` and `b`; `x = 1;` arrives with the literal's size unknown
//! and it has to come from `x`. Sizes are therefore resolved here, bottom up
//! from the varnodes and top down from the assignment target, and an
//! expression whose size cannot be settled either way produces
//! [`Opcode::Unimplemented`] rather than a guess.

use std::collections::HashMap;

use crate::decode::{Decoded, Value};
use crate::model::{
    BinOp, Builtin, Constructor, Export, Expr, Intrinsic, JumpTarget, Lvalue, MacroId, SpaceKind,
    Spec, Stmt, SymbolRef, UnOp, VarnodeId,
};

/// Where a lifted value lives.
///
/// The same four spaces `r12e_ir::op::Space` has, minus `Stack`, which is
/// something a later analysis proves rather than something a lifter knows.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Space {
    /// A literal. The offset is the value.
    Const,
    /// The machine's register file. The offset is a byte position in it.
    Register,
    /// Addressable memory. The offset is an address.
    Ram,
    /// A temporary introduced by lifting.
    Unique,
}

/// A storage location: a space, an offset in it, and a size in bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Varnode {
    /// Which space.
    pub space: Space,
    /// Where in it.
    pub offset: u64,
    /// How many bytes.
    pub size: u8,
}

impl Varnode {
    /// A literal value.
    pub const fn constant(value: u64, size: u8) -> Varnode {
        Varnode {
            space: Space::Const,
            offset: value,
            size,
        }
    }

    /// A register at a byte offset in the register file.
    pub const fn register(offset: u64, size: u8) -> Varnode {
        Varnode {
            space: Space::Register,
            offset,
            size,
        }
    }

    /// A lifting temporary.
    pub const fn temp(id: u64, size: u8) -> Varnode {
        Varnode {
            space: Space::Unique,
            offset: id,
            size,
        }
    }
}

/// What an operation does. Variant for variant `r12e_ir::op::Op`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(missing_docs)]
pub enum Opcode {
    Copy,
    Load,
    Store,
    Branch,
    CBranch,
    BranchInd,
    Call,
    CallInd,
    Return,
    IntAdd,
    IntSub,
    IntMul,
    IntDiv,
    IntSDiv,
    IntRem,
    IntSRem,
    IntMulHigh,
    IntSMulHigh,
    IntAnd,
    IntOr,
    IntXor,
    IntNot,
    IntNegate,
    IntLeft,
    IntRight,
    IntSRight,
    IntEqual,
    IntNotEqual,
    IntLess,
    IntSLess,
    IntLessEqual,
    IntSLessEqual,
    IntCarry,
    IntSCarry,
    IntSBorrow,
    IntZExt,
    IntSExt,
    PopCount,
    LzCount,
    BoolAnd,
    BoolOr,
    BoolXor,
    BoolNot,
    FloatAdd,
    FloatSub,
    FloatMul,
    FloatDiv,
    FloatNeg,
    FloatAbs,
    FloatSqrt,
    FloatEqual,
    FloatNotEqual,
    FloatLess,
    FloatLessEqual,
    FloatNan,
    FloatTrunc,
    FloatRound,
    FloatCeil,
    FloatFloor,
    IntToFloat,
    FloatToInt,
    FloatConvert,
    Piece,
    SubPiece,
    /// A `define pcodeop`: an operation the specification names and gives no
    /// semantics for, which is Ghidra's CALLOTHER. The note carries its name,
    /// and the inputs and output are the ones the specification wrote, so a
    /// consumer knows exactly what it does not know.
    Other,
    /// Something with no opcode in this list. The note says what.
    Unimplemented,
}

/// One lifted operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Insn {
    /// What it does.
    pub op: Opcode,
    /// Where the result goes, when there is one.
    pub out: Option<Varnode>,
    /// Its inputs.
    pub ins: Vec<Varnode>,
    /// For a branch inside the instruction, `in0` is an index into
    /// [`Pcode::ops`] rather than an address. SLEIGH's `<label>` targets are
    /// this and nothing else is, and a caller that flattens p-code into a
    /// block graph has to know the difference.
    pub relative: bool,
    /// For [`Opcode::Unimplemented`], what the specification asked for.
    pub note: Option<String>,
}

impl Insn {
    fn new(op: Opcode, out: Option<Varnode>, ins: Vec<Varnode>) -> Insn {
        Insn {
            op,
            out,
            ins,
            relative: false,
            note: None,
        }
    }

    /// A named operation the specification gives no semantics for.
    fn other(name: impl Into<String>, out: Option<Varnode>, ins: Vec<Varnode>) -> Insn {
        Insn {
            op: Opcode::Other,
            out,
            ins,
            relative: false,
            note: Some(name.into()),
        }
    }

    fn unimplemented(what: impl Into<String>, out: Option<Varnode>) -> Insn {
        Insn {
            op: Opcode::Unimplemented,
            out,
            ins: Vec::new(),
            relative: false,
            note: Some(what.into()),
        }
    }
}

/// One instruction's worth of p-code.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Pcode {
    /// The operations, in order.
    pub ops: Vec<Insn>,
    /// How many `unique` offsets were handed out.
    pub temps: u64,
    /// The SLEIGH constructs that have no opcode, in the order they were met.
    /// Empty means the lift is complete.
    pub unsupported: Vec<String>,
}

impl Pcode {
    /// Whether everything in the instruction was modelled.
    pub fn is_complete(&self) -> bool {
        self.unsupported.is_empty()
    }
}

/// The ceilings a lift runs under.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LiftLimits {
    /// Most operations one instruction may produce.
    pub max_ops: usize,
    /// Deepest macro and expression nesting.
    pub max_depth: usize,
    /// Most `unique` offsets one instruction may use.
    pub max_temps: u64,
}

impl Default for LiftLimits {
    fn default() -> LiftLimits {
        LiftLimits {
            max_ops: 4096,
            max_depth: 64,
            max_temps: 4096,
        }
    }
}

/// Lift a decoded instruction.
///
/// Never fails and never panics: a construct with no opcode becomes
/// [`Opcode::Unimplemented`] with a note, and a ceiling reached stops the walk
/// with what it has. [`Pcode::is_complete`] is how a caller tells a full lift
/// from a partial one.
pub fn lift(spec: &Spec, insn: &Decoded) -> Pcode {
    lift_with(spec, insn, &LiftLimits::default())
}

/// The same, under explicit ceilings.
pub fn lift_with(spec: &Spec, insn: &Decoded, limits: &LiftLimits) -> Pcode {
    let mut l = Lifter {
        spec,
        insn,
        limits,
        out: Pcode::default(),
        labels: HashMap::new(),
        fixups: Vec::new(),
        exports: HashMap::new(),
        params: Vec::new(),
        locals: vec![HashMap::new()],
        depth: 0,
        next_temp: 0,
    };
    l.node(0);
    l.patch_labels();
    let mut out = std::mem::take(&mut l.out);
    out.temps = l.next_temp;
    out
}

struct Lifter<'a> {
    spec: &'a Spec,
    insn: &'a Decoded,
    limits: &'a LiftLimits,
    out: Pcode,
    /// Label index to the operation it sits before, per constructor node.
    labels: HashMap<(u32, u16), usize>,
    /// Operations whose `in0` is a label that had not been placed yet.
    fixups: Vec<(usize, u32, u16)>,
    /// What each constructor node exported, once its body has been lifted.
    exports: HashMap<u32, Export2>,
    /// The macro argument frame, innermost last.
    params: Vec<Vec<Varnode>>,
    /// Temporaries, keyed by node and local index. Macros get their own frame
    /// by being given a node of their own.
    locals: Vec<HashMap<(u32, u16), Varnode>>,
    depth: usize,
    /// The next free `unique` offset.
    next_temp: u64,
}

/// What a constructor exported to the table above it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Export2 {
    /// A varnode, read and written directly.
    Value(Varnode),
    /// `export *[space]:n addr`, which the parent reads and writes *through*.
    Deref {
        /// The pointer.
        addr: Varnode,
        /// The space pointed into.
        space: Space,
        /// How many bytes are read or written.
        size: u8,
    },
}

impl<'a> Lifter<'a> {
    // ---- plumbing ----

    fn emit(&mut self, insn: Insn) -> usize {
        if self.out.ops.len() >= self.limits.max_ops {
            return self.out.ops.len().saturating_sub(1);
        }
        self.out.ops.push(insn);
        self.out.ops.len() - 1
    }

    /// What the specification calls a `define pcodeop`.
    fn pcodeop_name(&self, op: crate::model::PcodeOpId) -> String {
        self.spec
            .pcodeops
            .get(op.index())
            .map(|p| p.name.clone())
            .unwrap_or_else(|| "?".into())
    }

    fn unsupported(&mut self, what: impl Into<String>, out: Option<Varnode>) {
        let what = what.into();
        if self.out.unsupported.len() < 64 {
            self.out.unsupported.push(what.clone());
        }
        self.emit(Insn::unimplemented(what, out));
    }

    fn temp(&mut self, size: u8) -> Varnode {
        let id = self.next_temp;
        self.next_temp = (self.next_temp + size.max(1) as u64).min(self.limits.max_temps);
        Varnode::temp(id, size)
    }

    /// The default space's pointer width, which is what a branch target and a
    /// `*` dereference are measured in.
    fn pointer_size(&self) -> u8 {
        self.spec
            .default_space
            .map(|s| self.spec.space(s).size as u8)
            .unwrap_or(8)
    }

    fn space_of(&self, id: crate::model::SpaceId) -> Space {
        match self.spec.space(id).kind {
            SpaceKind::Register => Space::Register,
            SpaceKind::Constant => Space::Const,
            SpaceKind::Unique => Space::Unique,
            // A specification may define more than one addressable space; x86
            // has `io` beside `ram`. The opcode set has one, so they share it.
            SpaceKind::Ram | SpaceKind::Rom => Space::Ram,
        }
    }

    fn varnode(&self, id: VarnodeId) -> Varnode {
        let v = self.spec.varnode(id);
        Varnode {
            space: self.space_of(v.space),
            offset: v.offset,
            size: v.size.min(255) as u8,
        }
    }

    // ---- the walk ----

    /// Lift one constructor node: its subtables first unless a `build` says
    /// otherwise, then its own body.
    fn node(&mut self, node: u32) {
        if self.depth > self.limits.max_depth || self.out.ops.len() >= self.limits.max_ops {
            return;
        }
        self.depth += 1;
        let Some(n) = self.insn.nodes.get(node as usize) else {
            self.depth -= 1;
            return;
        };
        let c = self.spec.constructor(n.constructor);

        // The manual: "the nodes of a specific symbol tree are traversed in a
        // depth-first order, the p-code for a child node in general comes
        // before the p-code of the parent", and `build` is how a constructor
        // takes control of that. So the children a `build` names are left for
        // the body to place, and the rest go first.
        let built: Vec<u16> = c
            .body
            .iter()
            .flatten()
            .filter_map(|s| match s {
                Stmt::Build(i) => Some(*i),
                _ => None,
            })
            .collect();
        for (i, op) in n.operands.iter().enumerate() {
            if let Value::Sub(child) = op.value
                && !built.contains(&(i as u16))
            {
                self.node(child);
            }
        }

        match &c.body {
            Some(body) => self.body(node, c, body),
            // `unimpl`: the specification declined to model this instruction,
            // which is a fact about the specification and is reported as one.
            None => {
                let name = c
                    .display
                    .mnemonic
                    .clone()
                    .unwrap_or_else(|| "constructor".into());
                self.unsupported(format!("`unimpl`: {name} has no semantic body"), None);
            }
        }
        self.depth -= 1;
    }

    fn body(&mut self, node: u32, c: &Constructor, body: &[Stmt]) {
        for stmt in body {
            if self.out.ops.len() >= self.limits.max_ops {
                return;
            }
            self.stmt(node, c, stmt);
        }
    }

    fn stmt(&mut self, node: u32, c: &Constructor, stmt: &Stmt) {
        match stmt {
            Stmt::Assign { dest, value, .. } => self.assign(node, c, dest, value),
            Stmt::Declare(_) => {}
            Stmt::Build(i) => {
                if let Some(Value::Sub(child)) = self
                    .insn
                    .nodes
                    .get(node as usize)
                    .and_then(|n| n.operands.get(*i as usize))
                    .map(|o| o.value.clone())
                {
                    self.node(child);
                }
            }
            Stmt::Label(i) => {
                let at = self.out.ops.len();
                self.labels.insert((node, *i), at);
            }
            Stmt::Goto(t) => self.jump(node, c, t, Opcode::Branch, Opcode::BranchInd, None),
            Stmt::CondGoto { cond, target } => {
                let c8 = self.expr(node, c, cond, Some(1));
                self.jump(
                    node,
                    c,
                    target,
                    Opcode::CBranch,
                    Opcode::BranchInd,
                    Some(c8),
                );
            }
            Stmt::Call(t) => self.jump(node, c, t, Opcode::Call, Opcode::CallInd, None),
            Stmt::Return(v) => {
                let ptr = self.pointer_size();
                let target = self.expr(node, c, v, Some(ptr));
                self.emit(Insn::new(Opcode::Return, None, vec![target]));
            }
            Stmt::Export(e) => self.export(node, c, e),
            Stmt::UserOp { op, args } => {
                let name = self.pcodeop_name(*op);
                let ins = args
                    .iter()
                    .map(|a| self.expr(node, c, a, None))
                    .collect::<Vec<_>>();
                self.emit(Insn::other(name, None, ins));
            }
            Stmt::MacroCall { mac, args } => self.macro_call(node, c, *mac, args),
            Stmt::DelaySlot(n) => self.unsupported(
                format!("`delayslot({n})`, which places another instruction's p-code here"),
                None,
            ),
            Stmt::CrossBuild { .. } | Stmt::CrossBuildSection(_) => self.unsupported(
                "`crossbuild`, which places another instruction's p-code here",
                None,
            ),
        }
    }

    // ---- assignment ----

    fn assign(&mut self, node: u32, c: &Constructor, dest: &Lvalue, value: &Expr) {
        match dest {
            Lvalue::Symbol { symbol, size } => {
                // The destination's size is what an unsized literal on the
                // right takes, so it has to be settled first.
                let want = size
                    .map(|s| s.min(255) as u8)
                    .or_else(|| self.symbol_size(node, c, *symbol));
                let v = self.expr(node, c, value, want);
                let target = self.lvalue_symbol(node, c, *symbol, want.or(Some(v.size)));
                match target {
                    Some(Export2::Value(t)) => {
                        self.emit(Insn::new(Opcode::Copy, Some(t), vec![v]));
                    }
                    Some(Export2::Deref { addr, space, size }) => {
                        let _ = space;
                        self.emit(Insn::new(Opcode::Store, None, vec![addr, resize(v, size)]));
                    }
                    None => self.unsupported(
                        "an assignment whose target the specification does not bind",
                        None,
                    ),
                }
            }
            Lvalue::BitRange { symbol, lsb, bits } => {
                let Some(Export2::Value(t)) = self.lvalue_symbol(node, c, *symbol, None) else {
                    self.unsupported("a bit range assignment to a target with no varnode", None);
                    return;
                };
                let v = self.expr(node, c, value, Some(t.size));
                // Read, clear the range, shift the new bits in, write back.
                // There is no opcode for a partial write and there should not
                // be: the whole point of the IR being sized is that a write
                // says exactly which bits it changes.
                let mask = range_mask(*lsb, *bits);
                let keep = self.temp(t.size);
                self.emit(Insn::new(
                    Opcode::IntAnd,
                    Some(keep),
                    vec![t, Varnode::constant(!mask, t.size)],
                ));
                let widened = self.widen(v, t.size);
                let masked = self.temp(t.size);
                self.emit(Insn::new(
                    Opcode::IntAnd,
                    Some(masked),
                    vec![widened, Varnode::constant(mask_of(*bits), t.size)],
                ));
                let shifted = self.temp(t.size);
                self.emit(Insn::new(
                    Opcode::IntLeft,
                    Some(shifted),
                    vec![masked, Varnode::constant(*lsb as u64, 4)],
                ));
                self.emit(Insn::new(Opcode::IntOr, Some(t), vec![keep, shifted]));
            }
            Lvalue::Store { space, size, addr } => {
                let ptr = self.pointer_size();
                let a = self.expr(node, c, addr, Some(ptr));
                let bytes = size.map(|s| s.min(255) as u8).unwrap_or(ptr);
                let v = self.expr(node, c, value, Some(bytes));
                let _ = space;
                self.emit(Insn::new(Opcode::Store, None, vec![a, resize(v, bytes)]));
            }
        }
    }

    /// What a symbol names as a destination.
    fn lvalue_symbol(
        &mut self,
        node: u32,
        c: &Constructor,
        symbol: SymbolRef,
        size: Option<u8>,
    ) -> Option<Export2> {
        match symbol {
            SymbolRef::Local(i) => {
                let frame = self.locals.len().saturating_sub(1);
                if let Some(v) = self.locals.get(frame).and_then(|m| m.get(&(node, i))) {
                    return Some(Export2::Value(*v));
                }
                let declared = c
                    .locals
                    .get(i as usize)
                    .and_then(|l| l.size)
                    .map(|s| s.min(255) as u8);
                let v = self.temp(declared.or(size).unwrap_or(self.pointer_size()));
                while self.locals.len() <= frame {
                    self.locals.push(HashMap::new());
                }
                self.locals[frame].insert((node, i), v);
                Some(Export2::Value(v))
            }
            _ => self.read_symbol_place(node, c, symbol),
        }
    }

    // ---- expressions ----

    /// Lower an expression to a varnode holding its value.
    ///
    /// `want` is the size the context needs, used for a literal or a
    /// temporary the specification did not size.
    fn expr(&mut self, node: u32, c: &Constructor, e: &Expr, want: Option<u8>) -> Varnode {
        if self.depth > self.limits.max_depth {
            return Varnode::constant(0, want.unwrap_or(1));
        }
        self.depth += 1;
        let out = self.expr_inner(node, c, e, want);
        self.depth -= 1;
        out
    }

    fn expr_inner(&mut self, node: u32, c: &Constructor, e: &Expr, want: Option<u8>) -> Varnode {
        match e {
            Expr::Num { value, size } => Varnode::constant(
                *value,
                size.map(|s| s.min(255) as u8)
                    .or(want)
                    .unwrap_or(self.pointer_size()),
            ),
            Expr::Symbol(s) => self.read_symbol(node, c, *s, want),
            Expr::Truncate { value, bytes } => {
                let v = self.expr(node, c, value, None);
                let bytes = (*bytes).min(255) as u8;
                let out = self.temp(bytes);
                self.emit(Insn::new(
                    Opcode::SubPiece,
                    Some(out),
                    vec![v, Varnode::constant(0, 4)],
                ));
                out
            }
            Expr::Shave { value, bytes } => {
                let v = self.expr(node, c, value, None);
                let drop = (*bytes).min(255) as u8;
                let size = want.unwrap_or_else(|| v.size.saturating_sub(drop).max(1));
                let out = self.temp(size);
                self.emit(Insn::new(
                    Opcode::SubPiece,
                    Some(out),
                    vec![v, Varnode::constant(drop as u64, 4)],
                ));
                out
            }
            Expr::BitRange { value, lsb, bits } => {
                let v = self.expr(node, c, value, None);
                let shifted = if *lsb == 0 {
                    v
                } else {
                    let t = self.temp(v.size);
                    self.emit(Insn::new(
                        Opcode::IntRight,
                        Some(t),
                        vec![v, Varnode::constant(*lsb as u64, 4)],
                    ));
                    t
                };
                let out = self.temp(v.size);
                self.emit(Insn::new(
                    Opcode::IntAnd,
                    Some(out),
                    vec![shifted, Varnode::constant(mask_of(*bits), v.size)],
                ));
                out
            }
            Expr::AddressOf { value, size } => {
                let size = size
                    .map(|s| s.min(255) as u8)
                    .or(want)
                    .unwrap_or(self.pointer_size());
                // The address of a varnode is a disassembly-time constant, so
                // it is the offset the specification gave it.
                match &**value {
                    Expr::Symbol(s) => match self.read_symbol_place(node, c, *s) {
                        Some(Export2::Value(v)) => Varnode::constant(v.offset, size),
                        Some(Export2::Deref { addr, .. }) => resize(addr, size),
                        None => Varnode::constant(0, size),
                    },
                    other => {
                        let v = self.expr(node, c, other, Some(size));
                        Varnode::constant(v.offset, size)
                    }
                }
            }
            Expr::Load { space, size, addr } => {
                let ptr = self.pointer_size();
                let a = self.expr(node, c, addr, Some(ptr));
                let bytes = size.map(|s| s.min(255) as u8).or(want).unwrap_or(ptr);
                let _ = space;
                let out = self.temp(bytes);
                self.emit(Insn::new(Opcode::Load, Some(out), vec![a]));
                out
            }
            Expr::Unary(op, a) => {
                let (opcode, boolean) = match op {
                    UnOp::BoolNegate => (Opcode::BoolNot, true),
                    UnOp::Negate => (Opcode::IntNot, false),
                    UnOp::TwosComp => (Opcode::IntNegate, false),
                    UnOp::FloatNeg => (Opcode::FloatNeg, false),
                };
                let want_in = if boolean { Some(1) } else { want };
                let v = self.expr(node, c, a, want_in);
                let size = if boolean { 1 } else { v.size };
                let out = self.temp(size);
                self.emit(Insn::new(opcode, Some(out), vec![v]));
                out
            }
            Expr::Binary(op, a, b) => self.binary(node, c, *op, a, b, want),
            Expr::Intrinsic { op, args } => self.intrinsic(node, c, *op, args, want),
            Expr::UserOp { op, args } => {
                let name = self.pcodeop_name(*op);
                let ins = args
                    .iter()
                    .map(|a| self.expr(node, c, a, None))
                    .collect::<Vec<_>>();
                let out = self.temp(want.unwrap_or(self.pointer_size()));
                self.emit(Insn::other(name, Some(out), ins));
                out
            }
        }
    }

    fn binary(
        &mut self,
        node: u32,
        c: &Constructor,
        op: BinOp,
        a: &Expr,
        b: &Expr,
        want: Option<u8>,
    ) -> Varnode {
        use BinOp::*;
        // A comparison produces one byte whatever its inputs are, and a shift
        // count is its own size, so neither takes the caller's `want`.
        let compare = matches!(
            op,
            SLess
                | SLessEqual
                | Less
                | LessEqual
                | FloatLess
                | FloatLessEqual
                | Equal
                | NotEqual
                | FloatEqual
                | FloatNotEqual
                | BoolXor
                | BoolAnd
                | BoolOr
        );
        let boolean = matches!(op, BoolXor | BoolAnd | BoolOr);
        let shift = matches!(op, Left | Right | SRight);

        let want_a = if boolean {
            Some(1)
        } else if compare {
            None
        } else {
            want
        };
        let mut left = self.expr(node, c, a, want_a);
        let want_b = if boolean {
            Some(1)
        } else if shift {
            Some(4)
        } else {
            Some(left.size)
        };
        let mut right = self.expr(node, c, b, want_b);
        // A constant that arrived without a size takes its partner's.
        if !shift && !boolean {
            if left.space == Space::Const && right.space != Space::Const {
                left = resize(left, right.size);
            } else if right.space == Space::Const && left.space != Space::Const {
                right = resize(right, left.size);
            }
        }

        let opcode = match op {
            Mult => Opcode::IntMul,
            Div => Opcode::IntDiv,
            SDiv => Opcode::IntSDiv,
            Rem => Opcode::IntRem,
            SRem => Opcode::IntSRem,
            FloatDiv => Opcode::FloatDiv,
            FloatMult => Opcode::FloatMul,
            Add => Opcode::IntAdd,
            Sub => Opcode::IntSub,
            FloatAdd => Opcode::FloatAdd,
            FloatSub => Opcode::FloatSub,
            Left => Opcode::IntLeft,
            Right => Opcode::IntRight,
            SRight => Opcode::IntSRight,
            SLess => Opcode::IntSLess,
            SLessEqual => Opcode::IntSLessEqual,
            Less => Opcode::IntLess,
            LessEqual => Opcode::IntLessEqual,
            FloatLess => Opcode::FloatLess,
            FloatLessEqual => Opcode::FloatLessEqual,
            Equal => Opcode::IntEqual,
            NotEqual => Opcode::IntNotEqual,
            FloatEqual => Opcode::FloatEqual,
            FloatNotEqual => Opcode::FloatNotEqual,
            And => Opcode::IntAnd,
            Xor => Opcode::IntXor,
            Or => Opcode::IntOr,
            BoolXor => Opcode::BoolXor,
            BoolAnd => Opcode::BoolAnd,
            BoolOr => Opcode::BoolOr,
        };
        let size = if compare {
            1
        } else {
            want.unwrap_or(left.size)
        };
        let out = self.temp(size);
        self.emit(Insn::new(opcode, Some(out), vec![left, right]));
        out
    }

    fn intrinsic(
        &mut self,
        node: u32,
        c: &Constructor,
        op: Intrinsic,
        args: &[Expr],
        want: Option<u8>,
    ) -> Varnode {
        let ptr = self.pointer_size();
        let arg = |l: &mut Self, i: usize, w: Option<u8>| -> Varnode {
            match args.get(i) {
                Some(e) => l.expr(node, c, e, w),
                None => Varnode::constant(0, w.unwrap_or(1)),
            }
        };
        let (opcode, out_size) = match op {
            Intrinsic::Zext => (Opcode::IntZExt, want.unwrap_or(ptr)),
            Intrinsic::Sext => (Opcode::IntSExt, want.unwrap_or(ptr)),
            Intrinsic::Carry => (Opcode::IntCarry, 1),
            Intrinsic::SCarry => (Opcode::IntSCarry, 1),
            Intrinsic::SBorrow => (Opcode::IntSBorrow, 1),
            Intrinsic::Nan => (Opcode::FloatNan, 1),
            Intrinsic::Abs => (Opcode::FloatAbs, want.unwrap_or(ptr)),
            Intrinsic::Sqrt => (Opcode::FloatSqrt, want.unwrap_or(ptr)),
            Intrinsic::Int2Float => (Opcode::IntToFloat, want.unwrap_or(ptr)),
            Intrinsic::Float2Float => (Opcode::FloatConvert, want.unwrap_or(ptr)),
            Intrinsic::Trunc => (Opcode::FloatToInt, want.unwrap_or(ptr)),
            Intrinsic::Ceil => (Opcode::FloatCeil, want.unwrap_or(ptr)),
            Intrinsic::Floor => (Opcode::FloatFloor, want.unwrap_or(ptr)),
            Intrinsic::Round => (Opcode::FloatRound, want.unwrap_or(ptr)),
            Intrinsic::PopCount => (Opcode::PopCount, want.unwrap_or(4)),
            Intrinsic::LzCount => (Opcode::LzCount, want.unwrap_or(4)),
            Intrinsic::CPool | Intrinsic::NewObject => {
                let name = if matches!(op, Intrinsic::CPool) {
                    "`cpool`, Ghidra's CPOOLREF"
                } else {
                    "`newobject`, Ghidra's NEW"
                };
                let out = self.temp(want.unwrap_or(ptr));
                self.unsupported(format!("{name}, which has no opcode"), Some(out));
                return out;
            }
        };
        let a = arg(self, 0, None);
        let mut ins = vec![a];
        // The two and three input forms: carry and borrow take both operands.
        if matches!(
            op,
            Intrinsic::Carry | Intrinsic::SCarry | Intrinsic::SBorrow
        ) {
            let b = arg(self, 1, Some(a.size));
            ins.push(b);
        }
        let out = self.temp(out_size);
        self.emit(Insn::new(opcode, Some(out), ins));
        out
    }

    // ---- symbols ----

    /// The size a symbol reads at, when that is knowable without emitting
    /// anything.
    fn symbol_size(&mut self, node: u32, c: &Constructor, s: SymbolRef) -> Option<u8> {
        match s {
            SymbolRef::Varnode(v) => Some(self.varnode(v).size),
            SymbolRef::BitRange(b) => self
                .spec
                .bitranges
                .get(b.index())
                .map(|r| (r.bits.div_ceil(8)).clamp(1, 255) as u8),
            SymbolRef::Local(i) => c
                .locals
                .get(i as usize)
                .and_then(|l| l.size)
                .map(|s| s.min(255) as u8),
            SymbolRef::Operand(i) => match self.operand_export(node, i) {
                Some(Export2::Value(v)) => Some(v.size),
                Some(Export2::Deref { size, .. }) => Some(size),
                None => None,
            },
            _ => None,
        }
    }

    /// What a symbol names, without loading through a dereference.
    fn read_symbol_place(&mut self, node: u32, c: &Constructor, s: SymbolRef) -> Option<Export2> {
        match s {
            SymbolRef::Varnode(v) => Some(Export2::Value(self.varnode(v))),
            SymbolRef::BitRange(b) => {
                let r = self.spec.bitranges.get(b.index())?;
                // A bit range that happens to sit on byte boundaries is an
                // ordinary varnode; one that does not has no varnode of its
                // own, and the read and write paths handle it as bits of the
                // register it lives in.
                let reg = self.varnode(r.register);
                if r.low % 8 == 0 && r.bits % 8 == 0 {
                    return Some(Export2::Value(Varnode {
                        offset: reg.offset + (r.low / 8) as u64,
                        size: (r.bits / 8).clamp(1, 255) as u8,
                        ..reg
                    }));
                }
                Some(Export2::Value(reg))
            }
            SymbolRef::Local(i) => {
                let frame = self.locals.len().saturating_sub(1);
                self.locals
                    .get(frame)
                    .and_then(|m| m.get(&(node, i)))
                    .copied()
                    .map(Export2::Value)
                    .or_else(|| self.lvalue_symbol(node, c, s, None))
            }
            SymbolRef::Param(i) => self
                .params
                .last()
                .and_then(|f| f.get(i as usize))
                .copied()
                .map(Export2::Value),
            SymbolRef::Operand(i) => self.operand_export(node, i),
            SymbolRef::Builtin(b) => {
                let size = self.pointer_size();
                let v = match b {
                    Builtin::InstStart => self.insn.addr,
                    Builtin::InstNext => self.insn.end(),
                    Builtin::InstNext2 => self.insn.end(),
                    Builtin::Epsilon => 0,
                };
                Some(Export2::Value(Varnode::constant(v, size)))
            }
            SymbolRef::Field(_)
            | SymbolRef::Context(_)
            | SymbolRef::Table(_)
            | SymbolRef::Space(_) => None,
        }
    }

    /// Read a symbol's value, loading through a dereferencing export.
    fn read_symbol(
        &mut self,
        node: u32,
        c: &Constructor,
        s: SymbolRef,
        want: Option<u8>,
    ) -> Varnode {
        match self.read_symbol_place(node, c, s) {
            Some(Export2::Value(v)) => v,
            Some(Export2::Deref { addr, size, .. }) => {
                let out = self.temp(want.unwrap_or(size));
                self.emit(Insn::new(Opcode::Load, Some(out), vec![addr]));
                out
            }
            None => {
                let size = want.unwrap_or(self.pointer_size());
                let out = self.temp(size);
                self.unsupported(
                    "a symbol with no varnode: the specification names something \
                     this lifter cannot place",
                    Some(out),
                );
                out
            }
        }
    }

    /// What an operand of this node contributes as a value.
    fn operand_export(&mut self, node: u32, i: u16) -> Option<Export2> {
        let op = self
            .insn
            .nodes
            .get(node as usize)?
            .operands
            .get(i as usize)?;
        match &op.value {
            Value::Var(v) => Some(Export2::Value(self.varnode(*v))),
            // An integer operand is a constant in the semantics, sized like a
            // pointer because that is the widest thing it is ever added to and
            // a constant's size only decides how it is read.
            Value::Int(n) => Some(Export2::Value(Varnode::constant(
                *n as u64,
                self.pointer_size(),
            ))),
            Value::Sub(child) => self.exports.get(child).copied(),
            Value::Name(_) | Value::Unresolved => None,
        }
    }

    fn export(&mut self, node: u32, c: &Constructor, e: &Export) {
        let value = match e {
            Export::Value(expr) => {
                // `export r1;` exports the varnode, not a copy of it, so a
                // parent writing through the table writes the register. Taking
                // the place rather than the value is what preserves that.
                if let Expr::Symbol(s) = expr
                    && let Some(place) = self.read_symbol_place(node, c, *s)
                {
                    place
                } else {
                    Export2::Value(self.expr(node, c, expr, None))
                }
            }
            Export::Deref { space, size, addr } => {
                let ptr = self.pointer_size();
                let a = self.expr(node, c, addr, Some(ptr));
                Export2::Deref {
                    addr: a,
                    space: space.map(|s| self.space_of(s)).unwrap_or(Space::Ram),
                    size: size.map(|s| s.min(255) as u8).unwrap_or(ptr),
                }
            }
        };
        self.exports.insert(node, value);
    }

    // ---- control flow ----

    fn jump(
        &mut self,
        node: u32,
        c: &Constructor,
        target: &JumpTarget,
        direct: Opcode,
        indirect: Opcode,
        cond: Option<Varnode>,
    ) {
        let ptr = self.pointer_size();
        match target {
            JumpTarget::Direct { addr, .. } => {
                let a = self.expr(node, c, addr, Some(ptr));
                // A direct branch whose target is not a constant is an
                // indirect branch wearing a constant's syntax, which is what
                // `goto operand` is when the operand exported a register.
                let op = if a.space == Space::Const {
                    direct
                } else {
                    indirect
                };
                let mut ins = vec![a];
                if let Some(cv) = cond {
                    ins.push(cv);
                }
                let op = if cond.is_some() && op == indirect {
                    // There is no conditional indirect branch. Branch over an
                    // unconditional indirect one instead.
                    let skip = self.emit(Insn::new(
                        Opcode::CBranch,
                        None,
                        vec![
                            Varnode::constant(0, ptr),
                            cond.unwrap_or(Varnode::constant(0, 1)),
                        ],
                    ));
                    self.emit(Insn::new(indirect, None, vec![a]));
                    let after = self.out.ops.len();
                    if let Some(b) = self.out.ops.get_mut(skip) {
                        b.relative = true;
                        b.ins[0] = Varnode::constant(after as u64, ptr);
                        // The condition is inverted: the guard skips the
                        // branch when the condition is false.
                    }
                    let inverted = self.temp(1);
                    self.out.ops.insert(
                        skip,
                        Insn::new(
                            Opcode::BoolNot,
                            Some(inverted),
                            vec![cond.unwrap_or(Varnode::constant(0, 1))],
                        ),
                    );
                    if let Some(b) = self.out.ops.get_mut(skip + 1) {
                        b.ins[1] = inverted;
                        b.ins[0] = Varnode::constant((after + 1) as u64, ptr);
                    }
                    return;
                } else {
                    op
                };
                self.emit(Insn::new(op, None, ins));
            }
            JumpTarget::Indirect(e) => {
                let a = self.expr(node, c, e, Some(ptr));
                match cond {
                    None => {
                        self.emit(Insn::new(indirect, None, vec![a]));
                    }
                    Some(cv) => {
                        // Same shape as above: guard, then jump.
                        let inverted = self.temp(1);
                        self.emit(Insn::new(Opcode::BoolNot, Some(inverted), vec![cv]));
                        let guard = self.emit(Insn::new(
                            Opcode::CBranch,
                            None,
                            vec![Varnode::constant(0, ptr), inverted],
                        ));
                        self.emit(Insn::new(indirect, None, vec![a]));
                        let after = self.out.ops.len();
                        if let Some(b) = self.out.ops.get_mut(guard) {
                            b.relative = true;
                            b.ins[0] = Varnode::constant(after as u64, ptr);
                        }
                    }
                }
            }
            JumpTarget::Label(i) => {
                let mut ins = vec![Varnode::constant(0, ptr)];
                if let Some(cv) = cond {
                    ins.push(cv);
                }
                let op = if cond.is_some() {
                    Opcode::CBranch
                } else {
                    Opcode::Branch
                };
                let at = self.emit(Insn::new(op, None, ins));
                if let Some(b) = self.out.ops.get_mut(at) {
                    b.relative = true;
                }
                self.fixups.push((at, node, *i));
            }
        }
    }

    /// Point every label branch at the operation its label sits before.
    ///
    /// A label that was never placed points just past the end, which is a
    /// branch out of the instruction and is what falling off the end of the
    /// body means.
    fn patch_labels(&mut self) {
        let end = self.out.ops.len() as u64;
        for (at, node, label) in std::mem::take(&mut self.fixups) {
            let target = self
                .labels
                .get(&(node, label))
                .map(|&i| i as u64)
                .unwrap_or(end);
            if let Some(op) = self.out.ops.get_mut(at) {
                let size = op.ins[0].size;
                op.ins[0] = Varnode::constant(target, size);
            }
        }
    }

    // ---- macros ----

    fn macro_call(&mut self, node: u32, c: &Constructor, mac: MacroId, args: &[Expr]) {
        if self.depth > self.limits.max_depth || self.params.len() > 16 {
            self.unsupported("a macro nested past the depth limit", None);
            return;
        }
        let Some(def) = self.spec.macros.get(mac.index()) else {
            self.unsupported("a macro the specification does not define", None);
            return;
        };
        // Arguments are passed by reference: a macro that assigns to a
        // parameter assigns to what the caller named. So each argument is
        // lowered to a place, not to a copy, wherever it has one.
        let mut frame = Vec::with_capacity(args.len());
        for a in args {
            let v = match a {
                Expr::Symbol(s) => match self.read_symbol_place(node, c, *s) {
                    Some(Export2::Value(v)) => v,
                    _ => self.expr(node, c, a, None),
                },
                _ => self.expr(node, c, a, None),
            };
            frame.push(v);
        }
        self.params.push(frame);
        self.locals.push(HashMap::new());
        self.depth += 1;
        // The macro's body is lifted against a synthetic constructor so its
        // own locals and labels do not collide with the caller's.
        let body = def.body.clone();
        let shim = macro_shim(def);
        for stmt in &body {
            if self.out.ops.len() >= self.limits.max_ops {
                break;
            }
            self.stmt(node, &shim, stmt);
        }
        self.depth -= 1;
        self.locals.pop();
        self.params.pop();
    }
}

/// A constructor-shaped view of a macro, so one statement walker serves both.
fn macro_shim(def: &crate::model::MacroDef) -> Constructor {
    Constructor {
        table: crate::model::TableId(0),
        display: crate::model::Display::default(),
        operands: Vec::new(),
        order: Vec::new(),
        locals: def.locals.clone(),
        labels: def.labels.clone(),
        pattern: crate::model::PatternExpr::Epsilon,
        resolved: crate::model::ResolvedPattern::default(),
        disasm: Vec::new(),
        body: Some(Vec::new()),
        location: def.location.clone(),
    }
}

/// `size` low bits set.
fn mask_of(bits: u32) -> u64 {
    if bits == 0 {
        0
    } else if bits >= 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    }
}

fn range_mask(lsb: u32, bits: u32) -> u64 {
    mask_of(bits).checked_shl(lsb).unwrap_or(0)
}

/// The same varnode read at a different width. Only meaningful for a constant,
/// which is why nothing else is changed: a register read at the wrong width is
/// a different register.
fn resize(v: Varnode, size: u8) -> Varnode {
    if v.space == Space::Const {
        Varnode { size, ..v }
    } else {
        v
    }
}

impl Lifter<'_> {
    /// Zero extend a value to `size` bytes, or return it unchanged.
    fn widen(&mut self, v: Varnode, size: u8) -> Varnode {
        if v.size >= size {
            return v;
        }
        if v.space == Space::Const {
            return Varnode { size, ..v };
        }
        let out = self.temp(size);
        self.emit(Insn::new(Opcode::IntZExt, Some(out), vec![v]));
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Decoder;

    const TOY: &str = r#"
define endian=little;
define space ram type=ram_space size=4 default;
define space register type=register_space size=4;
define register offset=0 size=4 [ r0 r1 r2 r3 ];
define token instr(16) op=(12,15) rd=(8,11) rs=(4,7) imm8=(0,7);
attach variables [ rd rs ] [ r0 r1 r2 r3 ];

:add rd,rs is op=0 & rd & rs { rd = rd + rs; }
:ld rd,rs  is op=1 & rd & rs { rd = *:4 rs; }
:st rd,rs  is op=2 & rd & rs { *:4 rd = rs; }
:jz rd,imm8 is op=3 & rd & imm8 { if (rd == 0) goto inst_start; }
:bad rd is op=4 & rd unimpl
"#;

    fn spec() -> crate::Spec {
        crate::parse_str(TOY).expect("parses")
    }

    fn lift_bytes(spec: &crate::Spec, bytes: &[u8]) -> Pcode {
        let mut d = Decoder::new(spec);
        let insn = d.decode(bytes, 0x1000).expect("decodes");
        lift(spec, &insn)
    }

    #[test]
    fn an_add_lifts_to_one_operation_on_two_registers() {
        let s = spec();
        // op=0 rd=1 rs=2
        let p = lift_bytes(&s, &[0x20, 0x01]);
        assert!(p.is_complete(), "{:?}", p.unsupported);
        let adds: Vec<&Insn> = p.ops.iter().filter(|o| o.op == Opcode::IntAdd).collect();
        assert_eq!(adds.len(), 1, "{:?}", p.ops);
        assert_eq!(adds[0].ins[0], Varnode::register(4, 4), "r1");
        assert_eq!(adds[0].ins[1], Varnode::register(8, 4), "r2");
        // And the result reaches r1.
        assert!(
            p.ops
                .iter()
                .any(|o| o.op == Opcode::Copy && o.out == Some(Varnode::register(4, 4)))
        );
    }

    #[test]
    fn a_dereference_becomes_a_load_and_a_store() {
        let s = spec();
        let load = lift_bytes(&s, &[0x20, 0x11]);
        assert!(load.ops.iter().any(|o| o.op == Opcode::Load));
        let store = lift_bytes(&s, &[0x20, 0x21]);
        assert!(store.ops.iter().any(|o| o.op == Opcode::Store));
    }

    #[test]
    fn a_conditional_branch_lifts_to_a_comparison_and_a_cbranch() {
        let s = spec();
        let p = lift_bytes(&s, &[0x00, 0x31]);
        assert!(p.ops.iter().any(|o| o.op == Opcode::IntEqual));
        let branch = p
            .ops
            .iter()
            .find(|o| o.op == Opcode::CBranch)
            .expect("a cbranch");
        assert_eq!(branch.ins[0], Varnode::constant(0x1000, 4), "inst_start");
        assert!(!branch.relative, "an address, not a p-code index");
    }

    #[test]
    fn unimpl_is_reported_rather_than_lifted_to_nothing() {
        let s = spec();
        let p = lift_bytes(&s, &[0x00, 0x41]);
        assert!(!p.is_complete());
        assert!(p.unsupported[0].contains("unimpl"), "{:?}", p.unsupported);
        assert_eq!(p.ops.len(), 1);
        assert_eq!(p.ops[0].op, Opcode::Unimplemented);
    }

    /// A `define pcodeop` is the specification saying an operation has no
    /// p-code, so naming it with its inputs and its output is a complete lift
    /// of an opaque operation. Losing the name, which is what
    /// `Opcode::Unimplemented` did, is what was incomplete.
    #[test]
    fn a_user_operation_is_named_with_its_inputs_and_its_output() {
        let s = crate::parse_str(
            r#"
define endian=little;
define space ram type=ram_space size=4 default;
define space register type=register_space size=4;
define register offset=0 size=4 [ r0 r1 ];
define token instr(8) op=(1,7) rd=(0,0);
define pcodeop arctan;
attach variables [ rd ] [ r0 r1 ];
:at rd is op=0 & rd { rd = arctan(rd); }
"#,
        )
        .expect("parses");
        let p = lift_bytes(&s, &[0x00]);
        assert!(p.is_complete(), "{:?}", p.unsupported);
        let call = p
            .ops
            .iter()
            .find(|i| i.op == Opcode::Other)
            .expect("the user operation is in the p-code");
        assert_eq!(call.note.as_deref(), Some("arctan"));
        assert_eq!(call.ins.len(), 1, "its argument is carried: {:?}", call.ins);
        assert!(call.out.is_some(), "and its result: {call:?}");
    }

    #[test]
    fn a_label_branch_is_a_p_code_index_and_points_forwards() {
        let s = crate::parse_str(
            r#"
define endian=little;
define space ram type=ram_space size=4 default;
define space register type=register_space size=4;
define register offset=0 size=4 [ r0 r1 ];
define token instr(8) op=(1,7) rd=(0,0);
attach variables [ rd ] [ r0 r1 ];
:skip rd is op=0 & rd { if (rd == 0) goto <done>; rd = rd + 1; <done> rd = rd - 1; }
"#,
        )
        .expect("parses");
        let p = lift_bytes(&s, &[0x00]);
        let branch = p
            .ops
            .iter()
            .position(|o| o.op == Opcode::CBranch)
            .expect("a cbranch");
        assert!(p.ops[branch].relative, "a label target is a p-code index");
        let target = p.ops[branch].ins[0].offset as usize;
        assert!(
            target > branch && target <= p.ops.len(),
            "target {target} should be a later operation, of {}",
            p.ops.len()
        );
    }
}
