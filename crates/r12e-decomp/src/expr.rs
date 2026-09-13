//! Expressions rebuilt from SSA.
//!
//! An SSA operation is a machine-shaped thing: one operator, operands that are
//! versioned locations. C is tree-shaped. Rebuilding means inlining a value's
//! definition into its use, which is only safe when the value is used once and
//! nothing between the two changes what it depends on.
//!
//! The rule here is deliberately conservative. A value used more than once
//! becomes a named local rather than being duplicated, because duplicating a
//! load or a call would change what the code does, and duplicating arithmetic
//! makes the output longer rather than clearer.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use r12e_ir::op::Op;
use r12e_ir::abi::Abi;
use r12e_ir::ssa::{Location, Operand, SsaFunction, SsaKind, SsaOp, Value};

/// A rebuilt expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    /// A literal.
    Const(u64, u8),
    /// A literal read as a floating point number, which is how the bit pattern
    /// was meant when a floating point operation consumes it.
    FConst(u64, u8),
    /// A named local.
    Local(String),
    /// A value that arrived from outside: an argument, or a register the
    /// function inherited. The name is resolved once, where the convention is
    /// known.
    Input(Location, String),
    /// A unary operator applied to an expression.
    Unary(&'static str, Box<Expr>),
    /// A binary operator.
    Binary(&'static str, Box<Expr>, Box<Expr>),
    /// A memory read.
    Deref(Box<Expr>, u8),
    /// A named operation C has no operator for.
    Named(&'static str, Vec<Expr>),
    /// A call to a known address.
    Call(u64, Vec<Expr>),
    /// A call through an expression.
    CallInd(Box<Expr>),
    /// A cast, which the machine performs and C has to be told about.
    Cast(&'static str, Box<Expr>),
    /// Something the rebuilder does not model, named by its operator.
    Unknown(&'static str),
}

impl Expr {
    /// True when the expression is a literal.
    pub fn is_const(&self) -> bool {
        matches!(self, Expr::Const(..))
    }

    /// How deep the tree goes, used to keep one statement from growing past
    /// what a person can read.
    pub fn depth(&self) -> usize {
        match self {
            Expr::Unary(_, a) | Expr::Cast(_, a) | Expr::Deref(a, _) => 1 + a.depth(),
            Expr::Binary(_, a, b) => 1 + a.depth().max(b.depth()),
            Expr::Call(_, args) => 1 + args.iter().map(Expr::depth).max().unwrap_or(0),
            Expr::CallInd(a) => 1 + a.depth(),
            _ => 1,
        }
    }
}

/// The precedence of an operator, so parentheses appear only where they are
/// needed. C's table, with the operators this emits.
fn precedence(op: &str) -> u8 {
    match op {
        "*" | "/" | "%" => 10,
        "+" | "-" => 9,
        "<<" | ">>" => 8,
        "<" | "<=" | ">" | ">=" => 7,
        "==" | "!=" => 6,
        "&" => 5,
        "^" => 4,
        "|" => 3,
        "&&" => 2,
        "||" => 1,
        _ => 11,
    }
}

/// Read a constant as signed at its own width.
fn sign_extend(v: u64, size: u8) -> i64 {
    if size == 0 || size >= 8 {
        return v as i64;
    }
    let bits = size as u32 * 8;
    ((v << (64 - bits)) as i64) >> (64 - bits)
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.render(f, 0)
    }
}

impl Expr {
    fn render(&self, f: &mut fmt::Formatter<'_>, outer: u8) -> fmt::Result {
        match self {
            Expr::Const(v, size) => {
                // A small value reads better in decimal; a large one is almost
                // always a mask or an address and reads better in hex.
                let signed = sign_extend(*v, *size);
                if *size <= 8 && signed < 0 && signed > -0x10000 {
                    write!(f, "{signed}")
                } else if *v < 0x10000 {
                    write!(f, "{v}")
                } else {
                    write!(f, "{v:#x}")
                }
            }
            Expr::FConst(bits, size) => {
                let v = if *size == 4 {
                    f32::from_bits(*bits as u32) as f64
                } else {
                    f64::from_bits(*bits)
                };
                // A round number still reads as one, and anything else keeps
                // enough digits to name the same value again.
                if v == v.trunc() && v.abs() < 1e15 {
                    write!(f, "{v:.1}")
                } else {
                    write!(f, "{v}")
                }
            }
            Expr::Local(n) => f.write_str(n),
            Expr::Input(_, name) => f.write_str(name),
            Expr::Unary(op, a) => {
                f.write_str(op)?;
                a.render(f, 11)
            }
            Expr::Binary(op, a, b) => {
                let p = precedence(op);
                let parens = p < outer;
                if parens {
                    f.write_str("(")?;
                }
                a.render(f, p)?;
                write!(f, " {op} ")?;
                // The right operand of a left-associative operator needs
                // parentheses at equal precedence.
                b.render(f, p + 1)?;
                if parens {
                    f.write_str(")")?;
                }
                Ok(())
            }
            Expr::Deref(a, size) => {
                write!(f, "*({} *)", c_type(*size))?;
                a.render(f, 11)
            }
            Expr::Named(name, args) => {
                f.write_str(name)?;
                f.write_str("(")?;
                for (n, a) in args.iter().enumerate() {
                    if n > 0 {
                        f.write_str(", ")?;
                    }
                    a.render(f, 0)?;
                }
                f.write_str(")")
            }
            Expr::Call(target, args) => {
                write!(f, "sub_{target:x}(")?;
                for (n, a) in args.iter().enumerate() {
                    if n > 0 {
                        f.write_str(", ")?;
                    }
                    a.render(f, 0)?;
                }
                f.write_str(")")
            }
            Expr::CallInd(a) => {
                f.write_str("(*")?;
                a.render(f, 11)?;
                f.write_str(")()")
            }
            Expr::Cast(t, a) => {
                write!(f, "({t})")?;
                a.render(f, 11)
            }
            Expr::Unknown(what) => write!(f, "__{what}()"),
        }
    }
}

/// The C type for a size in bytes.
/// The floating point type of a width.
pub fn float_type(size: u8) -> &'static str {
    if size == 4 { "float" } else { "double" }
}

/// The unsigned C type of a width.
pub fn c_type(size: u8) -> &'static str {
    match size {
        1 => "uint8_t",
        2 => "uint16_t",
        4 => "uint32_t",
        16 => "__int128",
        _ => "uint64_t",
    }
}

/// The signed C type for a size in bytes.
fn signed_type(size: u8) -> &'static str {
    match size {
        1 => "int8_t",
        2 => "int16_t",
        4 => "int32_t",
        _ => "int64_t",
    }
}

/// A readable name for a location nothing defines.
///
/// On AArch64 the first eight registers carry arguments, so they are named as
/// such; anything else keeps its machine name, which is honest about not
/// knowing where the value came from.
pub fn input_name(l: Location, abi: &Abi) -> String {
    if l.space == r12e_ir::op::Space::Stack {
        return slot_name(l);
    }
    if l.space != r12e_ir::op::Space::Register {
        return format!("mem{:x}", l.offset);
    }
    if l.offset == abi.stack_pointer {
        return "sp".to_string();
    }
    // A register the convention passes arguments in, read before anything
    // wrote it, is an argument. Anything else read that way is a register the
    // function inherited, which is named rather than invented.
    if let Some(name) = abi.argument_name(l.offset) {
        return name;
    }
    if l.size == 1 {
        return format!("flag{}", l.offset % 8);
    }
    format!("reg{:x}", l.offset)
}

/// How many times each value is read.
pub fn use_counts(f: &SsaFunction) -> BTreeMap<Value, usize> {
    let mut out: BTreeMap<Value, usize> = BTreeMap::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            for i in &op.inputs {
                if let Operand::Value(v) = i {
                    *out.entry(*v).or_default() += 1;
                }
            }
        }
    }
    out
}

/// The name a promoted stack slot gets, from its offset.
pub fn slot_name(l: Location) -> String {
    let offset = l.offset as i64;
    if offset < 0 {
        format!("local_{:x}", -offset)
    } else {
        // Above the stack pointer on entry is the caller's frame, which is
        // where arguments past the registers arrive.
        format!("arg_s{offset:x}")
    }
}

/// True when a location is an argument the caller passed on the stack.
pub fn is_stack_argument(l: Location) -> bool {
    l.space == r12e_ir::op::Space::Stack && (l.offset as i64) > 0
}

/// Which locations hold floating point values.
///
/// Anything a floating point operation reads or writes, which is as much type
/// recovery as this needs: the operation says what the bits mean.
pub fn float_locations(f: &SsaFunction) -> BTreeSet<Location> {
    let mut out = BTreeSet::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            let SsaKind::Op(o) = op.kind else { continue };
            if !is_float_op(o) {
                continue;
            }
            if let Some(v) = op.out {
                if !produces_bool(o) {
                    out.insert(v.location);
                }
            }
            // The integer side of a conversion is not floating.
            if matches!(o, Op::IntToFloat | Op::UIntToFloat) {
                continue;
            }
            for i in &op.inputs {
                match i {
                    Operand::Value(v) => {
                        out.insert(v.location);
                    }
                    Operand::Undefined(l) => {
                        out.insert(*l);
                    }
                    Operand::Const(..) => {}
                }
            }
        }
    }
    out
}

fn is_float_op(o: Op) -> bool {
    matches!(
        o,
        Op::FloatAdd
            | Op::FloatSub
            | Op::FloatMul
            | Op::FloatDiv
            | Op::FloatMulAdd
            | Op::FloatNeg
            | Op::FloatAbs
            | Op::FloatSqrt
            | Op::FloatMax
            | Op::FloatMin
            | Op::FloatEqual
            | Op::FloatNotEqual
            | Op::FloatLess
            | Op::FloatLessEqual
            | Op::FloatNan
            | Op::FloatTrunc
            | Op::FloatRound
            | Op::FloatCeil
            | Op::FloatFloor
            | Op::FloatConvert
            | Op::FloatToInt
            | Op::FloatToUInt
            | Op::IntToFloat
            | Op::UIntToFloat
    )
}

fn produces_bool(o: Op) -> bool {
    matches!(
        o,
        Op::FloatEqual
            | Op::FloatNotEqual
            | Op::FloatLess
            | Op::FloatLessEqual
            | Op::FloatNan
            | Op::FloatToInt
            | Op::FloatToUInt
    )
}

/// Rebuilds expressions from an SSA function.
pub struct Rebuilder<'a> {
    f: &'a SsaFunction,
    /// The calling convention, which says what an incoming register means.
    pub abi: Abi,
    defs: BTreeMap<Value, (r12e_core::Addr, usize)>,
    uses: BTreeMap<Value, usize>,
    /// Values that became named locals because they are read more than once.
    pub locals: BTreeMap<Value, String>,
    /// Locations that hold floating point values, which is what decides how a
    /// literal is printed and how a parameter is declared.
    pub floats: BTreeSet<Location>,
}

impl<'a> Rebuilder<'a> {
    /// Prepare to rebuild, naming the values that need names.
    pub fn new(f: &'a SsaFunction) -> Rebuilder<'a> {
        let defs = f.definitions();
        let uses = use_counts(f);
        let mut locals = BTreeMap::new();
        let mut n = 0;
        // Values read more than once, and every phi, get a name. A phi is a
        // merge of paths and inlining it would mean writing the merge out at
        // each use.
        for (value, (block, index)) in &defs {
            let Some(op) = f.blocks.get(block).and_then(|b| b.ops.get(*index)) else {
                continue;
            };
            let multiple = uses.get(value).copied().unwrap_or(0) > 1;
            if multiple || op.kind == SsaKind::Phi {
                locals.insert(*value, format!("v{n}"));
                n += 1;
            }
        }
        Rebuilder {
            f,
            floats: float_locations(f),
            abi: r12e_ir::abi::of(&f.arch),
            defs,
            uses,
            locals,
        }
    }

    /// The expression for one operand.
    pub fn operand(&self, o: &Operand) -> Expr {
        match o {
            Operand::Const(v, s) => Expr::Const(*v, *s),
            Operand::Undefined(l) => Expr::Input(*l, input_name(*l, &self.abi)),
            Operand::Value(v) => {
                if let Some(name) = self.locals.get(v) {
                    return Expr::Local(name.clone());
                }
                match self.definition(*v) {
                    Some(op) => self.expr(op),
                    None => Expr::Input(v.location, input_name(v.location, &self.abi)),
                }
            }
        }
    }

    fn definition(&self, v: Value) -> Option<&'a SsaOp> {
        let (block, index) = self.defs.get(&v)?;
        self.f.blocks.get(block)?.ops.get(*index)
    }

    /// The expression one operation computes.
    pub fn expr(&self, op: &SsaOp) -> Expr {
        let SsaKind::Op(o) = op.kind else {
            // A phi always has a name, so reaching one here means the naming
            // missed it; say so rather than inventing a value.
            return Expr::Unknown("phi");
        };
        let a = || op.inputs.first().map(|i| self.operand(i)).unwrap_or(Expr::Unknown("missing"));
        let b = || op.inputs.get(1).map(|i| self.operand(i)).unwrap_or(Expr::Unknown("missing"));
        let bin = |sym: &'static str| Expr::Binary(sym, Box::new(a()), Box::new(b()));
        let signed_bin = |sym: &'static str| {
            // The width of what is being compared, which is not the width of
            // the answer: a comparison produces one byte.
            let width = op
                .inputs
                .first()
                .map(|i| i.size())
                .unwrap_or(op.size)
                .max(op.inputs.get(1).map(|i| i.size()).unwrap_or(0));
            let t = signed_type(width);
            Expr::Binary(
                sym,
                Box::new(Expr::Cast(t, Box::new(a()))),
                Box::new(Expr::Cast(t, Box::new(b()))),
            )
        };

        // An operand is read as whatever the operation consuming it expects.
        // A value the machine holds in a register has no type of its own, so
        // where the two disagree the reinterpretation is written down rather
        // than left for the C compiler to do something else with.
        let float_in = |e: Expr, o: &Operand| -> Expr {
            match o {
                Operand::Const(v, size) => Expr::FConst(*v, *size),
                Operand::Value(v) if !self.floats.contains(&v.location) => {
                    Expr::Named("__dbl", vec![e])
                }
                Operand::Undefined(l) if !self.floats.contains(l) => {
                    Expr::Named("__dbl", vec![e])
                }
                _ => e,
            }
        };
        let int_in = |e: Expr, o: &Operand| -> Expr {
            match o {
                Operand::Value(v) if self.floats.contains(&v.location) => {
                    Expr::Named("__bits", vec![e])
                }
                Operand::Undefined(l) if self.floats.contains(l) => {
                    Expr::Named("__bits", vec![e])
                }
                _ => e,
            }
        };

        // A literal consumed by a floating point operation is a number, not a
        // bit pattern, and printing it as one is the difference between `1.0`
        // and `0x3ff0000000000000`.
        let fa = || match op.inputs.first() {
            Some(o) => float_in(a(), o),
            None => a(),
        };
        let fb = || match op.inputs.get(1) {
            Some(o) => float_in(b(), o),
            None => b(),
        };
        let ia = || match op.inputs.first() {
            Some(o) => int_in(a(), o),
            None => a(),
        };
        let ib = || match op.inputs.get(1) {
            Some(o) => int_in(b(), o),
            None => b(),
        };
        let ibin = |sym: &'static str| Expr::Binary(sym, Box::new(ia()), Box::new(ib()));
        let fbin = |sym: &'static str| Expr::Binary(sym, Box::new(fa()), Box::new(fb()));

        match o {
            Op::Copy => a(),
            Op::Load => Expr::Deref(Box::new(a()), op.size),
            Op::IntAdd => bin("+"),
            Op::IntSub => bin("-"),
            Op::IntMul => bin("*"),
            Op::IntDiv => bin("/"),
            Op::IntRem => bin("%"),
            Op::IntSDiv => signed_bin("/"),
            Op::IntSRem => signed_bin("%"),
            Op::IntAnd => ibin("&"),
            Op::IntOr => ibin("|"),
            Op::IntXor => ibin("^"),
            Op::IntNot => Expr::Unary("~", Box::new(ia())),
            Op::IntNegate => Expr::Unary("-", Box::new(a())),
            Op::IntLeft => ibin("<<"),
            Op::IntRight => ibin(">>"),
            Op::IntSRight => signed_bin(">>"),
            Op::IntEqual => bin("=="),
            Op::IntNotEqual => bin("!="),
            Op::IntLess => bin("<"),
            Op::IntLessEqual => bin("<="),
            Op::IntSLess => signed_bin("<"),
            Op::IntSLessEqual => signed_bin("<="),
            Op::BoolAnd => bin("&&"),
            Op::BoolOr => bin("||"),
            Op::BoolXor => bin("^"),
            Op::BoolNot => Expr::Unary("!", Box::new(a())),
            Op::IntZExt => Expr::Cast(c_type(op.size), Box::new(a())),
            Op::IntSExt => Expr::Cast(signed_type(op.size), Box::new(a())),
            // A shift by a byte count, which is how a narrow read is expressed.
            Op::SubPiece => match op.inputs.get(1).and_then(|i| i.as_const()) {
                Some(0) => Expr::Cast(c_type(op.size), Box::new(a())),
                Some(n) => Expr::Cast(
                    c_type(op.size),
                    Box::new(Expr::Binary(
                        ">>",
                        Box::new(a()),
                        Box::new(Expr::Const(n * 8, 1)),
                    )),
                ),
                None => Expr::Unknown("subpiece"),
            },
            Op::CallInd => Expr::Named("__callind", vec![a()]),
            Op::Call => match op.inputs.first().and_then(|i| i.as_const()) {
                Some(target) => Expr::Call(target, Vec::new()),
                None => Expr::Unknown("call"),
            },
            Op::PopCount => Expr::Named("__popcount", vec![a()]),
            Op::IntMulHigh => Expr::Binary("__mulhi", Box::new(a()), Box::new(b())),
            Op::IntSMulHigh => Expr::Binary("__smulhi", Box::new(a()), Box::new(b())),
            // The double-width divides take their dividend in two halves,
            // which C has no notation for; the call form says so plainly.
            Op::IntDiv128 | Op::IntSDiv128 | Op::IntRem128 | Op::IntSRem128 => {
                let name = match o {
                    Op::IntDiv128 => "__udiv128",
                    Op::IntSDiv128 => "__sdiv128",
                    Op::IntRem128 => "__urem128",
                    _ => "__srem128",
                };
                Expr::Named(
                    name,
                    op.inputs.iter().map(|i| self.operand(i)).collect(),
                )
            }
            Op::FloatAdd => fbin("+"),
            Op::FloatSub => fbin("-"),
            Op::FloatMul => fbin("*"),
            Op::FloatDiv => fbin("/"),
            Op::FloatEqual => fbin("=="),
            Op::FloatNotEqual => fbin("!="),
            Op::FloatLess => fbin("<"),
            Op::FloatLessEqual => fbin("<="),
            Op::FloatNeg => Expr::Unary("-", Box::new(fa())),
            Op::FloatAbs => Expr::Named("__fabs", vec![a()]),
            Op::FloatSqrt => Expr::Named("__sqrt", vec![a()]),
            Op::FloatMax => Expr::Named("__fmax", vec![a(), b()]),
            Op::FloatMin => Expr::Named("__fmin", vec![a(), b()]),
            Op::FloatNan => Expr::Named("__isnan", vec![a()]),
            Op::FloatTrunc => Expr::Named("__trunc", vec![a()]),
            Op::FloatRound => Expr::Named("__rint", vec![a()]),
            Op::FloatCeil => Expr::Named("__ceil", vec![a()]),
            Op::FloatFloor => Expr::Named("__floor", vec![a()]),
            Op::FloatMulAdd => Expr::Named(
                "__fma",
                op.inputs
                    .iter()
                    .map(|i| match i {
                        Operand::Const(v, size) => Expr::FConst(*v, *size),
                        other => self.operand(other),
                    })
                    .collect(),
            ),
            Op::IntToFloat | Op::UIntToFloat => Expr::Cast(float_type(op.size), Box::new(ia())),
            Op::FloatToInt => Expr::Cast(signed_type(op.size), Box::new(fa())),
            Op::FloatToUInt => Expr::Cast(c_type(op.size), Box::new(fa())),
            Op::FloatConvert => Expr::Cast(float_type(op.size), Box::new(fa())),
            Op::LzCount => Expr::Named("__clz", vec![a()]),
            Op::IntCarry => Expr::Named("__carry", vec![a(), b()]),
            Op::IntSCarry => Expr::Named("__overflow", vec![a(), b()]),
            Op::IntSBorrow => Expr::Named("__borrow", vec![a(), b()]),
            Op::Piece => Expr::Unknown("piece"),
            Op::Unimplemented => Expr::Unknown("unmodelled"),
            _ => Expr::Unknown("op"),
        }
    }

    /// How many times a value is read.
    pub fn uses(&self, v: Value) -> usize {
        self.uses.get(&v).copied().unwrap_or(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn precedence_puts_parentheses_only_where_needed() {
        let a = Expr::Local("a".into());
        let b = Expr::Local("b".into());
        let c = Expr::Local("c".into());
        // Multiplication binds tighter, so no parentheses.
        let e = Expr::Binary(
            "+",
            Box::new(a.clone()),
            Box::new(Expr::Binary("*", Box::new(b.clone()), Box::new(c.clone()))),
        );
        assert_eq!(e.to_string(), "a + b * c");
        // Addition inside multiplication needs them.
        let e = Expr::Binary(
            "*",
            Box::new(Expr::Binary("+", Box::new(a.clone()), Box::new(b.clone()))),
            Box::new(c.clone()),
        );
        assert_eq!(e.to_string(), "(a + b) * c");
    }

    #[test]
    fn subtraction_is_not_reassociated_by_the_printer() {
        // `a - (b - c)` must keep its parentheses, or the output means
        // something else.
        let e = Expr::Binary(
            "-",
            Box::new(Expr::Local("a".into())),
            Box::new(Expr::Binary(
                "-",
                Box::new(Expr::Local("b".into())),
                Box::new(Expr::Local("c".into())),
            )),
        );
        assert_eq!(e.to_string(), "a - (b - c)");
    }

    #[test]
    fn constants_print_in_the_base_that_reads_better() {
        assert_eq!(Expr::Const(10, 8).to_string(), "10");
        assert_eq!(Expr::Const(0x4006e8, 8).to_string(), "0x4006e8");
        // A small negative at a narrow width is a number, not a huge mask.
        assert_eq!(Expr::Const(0xffff_ffff, 4).to_string(), "-1");
    }

    #[test]
    fn depth_counts_the_tree() {
        let e = Expr::Binary(
            "+",
            Box::new(Expr::Local("a".into())),
            Box::new(Expr::Binary(
                "*",
                Box::new(Expr::Local("b".into())),
                Box::new(Expr::Local("c".into())),
            )),
        );
        assert_eq!(e.depth(), 3);
    }
}
