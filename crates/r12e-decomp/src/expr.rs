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

use r12e_ir::abi::Abi;
use r12e_ir::op::Op;
use r12e_ir::ssa::{Location, Operand, SsaFunction, SsaKind, SsaOp, Value};

use crate::emit::Prototype;

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
    /// A field of a structure reached through a pointer.
    Field(Box<Expr>, String),
    /// A field of one element of an array of structures.
    Element(Box<Expr>, Box<Expr>, String),
    /// A named operation C has no operator for.
    Named(&'static str, Vec<Expr>),
    /// A call to a function, named.
    Call(String, Vec<Expr>),
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
            Expr::Field(base, name) => {
                base.render(f, 12)?;
                write!(f, "->{name}")
            }
            Expr::Element(base, index, name) => {
                base.render(f, 12)?;
                f.write_str("[")?;
                index.render(f, 0)?;
                write!(f, "].{name}")
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
            Expr::Call(name, args) => {
                write!(f, "{name}(")?;
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
                // A signed cast of a constant C already gives that type is
                // noise. `(int32_t)81` and `81` convert identically in every
                // context, because a decimal literal is already `int` and the
                // usual arithmetic conversions then treat the two the same.
                // Only for values `int` can hold, and only for signed targets:
                // `(uint32_t)81` beside a signed operand chooses unsigned
                // division, which dropping it would silently change.
                if let Expr::Const(v, size) = a.as_ref()
                    && t.starts_with("int")
                    && (0..=0x7fff_ffff).contains(&sign_extend(*v, *size))
                {
                    return a.render(f, outer);
                }
                write!(f, "({t})")?;
                a.render(f, 11)
            }
            Expr::Unknown(what) => write!(f, "__{what}()"),
        }
    }
}

/// The C type for a size in bytes.
/// What to call a function whose name is not known.
pub fn default_call_name(target: u64) -> String {
    format!("sub_{target:x}")
}

/// The helper that reads a bit pattern as a number of this width.
pub fn reinterpret_to_float(size: u8) -> &'static str {
    if size == 4 { "__flt" } else { "__dbl" }
}

/// The helper that reads a number of this width as its bits.
pub fn reinterpret_to_bits(size: u8) -> &'static str {
    if size == 4 { "__bits32" } else { "__bits" }
}

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

/// How an address was built from an incoming pointer.
struct Walk {
    register: u64,
    offset: i64,
    index: Option<(Expr, u64)>,
}

/// What to call a field at an offset, since nothing named it.
pub fn field_name(offset: i64) -> String {
    if offset < 0 {
        format!("field_m{:x}", -offset)
    } else {
        format!("field_{offset:x}")
    }
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

/// Negate a condition without stacking `!` on something already negated.
pub fn negate(e: Expr) -> Expr {
    match e {
        Expr::Unary("!", inner) => *inner,
        Expr::Binary("==", a, b) => Expr::Binary("!=", a, b),
        Expr::Binary("!=", a, b) => Expr::Binary("==", a, b),
        Expr::Binary("<", a, b) => Expr::Binary(">=", a, b),
        Expr::Binary("<=", a, b) => Expr::Binary(">", a, b),
        Expr::Binary(">", a, b) => Expr::Binary("<=", a, b),
        Expr::Binary(">=", a, b) => Expr::Binary("<", a, b),
        other => Expr::Unary("!", Box::new(other)),
    }
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
    /// Names for incoming registers, from whatever knew better than the
    /// convention did.
    pub names: BTreeMap<u64, String>,
    /// Incoming registers whose declared type is a pointer. C scales
    /// arithmetic on those by the size of what they point at, and the machine
    /// has already done the scaling, so they are cast back to integers
    /// wherever they are used as addresses.
    pub pointers: BTreeSet<u64>,
    /// The declared width of an incoming register's value, which is not the
    /// width of the register: a `float` arrives in a sixteen-byte one.
    pub sizes: BTreeMap<u64, u8>,
    /// Fields seen through each incoming pointer, so an access at a known
    /// offset reads as the field it is rather than as arithmetic.
    pub fields: BTreeMap<u64, Vec<(i64, u8)>>,
    /// The element size of each of those, when the pointer walks an array.
    pub strides: BTreeMap<u64, u64>,
    /// What a declaration called the field at an offset, by pointer register.
    ///
    /// An offset missing from here is named after itself, which is how the
    /// output tells the two apart: `p->tag` is a name somebody wrote down and
    /// `p->field_8` is one this crate made up from the offset the code used.
    /// Nothing is lost by the fallback except the name, so a shape nobody
    /// declared still reads as a structure.
    pub field_names: BTreeMap<u64, BTreeMap<i64, String>>,
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
            // A call's result gets a name whether or not it is read twice: the
            // call is a statement, and inlining its result would write the
            // call out again and make it happen twice.
            let call = matches!(op.kind, SsaKind::Op(Op::Call) | SsaKind::Op(Op::CallInd));
            if multiple || call || op.kind == SsaKind::Phi {
                locals.insert(*value, format!("v{n}"));
                n += 1;
            }
        }
        Rebuilder {
            f,
            names: BTreeMap::new(),
            pointers: BTreeSet::new(),
            sizes: BTreeMap::new(),
            fields: BTreeMap::new(),
            strides: BTreeMap::new(),
            field_names: BTreeMap::new(),
            floats: float_locations(f),
            abi: r12e_ir::abi::of(&f.arch),
            defs,
            uses,
            locals,
        }
    }

    /// An expression read as an integer, whatever it was declared as.
    ///
    /// A floating value has to be reinterpreted, and a pointer has to be cast,
    /// because C scales arithmetic on a pointer and the machine already did.
    pub fn integer(&self, e: Expr, o: &Operand) -> Expr {
        let location = match o {
            Operand::Value(v) => Some(v.location),
            Operand::Undefined(l) => Some(*l),
            Operand::Const(..) => None,
        };
        let Some(l) = location else { return e };
        // A value a floating point operation produced is a number whatever
        // location it landed in: the conversion ops write one into a register
        // this pass has no other reason to call floating.
        if !self.floats.contains(&l) && self.produces_float(o) {
            let size = match o {
                Operand::Value(v) => v.location.size,
                _ => l.size,
            };
            return Expr::Named(reinterpret_to_bits(size.min(8)), vec![e]);
        }
        if self.floats.contains(&l) {
            let size = if l.space == r12e_ir::op::Space::Register {
                self.sizes.get(&l.offset).copied().unwrap_or(l.size)
            } else {
                l.size
            };
            return Expr::Named(reinterpret_to_bits(size), vec![e]);
        }
        if l.space == r12e_ir::op::Space::Register && self.pointers.contains(&l.offset) {
            return Expr::Cast("uint64_t", Box::new(e));
        }
        e
    }

    /// The field an address names, when it is a known offset from a pointer
    /// whose shape was recovered.
    ///
    /// Only a constant offset from the pointer itself: anything with an index
    /// in it is walking an array, and calling that a field would be wrong.
    pub fn field_access(&self, address: Option<&Operand>, size: u8) -> Option<Expr> {
        let walk = self.pointer_offset(address?, 0)?;
        let shape = self.fields.get(&walk.register)?;
        let (at, width) = shape.iter().find(|(at, _)| *at == walk.offset)?;
        if *width != size {
            return None;
        }
        let name = self.names.get(&walk.register).cloned()?;
        let base = Expr::Input(
            Location {
                space: r12e_ir::op::Space::Register,
                offset: walk.register,
                size: 8,
            },
            name,
        );
        let field = self.field_label(walk.register, *at);
        match walk.index {
            // An index scaled by the element size is an array subscript; one
            // scaled by anything else is arithmetic this does not understand.
            Some((index, scale)) if self.strides.get(&walk.register) == Some(&scale) => {
                Some(Expr::Element(Box::new(base), Box::new(index), field))
            }
            Some(_) => None,
            None => Some(Expr::Field(Box::new(base), field)),
        }
    }

    /// What to call the field at an offset through one incoming pointer.
    ///
    /// The declared name when a declaration gave one, and otherwise a name
    /// built from the offset, which says on its face that nothing declared it.
    fn field_label(&self, register: u64, offset: i64) -> String {
        self.field_names
            .get(&register)
            .and_then(|m| m.get(&offset))
            .cloned()
            .unwrap_or_else(|| field_name(offset))
    }

    /// An address written as an incoming register, a constant, and at most one
    /// scaled index.
    fn pointer_offset(&self, o: &Operand, depth: u32) -> Option<Walk> {
        if depth > 8 {
            return None;
        }
        match o {
            Operand::Undefined(l) if l.space == r12e_ir::op::Space::Register => Some(Walk {
                register: l.offset,
                offset: 0,
                index: None,
            }),
            Operand::Value(v) => {
                let op = self.definition(*v)?;
                let SsaKind::Op(kind) = op.kind else {
                    return None;
                };
                match kind {
                    Op::Copy => self.pointer_offset(op.inputs.first()?, depth + 1),
                    Op::IntAdd => {
                        let (a, b) = (op.inputs.first()?, op.inputs.get(1)?);
                        if let Some(k) = b.as_const() {
                            let mut walk = self.pointer_offset(a, depth + 1)?;
                            walk.offset += k as i64;
                            return Some(walk);
                        }
                        // One side is the pointer and the other a scaled index.
                        let (base, other) = match self.pointer_offset(a, depth + 1) {
                            Some(w) => (w, b),
                            None => (self.pointer_offset(b, depth + 1)?, a),
                        };
                        if base.index.is_some() {
                            return None;
                        }
                        let (index, scale) = self.scaled(other)?;
                        Some(Walk {
                            index: Some((index, scale)),
                            ..base
                        })
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// An index multiplied by a constant, however it was written.
    fn scaled(&self, o: &Operand) -> Option<(Expr, u64)> {
        let Operand::Value(v) = o else { return None };
        let op = self.definition(*v)?;
        let SsaKind::Op(kind) = op.kind else {
            return None;
        };
        match kind {
            Op::IntLeft => {
                let n = op.inputs.get(1)?.as_const()?;
                if n >= 32 {
                    return None;
                }
                Some((self.operand(op.inputs.first()?), 1u64 << n))
            }
            Op::IntMul => {
                let n = op.inputs.get(1)?.as_const()?;
                Some((self.operand(op.inputs.first()?), n))
            }
            Op::Copy | Op::IntSExt | Op::IntZExt => self.scaled(op.inputs.first()?),
            _ => None,
        }
    }

    /// True when an operand holds a value a floating point operation made.
    fn produces_float(&self, o: &Operand) -> bool {
        let Operand::Value(v) = o else { return false };
        let Some(op) = self.definition(*v) else {
            return false;
        };
        let SsaKind::Op(kind) = op.kind else {
            return false;
        };
        is_float_op(kind) && !produces_bool(kind)
    }

    /// What to call a value that arrived from outside.
    pub fn name_of(&self, l: Location) -> String {
        if l.space == r12e_ir::op::Space::Register {
            if let Some(name) = self.names.get(&l.offset) {
                return name.clone();
            }
        }
        input_name(l, &self.abi)
    }

    /// The expression for one operand.
    pub fn operand(&self, o: &Operand) -> Expr {
        match o {
            Operand::Const(v, s) => Expr::Const(*v, *s),
            Operand::Undefined(l) => Expr::Input(*l, self.name_of(*l)),
            Operand::Value(v) => {
                if let Some(name) = self.locals.get(v) {
                    return Expr::Local(name.clone());
                }
                match self.definition(*v) {
                    Some(op) => self.expr(op),
                    None => Expr::Input(v.location, self.name_of(v.location)),
                }
            }
        }
    }

    /// Where a value is defined: which block, and which operation in it.
    pub fn definition_site(&self, v: Value) -> Option<(r12e_core::Addr, usize)> {
        self.defs.get(&v).copied()
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
        let a = || {
            op.inputs
                .first()
                .map(|i| self.operand(i))
                .unwrap_or(Expr::Unknown("missing"))
        };
        let b = || {
            op.inputs
                .get(1)
                .map(|i| self.operand(i))
                .unwrap_or(Expr::Unknown("missing"))
        };
        let bin = |sym: &'static str| Expr::Binary(sym, Box::new(a()), Box::new(b()));
        let signed_at = |width: u8, sym: &'static str| {
            let t = signed_type(width);
            Expr::Binary(
                sym,
                Box::new(Expr::Cast(t, Box::new(a()))),
                Box::new(Expr::Cast(t, Box::new(b()))),
            )
        };
        // A comparison's answer is one byte whatever it compared, so its width
        // comes from the operands. Signed arithmetic's answer is as wide as
        // the operation, and its operands are read at that width however wide
        // the location holding them is.
        let compared = |sym: &'static str| {
            let width = op
                .inputs
                .first()
                .map(|i| i.size())
                .unwrap_or(op.size)
                .max(op.inputs.get(1).map(|i| i.size()).unwrap_or(0));
            signed_at(width, sym)
        };
        let signed_bin = |sym: &'static str| signed_at(op.size, sym);

        // An operand is read as whatever the operation consuming it expects.
        // A value the machine holds in a register has no type of its own, so
        // where the two disagree the reinterpretation is written down rather
        // than left for the C compiler to do something else with.
        // The width the operation works at, which is what a literal operand
        // means whatever width it was stored as.
        let width = op
            .inputs
            .first()
            .map(|i| i.size())
            .filter(|s| *s == 4 || *s == 8)
            .unwrap_or(op.size);
        let float_in = |e: Expr, o: &Operand| -> Expr {
            match o {
                Operand::Const(v, _) => Expr::FConst(*v, width),
                Operand::Value(v) if !self.floats.contains(&v.location) => {
                    Expr::Named(reinterpret_to_float(width), vec![e])
                }
                Operand::Undefined(l) if !self.floats.contains(l) => {
                    Expr::Named(reinterpret_to_float(width), vec![e])
                }
                _ => e,
            }
        };
        let int_in = |e: Expr, o: &Operand| -> Expr { self.integer(e, o) };

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
        // The width of the operand an extension reads, which is the width it
        // extends from.
        let input_width = op.inputs.first().map(|i| i.size()).unwrap_or(op.size);
        let ibin = |sym: &'static str| Expr::Binary(sym, Box::new(ia()), Box::new(ib()));
        let fbin = |sym: &'static str| Expr::Binary(sym, Box::new(fa()), Box::new(fb()));

        match o {
            // A copy of a value whose declared type is not an integer still
            // lands in an integer local, so the conversion is written down.
            Op::Copy => ia(),
            Op::Load => match self.field_access(op.inputs.first(), op.size) {
                Some(field) => field,
                None => Expr::Deref(Box::new(ia()), op.size),
            },
            Op::IntAdd => ibin("+"),
            Op::IntSub => ibin("-"),
            Op::IntMul => ibin("*"),
            Op::IntDiv => ibin("/"),
            Op::IntRem => ibin("%"),
            Op::IntSDiv => signed_bin("/"),
            Op::IntSRem => signed_bin("%"),
            Op::IntAnd => ibin("&"),
            Op::IntOr => ibin("|"),
            Op::IntXor => ibin("^"),
            Op::IntNot => Expr::Unary("~", Box::new(ia())),
            Op::IntNegate => Expr::Unary("-", Box::new(ia())),
            Op::IntLeft => ibin("<<"),
            Op::IntRight => ibin(">>"),
            Op::IntSRight => signed_bin(">>"),
            Op::IntEqual => ibin("=="),
            Op::IntNotEqual => ibin("!="),
            Op::IntLess => ibin("<"),
            Op::IntLessEqual => ibin("<="),
            Op::IntSLess => compared("<"),
            Op::IntSLessEqual => compared("<="),
            Op::BoolAnd => bin("&&"),
            Op::BoolOr => bin("||"),
            Op::BoolXor => bin("^"),
            // A negated comparison is the opposite comparison, which is what
            // the source said before the machine turned it into flags.
            Op::BoolNot => negate(a()),
            // Both extensions name the width they extend *from* as well as
            // the one they extend to. Every local is declared at its whole
            // register's width, so without the inner cast the bits above the
            // source's width come along and the extension does nothing.
            Op::IntZExt => Expr::Cast(
                c_type(op.size),
                Box::new(Expr::Cast(c_type(input_width), Box::new(ia()))),
            ),
            Op::IntSExt => Expr::Cast(
                signed_type(op.size),
                Box::new(Expr::Cast(signed_type(input_width), Box::new(ia()))),
            ),
            // A shift by a byte count, which is how a narrow read is expressed.
            Op::SubPiece => match op.inputs.get(1).and_then(|i| i.as_const()) {
                Some(0) => Expr::Cast(c_type(op.size), Box::new(ia())),
                Some(n) => Expr::Cast(
                    c_type(op.size),
                    Box::new(Expr::Binary(
                        ">>",
                        Box::new(ia()),
                        Box::new(Expr::Const(n * 8, 1)),
                    )),
                ),
                None => Expr::Unknown("subpiece"),
            },
            Op::CallInd => Expr::Named("__callind", vec![ia()]),
            Op::Call => match op.inputs.first().and_then(|i| i.as_const()) {
                Some(target) => Expr::Call(default_call_name(target), Vec::new()),
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
                Expr::Named(name, op.inputs.iter().map(|i| self.operand(i)).collect())
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
            Op::Undefine => Expr::Unknown("clobbered"),
            Op::Unimplemented => Expr::Unknown("unmodelled"),
            _ => Expr::Unknown("op"),
        }
    }

    /// How many times a value is read.
    pub fn uses(&self, v: Value) -> usize {
        self.uses.get(&v).copied().unwrap_or(0)
    }

    /// Wire in what a prototype says about the values arriving from outside.
    ///
    /// A declared parameter arrives in a register the convention chooses, so
    /// once the declaration is laid over the convention the body can use the
    /// name, the width and the fields the declaration gave rather than the
    /// register it happened to come in.
    pub fn declare(&mut self, p: &Prototype) {
        let (mut ints, mut floats) = (0usize, 0usize);
        for param in &p.parameters {
            let offset = if param.floating {
                let o = self.abi.float_arguments.get(floats).copied();
                floats += 1;
                o
            } else {
                let o = self.abi.integer_arguments.get(ints).copied();
                ints += 1;
                o
            };
            let Some(o) = offset else { continue };
            self.names.insert(o, param.name.clone());
            if param.pointer {
                self.pointers.insert(o);
            }
            if param.size > 0 {
                self.sizes.insert(o, param.size);
            }
            if !param.fields.is_empty() {
                self.fields.insert(o, param.fields.clone());
                if let Some(stride) = param.stride {
                    self.strides.insert(o, stride);
                }
            }
            // A parameter declared floating is floating even when nothing in
            // the body does arithmetic on it: at O0 it is stored to the stack
            // before anything touches it.
            if param.floating {
                self.floats.insert(Location {
                    space: r12e_ir::op::Space::Register,
                    offset: o,
                    size: 8,
                });
            }
        }
    }

    /// The type the body declares a value of this location with.
    fn type_of(&self, l: Location) -> &'static str {
        if self.floats.contains(&l) {
            float_type(l.size)
        } else {
            c_type(l.size)
        }
    }
}

/// Where the machine kept a variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Home {
    /// A register, by its offset in the register file.
    Register(u64),
    /// A slot at this offset from the stack pointer on entry, which is what a
    /// frame offset means once the stack has been promoted.
    Stack(i64),
    /// Somewhere the rebuilder did not have to name: a value that exists only
    /// between the operation that made it and the one that reads it.
    Anywhere,
}

/// What a variable is to the function that declares it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Role {
    /// Something the caller passed.
    Parameter,
    /// Something the body computes and names.
    Local,
    /// A register or slot read before anything in this function wrote it,
    /// which the convention does not pass arguments in either. Neither a
    /// parameter nor anything this function made.
    Inherited,
}

/// One variable a decompiled function declares.
///
/// The count of these is not a fact anything can be checked against: matching
/// what was recovered to what the source declared needs the name, the type and
/// where the value lived.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Variable {
    /// What the body calls it.
    pub name: String,
    /// Its type, as the declaration spells it.
    pub ty: String,
    /// Its width in bytes, zero when nothing said.
    pub size: u8,
    /// Parameter, local, or inherited.
    pub role: Role,
    /// Where the machine kept it.
    pub home: Home,
}

/// Every variable one decompiled function declares.
///
/// Rebuilt from the same SSA and the same prototype the emitter used, so these
/// are the names that appear in its text rather than a second opinion. `body`
/// is that text: an inherited register every optimization removed is declared
/// by neither, and whether the text mentions it is how the emitter decides.
pub fn variables(f: &SsaFunction, prototype: Option<&Prototype>, body: &str) -> Vec<Variable> {
    let mut r = Rebuilder::new(f);
    if let Some(p) = prototype {
        r.declare(p);
    }
    let r = r;

    let mut out: Vec<Variable> = Vec::new();
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut push = |out: &mut Vec<Variable>, v: Variable| {
        if seen.insert(v.name.clone()) {
            out.push(v);
        }
    };

    // Parameters in the order the declaration gives them, which is the order
    // they appear in the signature.
    match prototype.filter(|p| !p.parameters.is_empty()) {
        Some(p) => {
            let (mut ints, mut floats) = (0usize, 0usize);
            for param in &p.parameters {
                let offset = if param.floating {
                    let o = r.abi.float_arguments.get(floats).copied();
                    floats += 1;
                    o
                } else {
                    let o = r.abi.integer_arguments.get(ints).copied();
                    ints += 1;
                    o
                };
                push(
                    &mut out,
                    Variable {
                        ty: declared_type(&param.decl, &param.name),
                        name: param.name.clone(),
                        size: param.size,
                        role: Role::Parameter,
                        home: offset.map_or(Home::Anywhere, Home::Register),
                    },
                );
            }
        }
        // Nothing declared anything: the convention's argument registers that
        // arrive with values are the parameters, in the convention's order.
        None => {
            let order: Vec<u64> = r
                .abi
                .integer_arguments
                .iter()
                .chain(r.abi.float_arguments.iter())
                .copied()
                .collect();
            let mut by_slot: BTreeMap<usize, Variable> = BTreeMap::new();
            for l in undefined(f) {
                let name = r.name_of(l);
                let slot = if l.space == r12e_ir::op::Space::Register {
                    order.iter().position(|o| *o == l.offset)
                } else if is_stack_argument(l) {
                    Some(order.len() + l.offset as usize)
                } else {
                    None
                };
                let Some(slot) = slot else { continue };
                by_slot.entry(slot).or_insert(Variable {
                    name,
                    ty: r.type_of(l).to_string(),
                    size: l.size,
                    role: Role::Parameter,
                    home: home_of(l),
                });
            }
            for v in by_slot.into_values() {
                push(&mut out, v);
            }
        }
    }

    // Registers and slots the function inherited: declared by the emitter only
    // where the body still mentions them.
    let parameters: BTreeSet<String> = out.iter().map(|v| v.name.clone()).collect();
    for l in undefined(f) {
        let name = r.name_of(l);
        if parameters.contains(&name) || !mentions(body, &name) {
            continue;
        }
        push(
            &mut out,
            Variable {
                name,
                ty: r.type_of(l).to_string(),
                size: l.size,
                role: Role::Inherited,
                home: home_of(l),
            },
        );
    }

    for (value, name) in &r.locals {
        push(
            &mut out,
            Variable {
                name: name.clone(),
                ty: r.type_of(value.location).to_string(),
                size: value.location.size,
                role: Role::Local,
                home: home_of(value.location),
            },
        );
    }
    out
}

/// Every location read before anything in the function wrote it.
fn undefined(f: &SsaFunction) -> Vec<Location> {
    let mut out = Vec::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            for i in &op.inputs {
                if let Operand::Undefined(l) = i {
                    out.push(*l);
                }
            }
        }
    }
    out
}

/// Where a location lives, in the terms a reader of the output cares about.
fn home_of(l: Location) -> Home {
    match l.space {
        r12e_ir::op::Space::Register => Home::Register(l.offset),
        r12e_ir::op::Space::Stack => Home::Stack(l.offset as i64),
        _ => Home::Anywhere,
    }
}

/// The type half of a declaration.
///
/// C wraps the type around the name rather than putting the two side by side,
/// so this is a removal and not a split: `struct Point *p` is a `struct Point
/// *` and `int (*f)(int)` is an `int (*)(int)`.
pub fn declared_type(decl: &str, name: &str) -> String {
    let Some(at) = word(decl, name) else {
        return decl.trim().to_string();
    };
    let (head, tail) = (&decl[..at], &decl[at + name.len()..]);
    let joined = format!("{}{tail}", head.trim_end());
    joined.trim().to_string()
}

/// Where a name appears in a text as a whole word, last occurrence first.
fn word(text: &str, name: &str) -> Option<usize> {
    if name.is_empty() {
        return None;
    }
    let mut found = None;
    let mut at = 0;
    while let Some(next) = text[at..].find(name) {
        let start = at + next;
        let end = start + name.len();
        let part = |c: Option<char>| c.is_some_and(|c| c.is_alphanumeric() || c == '_');
        if !part(text[..start].chars().next_back()) && !part(text[end..].chars().next()) {
            found = Some(start);
        }
        at = end;
    }
    found
}

/// True when a name appears in a text as a whole word.
pub fn mentions(text: &str, name: &str) -> bool {
    word(text, name).is_some()
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
