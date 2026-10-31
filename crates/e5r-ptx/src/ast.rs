//! The PTX subset, one variant per supported form. It mirrors
//! `verification/ptx/Ptx/Syntax.lean` constructor for constructor; the only
//! extra information kept here is what the token round trip needs to print
//! the source back exactly (`.visible`, whether an address offset was
//! written).

/// Scalar types of the subset.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ty {
    /// `.u32`
    U32,
    /// `.s32`
    S32,
    /// `.b32`
    B32,
    /// `.u64`
    U64,
    /// `.s64`
    S64,
    /// `.b64`
    B64,
    /// `.pred`
    Pred,
}

impl Ty {
    /// The PTX spelling without the dot.
    pub fn name(self) -> &'static str {
        match self {
            Ty::U32 => "u32",
            Ty::S32 => "s32",
            Ty::B32 => "b32",
            Ty::U64 => "u64",
            Ty::S64 => "s64",
            Ty::B64 => "b64",
            Ty::Pred => "pred",
        }
    }

    /// Parse a spelling without the dot.
    pub fn from_name(s: &str) -> Option<Ty> {
        Some(match s {
            "u32" => Ty::U32,
            "s32" => Ty::S32,
            "b32" => Ty::B32,
            "u64" => Ty::U64,
            "s64" => Ty::S64,
            "b64" => Ty::B64,
            "pred" => Ty::Pred,
            _ => return None,
        })
    }

    /// Bit width, `None` for `.pred`.
    pub fn width(self) -> Option<u32> {
        match self {
            Ty::U32 | Ty::S32 | Ty::B32 => Some(32),
            Ty::U64 | Ty::S64 | Ty::B64 => Some(64),
            Ty::Pred => None,
        }
    }

    /// `.bN` types: only `eq`/`ne` comparisons are defined on them.
    pub fn is_bits(self) -> bool {
        matches!(self, Ty::B32 | Ty::B64)
    }
}

/// `.x`, `.y` or `.z`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dim {
    /// `.x`
    X,
    /// `.y`
    Y,
    /// `.z`
    Z,
}

/// The special registers of the subset.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sreg {
    /// `%tid`
    Tid(Dim),
    /// `%ntid`
    Ntid(Dim),
    /// `%ctaid`
    Ctaid(Dim),
    /// `%nctaid`
    Nctaid(Dim),
}

/// An instruction source operand.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operand {
    /// A declared register.
    Reg(String),
    /// An integer immediate, exactly as written.
    Imm(i128),
    /// A special register.
    Sreg(Sreg),
}

/// A memory operand. The offset is `None` when the source wrote none.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Address {
    /// `[%rd]` or `[%rd+off]`.
    Reg(String, Option<i128>),
    /// `[param]` or `[param+off]`.
    Param(String, Option<i128>),
}

/// `setp` comparison operators.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Lo,
    Ls,
    Hi,
    Hs,
}

impl CmpOp {
    /// The PTX spelling.
    pub fn name(self) -> &'static str {
        match self {
            CmpOp::Eq => "eq",
            CmpOp::Ne => "ne",
            CmpOp::Lt => "lt",
            CmpOp::Le => "le",
            CmpOp::Gt => "gt",
            CmpOp::Ge => "ge",
            CmpOp::Lo => "lo",
            CmpOp::Ls => "ls",
            CmpOp::Hi => "hi",
            CmpOp::Hs => "hs",
        }
    }

    /// Parse a spelling.
    pub fn from_name(s: &str) -> Option<CmpOp> {
        Some(match s {
            "eq" => CmpOp::Eq,
            "ne" => CmpOp::Ne,
            "lt" => CmpOp::Lt,
            "le" => CmpOp::Le,
            "gt" => CmpOp::Gt,
            "ge" => CmpOp::Ge,
            "lo" => CmpOp::Lo,
            "ls" => CmpOp::Ls,
            "hi" => CmpOp::Hi,
            "hs" => CmpOp::Hs,
            _ => return None,
        })
    }

    /// Ordered comparisons, which `.bN` types do not have.
    pub fn is_ordered(self) -> bool {
        !matches!(self, CmpOp::Eq | CmpOp::Ne)
    }
}

/// State spaces of `ld`/`st`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Space {
    /// `.global`
    Global,
    /// `.param`
    Param,
}

impl Space {
    /// The PTX spelling.
    pub fn name(self) -> &'static str {
        match self {
            Space::Global => "global",
            Space::Param => "param",
        }
    }
}

/// Binary operations that share one shape: `op.t d, a, b`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum BinOp {
    Add,
    Sub,
    MulLo,
    MulWide,
    And,
    Or,
    Xor,
    Shl,
    Shr,
}

impl BinOp {
    /// Opcode without the type suffix.
    pub fn opcode(self) -> &'static str {
        match self {
            BinOp::Add => "add",
            BinOp::Sub => "sub",
            BinOp::MulLo => "mul.lo",
            BinOp::MulWide => "mul.wide",
            BinOp::And => "and",
            BinOp::Or => "or",
            BinOp::Xor => "xor",
            BinOp::Shl => "shl",
            BinOp::Shr => "shr",
        }
    }

    /// Constructor name in `Ptx.Instr`.
    pub fn lean(self) -> &'static str {
        match self {
            BinOp::Add => "add",
            BinOp::Sub => "sub",
            BinOp::MulLo => "mulLo",
            BinOp::MulWide => "mulWide",
            BinOp::And => "and",
            BinOp::Or => "or",
            BinOp::Xor => "xor",
            BinOp::Shl => "shl",
            BinOp::Shr => "shr",
        }
    }
}

/// One instruction.
#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Instr {
    Bin(BinOp, Ty, String, Operand, Operand),
    MadLo(Ty, String, Operand, Operand, Operand),
    Not(Ty, String, Operand),
    Mov(Ty, String, Operand),
    Setp(CmpOp, Ty, String, Operand, Operand),
    Selp(Ty, String, Operand, Operand, String),
    Cvt(Ty, Ty, String, Operand),
    CvtaGlobal(String, Operand),
    Ld(Space, Ty, String, Address),
    St(Space, Ty, Address, Operand),
    Bra(bool, String),
    Ret,
    Exit,
}

/// `@%p` or `@!%p`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Guard {
    /// The predicate register.
    pub pred: String,
    /// `@!`.
    pub neg: bool,
}

/// A guarded instruction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stmt {
    /// The guard, if any.
    pub guard: Option<Guard>,
    /// The instruction.
    pub instr: Instr,
}

/// `.reg .t name<n>;` or `.reg .t name;`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegDecl {
    /// Declared type.
    pub ty: Ty,
    /// Name, or prefix when `count` is set.
    pub name: String,
    /// `<n>`: registers `name0 .. name{n-1}`.
    pub count: Option<u32>,
}

/// One `.entry`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Kernel {
    /// `.visible` was written.
    pub visible: bool,
    /// Entry name.
    pub name: String,
    /// Parameters, in order.
    pub params: Vec<(String, Ty)>,
    /// Register declarations, in order.
    pub regs: Vec<RegDecl>,
    /// Statements, in order.
    pub body: Vec<Stmt>,
    /// Each label and the index of the statement after it, in source order.
    pub labels: Vec<(String, usize)>,
}

/// A module: header directives and its kernels.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Module {
    /// `.version`, as written.
    pub version: String,
    /// `.target`.
    pub target: String,
    /// `.address_size`.
    pub address_size: u32,
    /// The kernels, in order.
    pub kernels: Vec<Kernel>,
}
