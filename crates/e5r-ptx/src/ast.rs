//! The PTX subset, one variant per supported form. It mirrors
//! `verification/ptx/Ptx/Syntax.lean` constructor for constructor; the only
//! extra information kept here is what the token round trip needs to print
//! the source back exactly (`.visible`, whether an address offset was
//! written).

/// Scalar types of the subset.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ty {
    /// `.u8`, admitted only for unsigned loads and stores.
    U8,
    /// `.u16`
    U16,
    /// `.s16`
    S16,
    /// `.b16`
    B16,
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
    /// `.f32`
    F32,
    /// `.f64`
    F64,
}

impl Ty {
    /// The PTX spelling without the dot.
    pub fn name(self) -> &'static str {
        match self {
            Ty::U8 => "u8",
            Ty::U16 => "u16",
            Ty::S16 => "s16",
            Ty::B16 => "b16",
            Ty::U32 => "u32",
            Ty::S32 => "s32",
            Ty::B32 => "b32",
            Ty::U64 => "u64",
            Ty::S64 => "s64",
            Ty::B64 => "b64",
            Ty::Pred => "pred",
            Ty::F32 => "f32",
            Ty::F64 => "f64",
        }
    }

    /// Parse a spelling without the dot.
    pub fn from_name(s: &str) -> Option<Ty> {
        Some(match s {
            "u8" => Ty::U8,
            "u16" => Ty::U16,
            "s16" => Ty::S16,
            "b16" => Ty::B16,
            "u32" => Ty::U32,
            "s32" => Ty::S32,
            "b32" => Ty::B32,
            "u64" => Ty::U64,
            "s64" => Ty::S64,
            "b64" => Ty::B64,
            "pred" => Ty::Pred,
            "f32" => Ty::F32,
            "f64" => Ty::F64,
            _ => return None,
        })
    }

    /// Bit width, `None` for `.pred`.
    pub fn width(self) -> Option<u32> {
        match self {
            Ty::U8 => Some(8),
            Ty::U16 | Ty::S16 | Ty::B16 => Some(16),
            Ty::U32 | Ty::S32 | Ty::B32 | Ty::F32 => Some(32),
            Ty::U64 | Ty::S64 | Ty::B64 | Ty::F64 => Some(64),
            Ty::Pred => None,
        }
    }

    /// `.bN` types: only `eq`/`ne` comparisons are defined on them.
    pub fn is_bits(self) -> bool {
        matches!(self, Ty::B16 | Ty::B32 | Ty::B64)
    }

    /// `.f32` and `.f64`.
    pub fn is_float(self) -> bool {
        matches!(self, Ty::F32 | Ty::F64)
    }

    /// Integer types admitted for floating-point conversions (32/64 bits).
    pub fn is_int(self) -> bool {
        matches!(self, Ty::U32 | Ty::S32 | Ty::U64 | Ty::S64)
    }

    /// The floating-point format of `.f32`/`.f64`.
    pub fn fmt(self) -> crate::fp::Fmt {
        if self == Ty::F64 {
            crate::fp::F64
        } else {
            crate::fp::F32
        }
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
    /// The address of a `.shared` variable (only in `mov`).
    Sym(String),
    /// A floating-point literal by its bits: `0fXXXXXXXX` (width 32) or
    /// `0dXXXXXXXXXXXXXXXX` (width 64).
    FImm(u64, u32),
}

/// A memory operand. The offset is `None` when the source wrote none.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Address {
    /// `[%rd]` or `[%rd+off]`.
    Reg(String, Option<i128>),
    /// `[name]` or `[name+off]`: a parameter (`ld.param`) or a `.shared`
    /// variable.
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

/// State spaces of `ld`/`st`/`atom`/`red`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Space {
    /// `.global`
    Global,
    /// `.param`
    Param,
    /// `.shared`
    Shared,
}

impl Space {
    /// The PTX spelling.
    pub fn name(self) -> &'static str {
        match self {
            Space::Global => "global",
            Space::Param => "param",
            Space::Shared => "shared",
        }
    }
}

/// Operations of `atom` and `red`; `cas` is its own instruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum AtomOp {
    Add,
    Min,
    Max,
    Exch,
    And,
    Or,
    Xor,
}

impl AtomOp {
    /// The PTX spelling, which is also the Lean constructor name.
    pub fn name(self) -> &'static str {
        match self {
            AtomOp::Add => "add",
            AtomOp::Min => "min",
            AtomOp::Max => "max",
            AtomOp::Exch => "exch",
            AtomOp::And => "and",
            AtomOp::Or => "or",
            AtomOp::Xor => "xor",
        }
    }

    /// Parse a spelling.
    pub fn from_name(s: &str) -> Option<AtomOp> {
        Some(match s {
            "add" => AtomOp::Add,
            "min" => AtomOp::Min,
            "max" => AtomOp::Max,
            "exch" => AtomOp::Exch,
            "and" => AtomOp::And,
            "or" => AtomOp::Or,
            "xor" => AtomOp::Xor,
            _ => return None,
        })
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

/// `add sub mul div` on `.f32`/`.f64`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum FBin {
    Add,
    Sub,
    Mul,
    Div,
}

impl FBin {
    /// The PTX spelling, which is also the Lean constructor.
    pub fn name(self) -> &'static str {
        match self {
            FBin::Add => "add",
            FBin::Sub => "sub",
            FBin::Mul => "mul",
            FBin::Div => "div",
        }
    }
}

pub use crate::fp::{FCmp, RMode};

impl RMode {
    /// `rn rz rm rp`, the Lean constructor too.
    pub fn name(self) -> &'static str {
        match self {
            RMode::Rn => "rn",
            RMode::Rz => "rz",
            RMode::Rm => "rm",
            RMode::Rp => "rp",
        }
    }
    /// Parse `rn rz rm rp`.
    pub fn from_name(s: &str) -> Option<RMode> {
        Some(match s {
            "rn" => RMode::Rn,
            "rz" => RMode::Rz,
            "rm" => RMode::Rm,
            "rp" => RMode::Rp,
            _ => return None,
        })
    }
}

/// The rounding of a `cvt` with a floating-point side.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CvtRnd {
    /// None written (`cvt.f64.f32`).
    None,
    /// `.rn .rz .rm .rp`
    F(RMode),
    /// `.rni .rzi .rmi .rpi`
    I(RMode),
}

/// One instruction.
#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Instr {
    /// `or.pred d, a, b`: logical OR of predicate registers.
    Por(String, String, String),
    Bin(BinOp, Ty, String, Operand, Operand),
    MadLo(Ty, String, Operand, Operand, Operand),
    /// bfi.b32 with immediate position + length <= 32 only.
    Bfi32(String, Operand, Operand, u8, u8),
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
    /// `atom.sp.op.t d, [a], b`
    Atom(Space, AtomOp, Ty, String, Address, Operand),
    /// `atom.sp.cas.t d, [a], b, c`
    Cas(Space, Ty, String, Address, Operand, Operand),
    /// `red.sp.op.t [a], b`
    Red(Space, AtomOp, Ty, Address, Operand),
    /// `bar.sync 0`
    Bar,
    /// `op.rnd{.ftz}{.sat}.t d, a, b` (`Ptx.Instr.fbin`)
    FBin(FBin, RMode, bool, bool, Ty, String, Operand, Operand),
    /// `fma.rnd{.ftz}{.sat}.t d, a, b, c`
    Ffma(RMode, bool, bool, Ty, String, Operand, Operand, Operand),
    /// `sqrt.rnd{.ftz}.t d, a`
    Fsqrt(RMode, bool, Ty, String, Operand),
    /// `rcp.rnd{.ftz}.t d, a`
    Frcp(RMode, bool, Ty, String, Operand),
    /// `neg{.ftz}.t d, a`
    Fneg(bool, Ty, String, Operand),
    /// `abs{.ftz}.t d, a`
    Fabs(bool, Ty, String, Operand),
    /// `min`/`max{.ftz}{.NaN}.t d, a, b`: (is max, ftz, NaN)
    Fminmax(bool, bool, bool, Ty, String, Operand, Operand),
    /// `setp.cmp{.ftz}.t p, a, b`
    Fsetp(FCmp, bool, Ty, String, Operand, Operand),
    /// `cvt{.rnd}{.ftz}{.sat}.dt.st d, a` with a floating-point side
    CvtF(Ty, Ty, CvtRnd, bool, bool, String, Operand),
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

/// `.shared {.align a} .t name{[n]};`. The element type is kept as written
/// (`b8`, `u32`, ...) for the round trip; the model only needs the size and
/// the alignment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SharedDecl {
    /// `.align a`, if written.
    pub align: Option<u32>,
    /// Element type, without the dot: `b8 u8 s8 b16 u16 s16` or a [`Ty`].
    pub elem: String,
    /// Name.
    pub name: String,
    /// `[n]`, if an array.
    pub count: Option<u32>,
}

impl SharedDecl {
    /// Bytes per element of a shared element type, `None` if not supported.
    pub fn elem_bytes(elem: &str) -> Option<u32> {
        match elem {
            "b8" | "u8" | "s8" => Some(1),
            "b16" | "u16" | "s16" => Some(2),
            "b32" | "u32" | "s32" => Some(4),
            "b64" | "u64" | "s64" => Some(8),
            _ => None,
        }
    }

    /// Size in bytes.
    pub fn size(&self) -> u64 {
        Self::elem_bytes(&self.elem).unwrap_or(1) as u64 * self.count.unwrap_or(1) as u64
    }

    /// Alignment in bytes: as written, or the element size.
    pub fn alignment(&self) -> u32 {
        self.align
            .unwrap_or_else(|| Self::elem_bytes(&self.elem).unwrap_or(1))
    }
}

/// A declaration at the head of a kernel body, in source order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Decl {
    /// Index into [`Kernel::regs`].
    Reg(usize),
    /// Index into [`Kernel::shared`].
    Shared(usize),
}

/// A byte-array kernel argument passed by value, with its declared alignment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AggregateParam {
    /// Parameter symbol.
    pub name: String,
    /// Declared alignment in bytes.
    pub align: u32,
    /// Declared byte-array length.
    pub size: u32,
}

/// Parameter declaration order, including aggregate arguments passed by value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParamDecl {
    /// Index into [`Kernel::params`].
    Scalar(usize),
    /// Index into [`Kernel::aggregate_params`].
    Aggregate(usize),
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
    /// Explicit byte-array arguments, without flattening their ABI.
    pub aggregate_params: Vec<AggregateParam>,
    /// The order scalar and aggregate parameters were declared.
    pub param_decls: Vec<ParamDecl>,
    /// Register declarations, in order.
    pub regs: Vec<RegDecl>,
    /// `.shared` variable declarations, in order.
    pub shared: Vec<SharedDecl>,
    /// The order the declarations were written in.
    pub decls: Vec<Decl>,
    /// Statements, in order.
    pub body: Vec<Stmt>,
    /// Each label and the index of the statement after it, in source order.
    pub labels: Vec<(String, usize)>,
}

/// One statically sized global definition with its exact load-time bytes.
/// Relocations, extern storage and partial initializer lists are not admitted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlobalDecl {
    /// Module-scoped symbol.
    pub name: String,
    /// Declared byte alignment.
    pub align: u32,
    /// Little-endian initializer bytes, including implicit zero initialization.
    pub bytes: Vec<u8>,
}

/// A module: header directives and its kernels.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Module {
    /// Global load image; symbol placement and allocation are launch preconditions.
    pub globals: Vec<GlobalDecl>,
    /// Validated non-executable directives and global declaration spellings,
    /// indexed by preceding core-token count. Global tokens/initializers are
    /// preserved separately from the structured load image.
    pub metadata: Vec<(usize, String)>,
    /// `.version`, as written.
    pub version: String,
    /// `.target`.
    pub target: String,
    /// `.address_size`.
    pub address_size: u32,
    /// The kernels, in order.
    pub kernels: Vec<Kernel>,
}

impl Module {
    /// Whether a kernel materializes a declared module-global address. In the
    /// admitted grammar, symbol operands occur only in mov; named global
    /// memory operands and relocation expressions remain outside the subset.
    /// Legacy proof domains must refuse these kernels until they bind a module
    /// placement/initializer contract, rather than default symbols to zero.
    pub fn uses_globals(&self, kernel: &Kernel) -> bool {
        kernel.body.iter().any(|s| {
            matches!(&s.instr, Instr::Mov(_, _, Operand::Sym(name))
                if self.globals.iter().any(|g| g.name == *name))
        })
    }
}
