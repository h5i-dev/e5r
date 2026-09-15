//! The in-memory model a decode engine runs against.
//!
//! This is the whole public surface of the front end. It is deliberately flat:
//! everything lives in an arena on [`Spec`] and is referred to by a small
//! index type, so a decoder can hold a `&Spec` and copy identifiers around
//! without lifetimes or reference counting. Nothing here borrows from the
//! source text.
//!
//! The shape a decoder is expected to use:
//!
//! 1. Start at [`Spec::root`], the `instruction` table.
//! 2. For each [`Constructor`] in the table, test [`Constructor::resolved`]
//!    against the instruction bytes and the context register. That test is a
//!    byte mask compare and is the fast path.
//! 3. If [`ResolvedPattern::approximation`] is set, or the alternative carries
//!    [`PatternAlt::residual`] constraints, also evaluate
//!    [`Constructor::pattern`], which is the pattern exactly as written.
//! 4. On a match, walk [`Constructor::operands`]. Each one names either a
//!    token field to extract at a known byte offset, a context field, a
//!    register, a subtable to recurse into, or a value the disassembly action
//!    section computes.
//! 5. Render with [`Constructor::display`] and lift with
//!    [`Constructor::body`].

use std::collections::HashMap;

use crate::error::Location;

/// Byte order, for the specification and for individual tokens.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Endian {
    /// Most significant byte first.
    Big,
    /// Least significant byte first. The default only matters before a
    /// specification has said, which the language requires it to do first.
    #[default]
    Little,
}

/// What an address space models.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpaceKind {
    /// Addressable read/write memory in the processor's map.
    Ram,
    /// The processor's registers: read/write, but not pointer addressable.
    Register,
    /// Read-only memory in the processor's map.
    Rom,
    /// The built-in space that holds constants.
    Constant,
    /// The built-in space that holds compiler temporaries.
    Unique,
}

/// How a field's value is printed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumberBase {
    /// Base sixteen, the SLEIGH default.
    Hex,
    /// Base ten.
    Dec,
}

macro_rules! id {
    ($(#[$m:meta])* $name:ident) => {
        $(#[$m])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(pub u32);

        impl $name {
            /// The index into the owning arena.
            pub fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

id!(
    /// Index into [`Spec::spaces`].
    SpaceId
);
id!(
    /// Index into [`Spec::varnodes`].
    VarnodeId
);
id!(
    /// Index into [`Spec::tokens`].
    TokenId
);
id!(
    /// Index into [`Spec::fields`].
    FieldId
);
id!(
    /// Index into [`Spec::context_fields`].
    ContextFieldId
);
id!(
    /// Index into [`Spec::bitranges`].
    BitRangeId
);
id!(
    /// Index into [`Spec::tables`].
    TableId
);
id!(
    /// Index into [`Spec::constructors`].
    ConstructorId
);
id!(
    /// Index into [`Spec::macros`].
    MacroId
);
id!(
    /// Index into [`Spec::pcodeops`].
    PcodeOpId
);

/// An address space.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Space {
    /// Its identifier in the specification.
    pub name: String,
    /// What it models.
    pub kind: SpaceKind,
    /// Bytes needed to hold any address in it.
    pub size: u32,
    /// Bytes addressed by one address. One unless the specification says
    /// otherwise, and the reason a pointer is not always a byte pointer.
    pub wordsize: u32,
    /// Whether `*` with no space override means this one.
    pub default: bool,
}

/// A named piece of an address space: a register, or any global the
/// specification wants to name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Varnode {
    /// Its identifier.
    pub name: String,
    /// The space it lives in.
    pub space: SpaceId,
    /// Its offset in that space.
    pub offset: u64,
    /// Its size in bytes.
    pub size: u32,
}

/// A fixed width slice of the instruction stream that fields are cut from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TokenDef {
    /// Its identifier.
    pub name: String,
    /// Its width in bytes. Always the declared bit count divided by eight.
    pub size: u32,
    /// Byte order used to turn its bytes into the integer the fields index
    /// into. Inherited from `define endian` unless the token overrides it.
    pub endian: Endian,
}

/// A range of bits within a token, and how to read it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Field {
    /// Its identifier.
    pub name: String,
    /// The token it is cut from.
    pub token: TokenId,
    /// Least significant bit of the range, counting from zero at the token's
    /// least significant bit.
    pub low: u32,
    /// Most significant bit of the range, inclusive.
    pub high: u32,
    /// Whether the encoding is twos complement.
    pub signed: bool,
    /// How the value prints when nothing is attached.
    pub base: NumberBase,
    /// The alternate meaning an `attach` statement gave it.
    pub attach: Attach,
}

impl Field {
    /// How many bits the field spans.
    pub fn bits(&self) -> u32 {
        self.high - self.low + 1
    }

    /// Which byte of the token, and which bit of that byte, hold bit `bit` of
    /// the field's token. `None` if the bit is outside the token.
    ///
    /// This is the bridge from the language's bit numbering to the bytes a
    /// decoder actually has: bit zero is the token's least significant bit,
    /// which is in the last byte of a big endian token and the first byte of a
    /// little endian one.
    pub fn bit_position(token: &TokenDef, bit: u32) -> Option<(usize, u32)> {
        if bit >= token.size * 8 {
            return None;
        }
        let byte = match token.endian {
            Endian::Big => token.size - 1 - bit / 8,
            Endian::Little => bit / 8,
        };
        Some((byte as usize, bit % 8))
    }

    /// Pull this field's raw value out of `bytes`, where `bytes` starts at the
    /// token's first byte. `None` if the slice is too short.
    pub fn extract(&self, token: &TokenDef, bytes: &[u8]) -> Option<u64> {
        if bytes.len() < token.size as usize {
            return None;
        }
        let mut value: u64 = 0;
        for (out, bit) in (self.low..=self.high).enumerate() {
            let (byte, offset) = Field::bit_position(token, bit)?;
            if bytes[byte] >> offset & 1 == 1 {
                value |= 1u64 << out;
            }
        }
        Some(value)
    }

    /// The same value, sign extended when the field says so.
    pub fn extract_signed(&self, token: &TokenDef, bytes: &[u8]) -> Option<i64> {
        let raw = self.extract(token, bytes)?;
        Some(if self.signed {
            sign_extend(raw, self.bits())
        } else {
            raw as i64
        })
    }
}

/// Interpret `value`, `bits` wide, as twos complement.
pub fn sign_extend(value: u64, bits: u32) -> i64 {
    if bits == 0 || bits >= 64 {
        return value as i64;
    }
    let shift = 64 - bits;
    ((value << shift) as i64) >> shift
}

/// A field defined over the context register rather than the instruction.
///
/// Bit numbering here runs the other way from a token field: bit zero is the
/// most significant bit of the context register's first byte, which is why
/// specifications declare `TMode=(0,0)` as the first flag and then count
/// upwards through the register. [`ContextField::bit_position`] is the one
/// place that convention is written down.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContextField {
    /// Its identifier.
    pub name: String,
    /// The register it is defined over.
    pub register: VarnodeId,
    /// First bit of the range, counting from the register's most significant
    /// bit.
    pub low: u32,
    /// Last bit of the range, inclusive. This is the range's *least*
    /// significant bit.
    pub high: u32,
    /// Whether the encoding is twos complement.
    pub signed: bool,
    /// How the value prints.
    pub base: NumberBase,
    /// Whether a `globalset` of this field stops at the instruction it names
    /// instead of following the flow.
    pub noflow: bool,
    /// The alternate meaning an `attach` statement gave it.
    pub attach: Attach,
}

impl ContextField {
    /// How many bits the field spans.
    pub fn bits(&self) -> u32 {
        self.high - self.low + 1
    }

    /// Which byte of the context register, and which bit of that byte, hold
    /// context bit `bit`.
    pub fn bit_position(bit: u32) -> (usize, u32) {
        ((bit / 8) as usize, 7 - bit % 8)
    }

    /// Pull this field out of a context register image.
    pub fn extract(&self, context: &[u8]) -> Option<u64> {
        let mut value = 0u64;
        for (out, bit) in (self.low..=self.high).rev().enumerate() {
            let (byte, offset) = ContextField::bit_position(bit);
            if byte >= context.len() {
                return None;
            }
            if context[byte] >> offset & 1 == 1 {
                value |= 1u64 << out;
            }
        }
        Some(value)
    }
}

/// A named run of bits inside a register, from `define bitrange`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BitRange {
    /// Its identifier.
    pub name: String,
    /// The register the bits live in.
    pub register: VarnodeId,
    /// Least significant bit of the range within that register.
    pub low: u32,
    /// How many bits.
    pub bits: u32,
}

/// What an `attach` statement did to a field.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub enum Attach {
    /// Nothing: the field is its own integer value.
    #[default]
    None,
    /// `attach variables`: the value indexes a register list. A `None` entry
    /// makes that encoding invalid rather than falling back to the integer.
    Variables(Vec<Option<VarnodeId>>),
    /// `attach names`: the value indexes a list of display strings, with the
    /// semantic meaning left alone.
    Names(Vec<Option<String>>),
    /// `attach values`: the value indexes a list of other integers.
    Values(Vec<Option<i64>>),
}

impl Attach {
    /// How many encodings the attachment covers. Zero when there is none.
    pub fn len(&self) -> usize {
        match self {
            Attach::None => 0,
            Attach::Variables(v) => v.len(),
            Attach::Names(v) => v.len(),
            Attach::Values(v) => v.len(),
        }
    }

    /// Whether there is no attachment.
    pub fn is_empty(&self) -> bool {
        matches!(self, Attach::None)
    }
}

/// A user defined p-code operation, declared with `define pcodeop`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PcodeOp {
    /// Its identifier, which is all the specification says about it.
    pub name: String,
}

/// Anything the parser resolved a name to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Symbol {
    /// An address space.
    Space(SpaceId),
    /// A named varnode.
    Varnode(VarnodeId),
    /// A token.
    Token(TokenId),
    /// A token field.
    Field(FieldId),
    /// A context field.
    Context(ContextFieldId),
    /// A named bit range.
    BitRange(BitRangeId),
    /// A table.
    Table(TableId),
    /// A p-code macro.
    Macro(MacroId),
    /// A user defined p-code operation.
    PcodeOp(PcodeOpId),
    /// One of the language's own symbols.
    Builtin(Builtin),
}

/// The symbols SLEIGH predefines.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Builtin {
    /// Offset of the current instruction's address.
    InstStart,
    /// Offset of the next instruction's address.
    InstNext,
    /// Offset of the address after the next instruction.
    InstNext2,
    /// The empty pattern, which matches anything.
    Epsilon,
}

/// A reference to a symbol from inside a constructor, a disassembly action or
/// a semantic body.
///
/// The important case for a decoder is [`SymbolRef::Operand`]: it is an index
/// into [`Constructor::operands`], so the decoder never has to match names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolRef {
    /// The constructor's operand at this index.
    Operand(u16),
    /// A temporary created inside the semantic body, at this index into
    /// [`Constructor::locals`] or [`MacroDef::locals`].
    Local(u16),
    /// A macro parameter, at this index into [`MacroDef::params`].
    Param(u16),
    /// A global named varnode.
    Varnode(VarnodeId),
    /// A token field, used directly.
    Field(FieldId),
    /// A context field.
    Context(ContextFieldId),
    /// A named bit range over a register.
    BitRange(BitRangeId),
    /// A table, named rather than used as an operand.
    Table(TableId),
    /// An address space, where one is named as a value.
    Space(SpaceId),
    /// One of the language's own symbols.
    Builtin(Builtin),
}

/// A local temporary in a semantic body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Local {
    /// Its identifier.
    pub name: String,
    /// Its size in bytes, when the specification gave one. Otherwise the size
    /// has to be inferred from the statements it appears in, which this front
    /// end deliberately does not do.
    pub size: Option<u32>,
}

/// How a constructor's display section renders.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Display {
    /// The instruction mnemonic, for constructors in the root table. A
    /// subtable constructor has none, and neither does a root constructor
    /// whose display starts with `^`.
    pub mnemonic: Option<String>,
    /// The rest of the section, in order.
    pub pieces: Vec<DisplayPiece>,
}

/// One element of a display section.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DisplayPiece {
    /// Text printed as it stands.
    Literal(String),
    /// An operand, printed by rendering whatever it resolved to.
    Operand(u16),
}

/// Where an operand's bits begin.
///
/// A plain byte offset from the start of the instruction is enough only while
/// every subtable ahead of the operand has a fixed width. x86 breaks that: a
/// ModR/M subtable matches between one and six bytes, so everything written
/// after it with a `;` sits where only the decoder can know. An offset is
/// therefore measured from a base, which is either the instruction's own start
/// or the end of an earlier operand's match.
///
/// The compiled `.sla` form carries the same pair per operand, with -1 as the
/// "from the start of the instruction" sentinel; see `docs/sla-format.md`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Offset {
    /// The operand whose match this is measured from the end of. `None`
    /// measures from the first byte of the instruction.
    pub base: Option<u16>,
    /// Bytes past the base.
    pub delta: usize,
}

impl Offset {
    /// An offset a fixed number of bytes into the instruction.
    pub fn absolute(delta: usize) -> Offset {
        Offset { base: None, delta }
    }

    /// Whether the offset is a plain number the caller can use without having
    /// resolved any other operand first.
    pub fn is_absolute(&self) -> bool {
        self.base.is_none()
    }

    /// Resolve against the end offsets of the operands already matched.
    ///
    /// `end_of` gives, for an operand index, the byte just past its match.
    /// Returns `None` when the base has not been resolved.
    pub fn resolve(&self, end_of: impl Fn(u16) -> Option<usize>) -> Option<usize> {
        match self.base {
            None => Some(self.delta),
            Some(i) => end_of(i).map(|end| end.saturating_add(self.delta)),
        }
    }
}

/// Where a constructor's operand gets its value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperandSource {
    /// A token field, read at [`Operand::offset`].
    Field(FieldId),
    /// A context field.
    Context(ContextFieldId),
    /// A subtable: recurse, starting at [`Operand::offset`].
    Table(TableId),
    /// A fixed register named in the pattern.
    Varnode(VarnodeId),
    /// A named bit range.
    BitRange(BitRangeId),
    /// Computed by the disassembly action section rather than read from bits.
    Computed,
    /// Nothing in the constructor defines it. Kept rather than rejected so a
    /// caller can report the specification's own mistake.
    Unbound,
}

/// One operand of a constructor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Operand {
    /// Its identifier, local to the constructor.
    pub name: String,
    /// Where its value comes from.
    pub source: OperandSource,
    /// Where its token, or its subtable's first token, begins. When the
    /// alternatives of [`Constructor::resolved`] disagree this holds the first
    /// of them; [`PatternAlt::offsets`] is the per-alternative truth.
    pub offset: Offset,
    /// Whether it appears nowhere in the display section.
    pub invisible: bool,
}

/// How two sides of a pattern constraint are compared.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstraintOp {
    /// `=`
    Equal,
    /// `!=`
    NotEqual,
    /// `<`
    Less,
    /// `<=`
    LessEqual,
    /// `>`
    Greater,
    /// `>=`
    GreaterEqual,
}

/// A constructor's bit pattern, exactly as written.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PatternExpr {
    /// `a & b`: both must hold, over the same tokens.
    And(Box<PatternExpr>, Box<PatternExpr>),
    /// `a | b`: either may hold.
    Or(Box<PatternExpr>, Box<PatternExpr>),
    /// `a ; b`: both hold, with b's tokens following a's in the stream.
    Cat(Box<PatternExpr>, Box<PatternExpr>),
    /// `a ...`: a is left justified in whatever length the whole turns out to
    /// be, so it stops forcing the length.
    EllipsisRight(Box<PatternExpr>),
    /// `... a`: a is right justified, so its offset is only known once the
    /// length is.
    EllipsisLeft(Box<PatternExpr>),
    /// A comparison between a symbol and an expression.
    Constraint {
        /// The left hand side, always a single symbol.
        lhs: SymbolRef,
        /// How they are compared.
        op: ConstraintOp,
        /// The right hand side.
        rhs: DisasmExpr,
    },
    /// A bare symbol: the bits are used but not constrained.
    Symbol(SymbolRef),
    /// `epsilon`: matches everything and consumes nothing.
    Epsilon,
}

/// An expression in a disassembly action or on the right of a constraint.
///
/// These are evaluated at disassembly time over arbitrary precision signed
/// integers, which is why the model keeps them as a tree rather than folding
/// them into the bit pattern.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DisasmExpr {
    /// A literal.
    Num(i64),
    /// A symbol whose integer meaning is used.
    Symbol(SymbolRef),
    /// A unary operator.
    Unary(DisasmUnOp, Box<DisasmExpr>),
    /// A binary operator.
    Binary(DisasmBinOp, Box<DisasmExpr>, Box<DisasmExpr>),
}

/// Unary operators available at disassembly time.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DisasmUnOp {
    /// `-`
    Negate,
    /// `~`
    Not,
}

/// Binary operators available at disassembly time.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DisasmBinOp {
    /// `+`
    Add,
    /// `-`
    Sub,
    /// `*`
    Mul,
    /// `/`
    Div,
    /// `<<`
    Shl,
    /// `>>`, arithmetic.
    Shr,
    /// `$and`, or `&` inside a disassembly action.
    And,
    /// `$or`, or `|` inside a disassembly action.
    Or,
    /// `$xor`, or `^`.
    Xor,
}

/// A statement in a disassembly action section.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DisasmStmt {
    /// Give an operand or a context field a computed value.
    Assign {
        /// What is written to.
        target: DisasmTarget,
        /// The value.
        value: DisasmExpr,
    },
    /// Make a context change stick from an address onwards.
    GlobalSet {
        /// The first address the new value applies at.
        address: DisasmExpr,
        /// The context field being published.
        context: ContextFieldId,
    },
}

/// What a disassembly action writes to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DisasmTarget {
    /// One of the constructor's operands.
    Operand(u16),
    /// A context field, which changes how the rest of this instruction parses.
    Context(ContextFieldId),
}

/// The reduction of a constructor's pattern to something a decoder can test
/// with byte compares.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ResolvedPattern {
    /// The alternatives. An encoding matches the constructor if it matches any
    /// one of them.
    pub alternatives: Vec<PatternAlt>,
    /// Why the reduction is only a filter, when it is. Everything the
    /// constructor matches still matches an alternative, but not the other way
    /// round, so the caller must also evaluate [`Constructor::pattern`].
    pub approximation: Option<Approximation>,
}

/// What stopped a pattern reducing exactly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Approximation {
    /// A `...` on the left of a sub-pattern right justifies it at a length
    /// that is not known until the whole instruction has been parsed, so the
    /// byte offset of its constraints is not known here.
    RightJustified,
    /// A `;` followed a sub-pattern whose length depends on which constructor
    /// of a subtable matched, so the bits written after it have no fixed place
    /// in the stream and are left out of [`PatternAlt::instr`] rather than
    /// guessed at. The operands after it are still placed: their
    /// [`Operand::offset`] is measured from the end of that subtable. This is
    /// x86 with a ModR/M byte, and nothing else in the published corpus.
    UnknownTokenOffset,
    /// The disjunction grew past [`crate::Limits::pattern_alternatives`] and
    /// was collapsed to the bits every alternative agrees on.
    TooManyAlternatives,
}

impl ResolvedPattern {
    /// Whether the alternatives are only a filter.
    pub fn is_approximate(&self) -> bool {
        self.approximation.is_some()
    }

    /// Whether any alternative's mask test passes. This is the fast path and
    /// it is necessary but, when [`ResolvedPattern::approximation`] is set or an
    /// alternative carries residuals, not sufficient.
    pub fn may_match(&self, instr: &[u8], context: &[u8]) -> bool {
        self.alternatives
            .iter()
            .any(|a| a.instr.matches(instr) && a.context.matches(context))
    }

    /// The fewest instruction bytes any alternative needs.
    pub fn min_length(&self) -> usize {
        self.alternatives
            .iter()
            .map(|a| a.length)
            .min()
            .unwrap_or(0)
    }
}

/// One conjunctive alternative of a resolved pattern.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct PatternAlt {
    /// The test against the instruction stream, byte zero being the byte at
    /// the instruction's own address.
    pub instr: MaskValue,
    /// The test against the context register image.
    pub context: MaskValue,
    /// Instruction bytes this alternative accounts for, including the
    /// shortest length of any subtable operand. It is the exact length when
    /// every table involved is fixed width, and a lower bound otherwise.
    pub length: usize,
    /// Constraints that are not a bit test and have to be evaluated after the
    /// masks pass: `r1 = r2`, `f < 3`, and anything else with an expression on
    /// the right.
    pub residual: Vec<PatternExpr>,
    /// Where each operand of the constructor begins if this alternative is the
    /// one that matched, indexed by operand.
    pub offsets: Vec<Offset>,
}

/// A mask and the value the masked bits must take.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct MaskValue {
    /// Which bits matter, byte by byte.
    pub mask: Vec<u8>,
    /// What those bits must be. Bits outside the mask are zero.
    pub value: Vec<u8>,
}

impl MaskValue {
    /// Whether the test is vacuous.
    pub fn is_empty(&self) -> bool {
        self.mask.iter().all(|&b| b == 0)
    }

    /// How many bytes the test reaches into.
    pub fn len(&self) -> usize {
        self.mask.iter().rposition(|&b| b != 0).map_or(0, |i| i + 1)
    }

    /// Whether `bytes` satisfies it. A slice too short for the mask fails,
    /// because a decoder that has not read the bytes has not matched them.
    pub fn matches(&self, bytes: &[u8]) -> bool {
        for (i, (&m, &v)) in self.mask.iter().zip(&self.value).enumerate() {
            if m == 0 {
                continue;
            }
            let Some(&b) = bytes.get(i) else {
                return false;
            };
            if b & m != v {
                return false;
            }
        }
        true
    }

    /// Add one byte's worth of constraint, growing the vectors as needed.
    /// Returns false when it contradicts what is already there.
    pub fn constrain(&mut self, byte: usize, mask: u8, value: u8) -> bool {
        if self.mask.len() <= byte {
            self.mask.resize(byte + 1, 0);
            self.value.resize(byte + 1, 0);
        }
        let overlap = self.mask[byte] & mask;
        if self.value[byte] & overlap != value & overlap {
            return false;
        }
        self.mask[byte] |= mask;
        self.value[byte] |= value & mask;
        true
    }

    /// Fold `other` in. Returns false when the two contradict.
    pub fn merge(&mut self, other: &MaskValue) -> bool {
        for (i, (&m, &v)) in other.mask.iter().zip(&other.value).enumerate() {
            if m != 0 && !self.constrain(i, m, v) {
                return false;
            }
        }
        true
    }

    /// The same test moved `bytes` later in the stream.
    pub fn shifted(&self, bytes: usize) -> MaskValue {
        if bytes == 0 || self.mask.is_empty() {
            return self.clone();
        }
        let mut mask = vec![0u8; bytes];
        let mut value = vec![0u8; bytes];
        mask.extend_from_slice(&self.mask);
        value.extend_from_slice(&self.value);
        MaskValue { mask, value }
    }

    /// Keep only what this test and `other` agree on, which is the weakest
    /// test both of them imply. Used when a disjunction is too large to keep
    /// exactly.
    pub fn intersect(&self, other: &MaskValue) -> MaskValue {
        let n = self.mask.len().min(other.mask.len());
        let mut mask = vec![0u8; n];
        let mut value = vec![0u8; n];
        for i in 0..n {
            let agree = self.mask[i] & other.mask[i] & !(self.value[i] ^ other.value[i]);
            mask[i] = agree;
            value[i] = self.value[i] & agree;
        }
        MaskValue { mask, value }
    }
}

/// A size written with the `:n` modifier, in bytes, where the specification
/// gave one.
pub type SizeHint = Option<u32>;

/// An expression in a semantic body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    /// A literal, with the size the `:n` modifier gave it.
    Num {
        /// The value.
        value: u64,
        /// Its size in bytes, if stated.
        size: SizeHint,
    },
    /// A symbol read as a varnode.
    Symbol(SymbolRef),
    /// `v:n`, the least significant n bytes.
    Truncate {
        /// What is truncated.
        value: Box<Expr>,
        /// How many bytes are kept.
        bytes: u32,
    },
    /// `v(n)`, dropping the n least significant bytes. The result's size comes
    /// from context.
    Shave {
        /// What is shaved.
        value: Box<Expr>,
        /// How many bytes are dropped.
        bytes: u32,
    },
    /// `v[lsb,bits]`, a bit range.
    BitRange {
        /// What the bits come from.
        value: Box<Expr>,
        /// Least significant bit of the range.
        lsb: u32,
        /// How many bits.
        bits: u32,
    },
    /// `&v`, the offset of a varnode as a constant. Resolved at disassembly
    /// time, not at run time.
    AddressOf {
        /// The varnode whose address is taken.
        value: Box<Expr>,
        /// The size of the resulting constant, if stated.
        size: SizeHint,
    },
    /// `*[space]:n addr`, a LOAD.
    Load {
        /// The space, when overridden.
        space: Option<SpaceId>,
        /// The size in bytes, when stated.
        size: SizeHint,
        /// The pointer.
        addr: Box<Expr>,
    },
    /// A unary p-code operator.
    Unary(UnOp, Box<Expr>),
    /// A binary p-code operator.
    Binary(BinOp, Box<Expr>, Box<Expr>),
    /// One of the language's function-syntax operators.
    Intrinsic {
        /// Which one.
        op: Intrinsic,
        /// Its arguments.
        args: Vec<Expr>,
    },
    /// A call to a `define pcodeop`, which produces CALLOTHER.
    UserOp {
        /// The operation.
        op: PcodeOpId,
        /// Its arguments.
        args: Vec<Expr>,
    },
}

/// Unary p-code operators with prefix syntax.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    /// `!`, BOOL_NEGATE.
    BoolNegate,
    /// `~`, INT_NEGATE.
    Negate,
    /// `-`, INT_2COMP.
    TwosComp,
    /// `f-`, FLOAT_NEG.
    FloatNeg,
}

/// Binary p-code operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    /// `*`, INT_MULT.
    Mult,
    /// `/`, INT_DIV.
    Div,
    /// `s/`, INT_SDIV.
    SDiv,
    /// `%`, INT_REM.
    Rem,
    /// `s%`, INT_SREM.
    SRem,
    /// `f/`, FLOAT_DIV.
    FloatDiv,
    /// `f*`, FLOAT_MULT.
    FloatMult,
    /// `+`, INT_ADD.
    Add,
    /// `-`, INT_SUB.
    Sub,
    /// `f+`, FLOAT_ADD.
    FloatAdd,
    /// `f-`, FLOAT_SUB.
    FloatSub,
    /// `<<`, INT_LEFT.
    Left,
    /// `>>`, INT_RIGHT.
    Right,
    /// `s>>`, INT_SRIGHT.
    SRight,
    /// `s<`, INT_SLESS.
    SLess,
    /// `s<=`, INT_SLESSEQUAL.
    SLessEqual,
    /// `<`, INT_LESS.
    Less,
    /// `<=`, INT_LESSEQUAL.
    LessEqual,
    /// `f<`, FLOAT_LESS.
    FloatLess,
    /// `f<=`, FLOAT_LESSEQUAL.
    FloatLessEqual,
    /// `==`, INT_EQUAL.
    Equal,
    /// `!=`, INT_NOTEQUAL.
    NotEqual,
    /// `f==`, FLOAT_EQUAL.
    FloatEqual,
    /// `f!=`, FLOAT_NOTEQUAL.
    FloatNotEqual,
    /// `&`, INT_AND.
    And,
    /// `^`, INT_XOR.
    Xor,
    /// `|`, INT_OR.
    Or,
    /// `^^`, BOOL_XOR.
    BoolXor,
    /// `&&`, BOOL_AND.
    BoolAnd,
    /// `||`, BOOL_OR.
    BoolOr,
}

/// The p-code operators written with function syntax.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Intrinsic {
    /// INT_ZEXT.
    Zext,
    /// INT_SEXT.
    Sext,
    /// INT_CARRY.
    Carry,
    /// INT_SCARRY.
    SCarry,
    /// INT_SBORROW.
    SBorrow,
    /// FLOAT_NAN.
    Nan,
    /// FLOAT_ABS.
    Abs,
    /// FLOAT_SQRT.
    Sqrt,
    /// INT2FLOAT.
    Int2Float,
    /// FLOAT2FLOAT.
    Float2Float,
    /// TRUNC.
    Trunc,
    /// FLOAT_CEIL.
    Ceil,
    /// FLOAT_FLOOR.
    Floor,
    /// FLOAT_ROUND.
    Round,
    /// POPCOUNT.
    PopCount,
    /// LZCOUNT.
    LzCount,
    /// CPOOLREF.
    CPool,
    /// NEW.
    NewObject,
}

impl Intrinsic {
    /// The name it is written as, or `None` if the name is not one.
    pub fn from_name(name: &str) -> Option<Intrinsic> {
        Some(match name {
            "zext" => Intrinsic::Zext,
            "sext" => Intrinsic::Sext,
            "carry" => Intrinsic::Carry,
            "scarry" => Intrinsic::SCarry,
            "sborrow" => Intrinsic::SBorrow,
            "nan" => Intrinsic::Nan,
            "abs" => Intrinsic::Abs,
            "sqrt" => Intrinsic::Sqrt,
            "int2float" => Intrinsic::Int2Float,
            "float2float" => Intrinsic::Float2Float,
            "trunc" => Intrinsic::Trunc,
            "ceil" => Intrinsic::Ceil,
            "floor" => Intrinsic::Floor,
            "round" => Intrinsic::Round,
            "popcount" => Intrinsic::PopCount,
            "lzcount" => Intrinsic::LzCount,
            "cpool" => Intrinsic::CPool,
            "newobject" => Intrinsic::NewObject,
            _ => return None,
        })
    }
}

/// What a semantic assignment writes to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lvalue {
    /// A varnode named directly, with the size given if the statement
    /// declared one.
    Symbol {
        /// The symbol written.
        symbol: SymbolRef,
        /// Its size in bytes, when the statement stated one.
        size: SizeHint,
    },
    /// `v[lsb,bits] = ...`, filling a bit range and leaving the rest alone.
    BitRange {
        /// The varnode whose bits are filled.
        symbol: SymbolRef,
        /// Least significant bit of the range.
        lsb: u32,
        /// How many bits.
        bits: u32,
    },
    /// `*[space]:n addr = ...`, a STORE.
    Store {
        /// The space, when overridden.
        space: Option<SpaceId>,
        /// The size in bytes, when stated.
        size: SizeHint,
        /// The pointer.
        addr: Box<Expr>,
    },
}

/// Where a branch goes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JumpTarget {
    /// An address, given as an offset and optionally a space.
    Direct {
        /// The offset.
        addr: Expr,
        /// The space, when the statement named one.
        space: Option<SpaceId>,
    },
    /// `[v]`, an offset taken from a varnode at run time.
    Indirect(Expr),
    /// `<name>`, a p-code operation within this instruction.
    Label(u16),
}

/// What a constructor exports to the table it belongs to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Export {
    /// A varnode or a constant.
    Value(Expr),
    /// `*[space]:n addr`, a reference that reads and writes through a pointer.
    Deref {
        /// The space, when overridden.
        space: Option<SpaceId>,
        /// The size in bytes, when stated.
        size: SizeHint,
        /// The pointer.
        addr: Expr,
    },
}

/// A statement in a semantic body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    /// An assignment. `local` is set when the statement declared the target.
    Assign {
        /// Whether the statement carried the `local` keyword.
        local: bool,
        /// What is written.
        dest: Lvalue,
        /// The value.
        value: Expr,
    },
    /// `local name:n;`, a temporary with no initial value.
    Declare(u16),
    /// `build operand;`
    Build(u16),
    /// `<<table>>`, which starts the run of statements that `crossbuild`
    /// pulls in for that table.
    ///
    /// This is not in the SLEIGH manual. It appears only in Ghidra's Hexagon
    /// specification, where a packet's instructions contribute p-code to
    /// packet level tables, and it is recorded rather than rejected so that
    /// the specification parses. A decoder that does not model packets can
    /// ignore it.
    CrossBuildSection(TableId),
    /// `crossbuild addr, table;`
    CrossBuild {
        /// The address whose instruction is built.
        addr: Expr,
        /// The table built there.
        table: TableId,
    },
    /// `delayslot(n);`
    DelaySlot(u64),
    /// `export ...;`
    Export(Export),
    /// `<name>`, defining a branch target within the instruction.
    Label(u16),
    /// `goto ...;`
    Goto(JumpTarget),
    /// `if cond goto ...;`
    CondGoto {
        /// The condition.
        cond: Expr,
        /// Where it goes when true.
        target: JumpTarget,
    },
    /// `call ...;`
    Call(JumpTarget),
    /// `return [v];`
    Return(Expr),
    /// A `define pcodeop` invoked for its effect.
    UserOp {
        /// The operation.
        op: PcodeOpId,
        /// Its arguments.
        args: Vec<Expr>,
    },
    /// A p-code macro invoked. Arguments are passed by reference.
    MacroCall {
        /// The macro.
        mac: MacroId,
        /// Its arguments.
        args: Vec<Expr>,
    },
}

/// A p-code macro.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroDef {
    /// Its identifier.
    pub name: String,
    /// Parameter names, in order. Referred to as [`SymbolRef::Param`].
    pub params: Vec<String>,
    /// Temporaries the body creates.
    pub locals: Vec<Local>,
    /// Labels the body defines.
    pub labels: Vec<String>,
    /// The body.
    pub body: Vec<Stmt>,
    /// Where it was written.
    pub location: Location,
}

/// A family symbol built from one or more constructors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Table {
    /// Its identifier. The root table is `instruction`.
    pub name: String,
    /// Its constructors, in the order the specification gave them, which is
    /// the order a decoder must try them in when two patterns overlap.
    pub constructors: Vec<ConstructorId>,
    /// The fewest instruction bytes any of its constructors consumes.
    pub min_length: usize,
    /// The most any of them consumes. Equal to `min_length` for a table of
    /// fixed width, which is what lets a `;` after it be placed exactly.
    pub max_length: usize,
}

impl Table {
    /// Whether every constructor of the table consumes the same number of
    /// bytes, so anything following it sits at a known offset.
    pub fn is_fixed_length(&self) -> bool {
        self.min_length == self.max_length
    }
}

/// One constructor: a display, a pattern, an optional disassembly action and
/// an optional semantic body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constructor {
    /// The table it belongs to.
    pub table: TableId,
    /// How it renders.
    pub display: Display,
    /// Its operands, display order first, then any the pattern alone names.
    ///
    /// This is the numbering [`DisplayPiece::Operand`], [`Offset::base`] and
    /// every [`SymbolRef::Operand`] use. It is *not* the order the bits arrive
    /// in; see [`Constructor::order`], and it is *not* the numbering a
    /// compiled `.sla` uses either: every index in that file is a position in
    /// the resolution-ordered list, which compiling all 152 definitions and
    /// diffing against the reference proved twice.
    pub operands: Vec<Operand>,
    /// Every operand index exactly once, in the order a decoder must resolve
    /// them.
    ///
    /// Display order and pattern order are different orders, and x86 is where
    /// that stops being pedantry:
    /// `:CMP^XmmCondPD^"PD" XmmReg,m128 is ... (m128 & XmmReg ...); XmmCondPD`
    /// prints `XmmCondPD` first and matches it last, after a ModR/M whose
    /// length only the decoder knows. Walking this list resolves every
    /// operand's [`Offset::base`] before the operand that is measured from
    /// it, which walking [`Constructor::operands`] in index order does not.
    pub order: Vec<u16>,
    /// Temporaries its body creates.
    pub locals: Vec<Local>,
    /// Labels its body defines.
    pub labels: Vec<String>,
    /// The pattern exactly as written.
    pub pattern: PatternExpr,
    /// The pattern reduced to byte tests.
    pub resolved: ResolvedPattern,
    /// The disassembly action section, empty when there was none.
    pub disasm: Vec<DisasmStmt>,
    /// The semantic body. `None` means the constructor was written `unimpl`.
    pub body: Option<Vec<Stmt>>,
    /// Where it was written.
    pub location: Location,
}

impl Constructor {
    /// Whether the constructor declined to model its own semantics.
    pub fn is_unimplemented(&self) -> bool {
        self.body.is_none()
    }
}

/// A whole processor specification.
#[derive(Debug, Clone, Default)]
pub struct Spec {
    /// Byte order for the processor as a whole.
    pub endian: Endian,
    /// Instruction alignment in bytes. One means no alignment requirement.
    pub alignment: u32,
    /// Every address space, including the built-in `const` and `unique`.
    pub spaces: Vec<Space>,
    /// The space `*` refers to without an override.
    pub default_space: Option<SpaceId>,
    /// Every named varnode.
    pub varnodes: Vec<Varnode>,
    /// Every token.
    pub tokens: Vec<TokenDef>,
    /// Every token field.
    pub fields: Vec<Field>,
    /// Every context field.
    pub context_fields: Vec<ContextField>,
    /// The register context fields are defined over, when there is one.
    pub context_register: Option<VarnodeId>,
    /// Every named bit range.
    pub bitranges: Vec<BitRange>,
    /// Every user defined p-code operation.
    pub pcodeops: Vec<PcodeOp>,
    /// Every p-code macro.
    pub macros: Vec<MacroDef>,
    /// Every table. Index zero is always `instruction`.
    pub tables: Vec<Table>,
    /// Every constructor, referred to by index from the tables.
    pub constructors: Vec<Constructor>,
    /// The global scope, by name.
    pub symbols: HashMap<String, Symbol>,
    /// Things that were wrong with the specification but did not stop it being
    /// read, in the order they were found.
    pub warnings: Vec<String>,
}

impl Spec {
    /// The root `instruction` table.
    pub fn root(&self) -> TableId {
        TableId(0)
    }

    /// A table by index.
    pub fn table(&self, id: TableId) -> &Table {
        &self.tables[id.index()]
    }

    /// A constructor by index.
    pub fn constructor(&self, id: ConstructorId) -> &Constructor {
        &self.constructors[id.index()]
    }

    /// A field by index.
    pub fn field(&self, id: FieldId) -> &Field {
        &self.fields[id.index()]
    }

    /// The token a field is cut from.
    pub fn token_of(&self, id: FieldId) -> &TokenDef {
        &self.tokens[self.fields[id.index()].token.index()]
    }

    /// A context field by index.
    pub fn context_field(&self, id: ContextFieldId) -> &ContextField {
        &self.context_fields[id.index()]
    }

    /// A varnode by index.
    pub fn varnode(&self, id: VarnodeId) -> &Varnode {
        &self.varnodes[id.index()]
    }

    /// A space by index.
    pub fn space(&self, id: SpaceId) -> &Space {
        &self.spaces[id.index()]
    }

    /// A macro by index.
    pub fn macro_def(&self, id: MacroId) -> &MacroDef {
        &self.macros[id.index()]
    }

    /// A global symbol by name.
    pub fn lookup(&self, name: &str) -> Option<Symbol> {
        self.symbols.get(name).copied()
    }

    /// How many bytes a context register image needs.
    pub fn context_bytes(&self) -> usize {
        self.context_register
            .map(|id| self.varnode(id).size as usize)
            .unwrap_or(0)
    }

    /// The constructors whose bit patterns could not be reduced exactly, with
    /// the reason. A decoder must fall back to [`Constructor::pattern`] for
    /// these; [`ResolvedPattern::alternatives`] is only a filter.
    pub fn approximate_constructors(
        &self,
    ) -> impl Iterator<Item = (ConstructorId, Approximation)> + '_ {
        self.constructors.iter().enumerate().filter_map(|(i, c)| {
            c.resolved
                .approximation
                .map(|why| (ConstructorId(i as u32), why))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn token(size: u32, endian: Endian) -> TokenDef {
        TokenDef {
            name: "t".into(),
            size,
            endian,
        }
    }

    fn field(low: u32, high: u32, signed: bool) -> Field {
        Field {
            name: "f".into(),
            token: TokenId(0),
            low,
            high,
            signed,
            base: NumberBase::Hex,
            attach: Attach::None,
        }
    }

    #[test]
    fn a_big_endian_field_reads_from_the_last_byte() {
        let t = token(4, Endian::Big);
        let f = field(0, 5, false);
        // 0x0000002a big endian: the low six bits live in byte three.
        assert_eq!(f.extract(&t, &[0, 0, 0, 0x2a]), Some(0x2a));
    }

    #[test]
    fn a_little_endian_field_reads_from_the_first_byte() {
        let t = token(4, Endian::Little);
        let f = field(0, 5, false);
        assert_eq!(f.extract(&t, &[0x2a, 0, 0, 0]), Some(0x2a));
    }

    #[test]
    fn a_signed_field_sign_extends() {
        let t = token(1, Endian::Little);
        let f = field(0, 3, true);
        assert_eq!(f.extract_signed(&t, &[0x0f]), Some(-1));
    }

    #[test]
    fn a_short_slice_extracts_nothing() {
        let t = token(4, Endian::Big);
        assert_eq!(field(0, 5, false).extract(&t, &[0, 0]), None);
    }

    #[test]
    fn a_context_field_counts_from_the_top() {
        let f = ContextField {
            name: "TMode".into(),
            register: VarnodeId(0),
            low: 0,
            high: 0,
            signed: false,
            base: NumberBase::Hex,
            noflow: false,
            attach: Attach::None,
        };
        assert_eq!(f.extract(&[0x80, 0, 0, 0]), Some(1));
        assert_eq!(f.extract(&[0x7f, 0xff, 0xff, 0xff]), Some(0));
    }

    #[test]
    fn masks_merge_and_contradict() {
        let mut a = MaskValue::default();
        assert!(a.constrain(0, 0xf0, 0x30));
        assert!(a.constrain(0, 0x0f, 0x05));
        assert_eq!(a.mask, vec![0xff]);
        assert_eq!(a.value, vec![0x35]);
        assert!(!a.constrain(0, 0xf0, 0x40));
    }

    #[test]
    fn a_mask_shifted_moves_the_test_along() {
        let mut a = MaskValue::default();
        a.constrain(0, 0xff, 0x90);
        let b = a.shifted(2);
        assert!(b.matches(&[0, 0, 0x90]));
        assert!(!b.matches(&[0x90, 0, 0]));
    }

    #[test]
    fn a_mask_never_matches_bytes_that_are_not_there() {
        let mut a = MaskValue::default();
        a.constrain(3, 0xff, 0x11);
        assert!(!a.matches(&[0x11]));
    }

    #[test]
    fn intersection_keeps_only_what_both_agree_on() {
        let mut a = MaskValue::default();
        a.constrain(0, 0xff, 0x30);
        let mut b = MaskValue::default();
        b.constrain(0, 0xff, 0x31);
        let c = a.intersect(&b);
        assert_eq!(c.mask, vec![0xfe]);
        assert_eq!(c.value, vec![0x30]);
    }
}
