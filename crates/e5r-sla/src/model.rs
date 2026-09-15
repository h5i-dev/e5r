//! The structured view of a `.sla`: spaces, registers, tokens, symbol tables,
//! constructors with their patterns and their p-code templates.
//!
//! Every field here is one this reader established by experiment; see
//! `docs/sla-format.md`. Anything else stays in [`crate::Sla::tree`] as raw
//! nodes with their offsets, and [`Coverage`] says how much that is.

use crate::decode::{Node, Value};
use crate::ids::{at, el, element_name};

/// One entry of the `<sourcefiles>` list. Only files that define a constructor
/// appear, which is why the index is stored rather than assumed positional.
#[derive(Debug, Clone)]
pub struct SourceFile {
    pub name: String,
    pub index: u64,
}

/// An address space.
#[derive(Debug, Clone)]
pub struct Space {
    /// Which element carried it: `space`, `space_other` or `space_unique`.
    pub kind: SpaceKind,
    pub name: String,
    /// Index used by `Value::Space` references elsewhere in the file.
    pub index: u32,
    pub big_endian: bool,
    pub delay: u64,
    pub size: u64,
    pub word_size: u64,
    pub physical: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpaceKind {
    Normal,
    Other,
    Unique,
}

/// A symbol scope. Scope 0 is the global one; a constructor's operands live in
/// a scope of their own.
#[derive(Debug, Clone)]
pub struct Scope {
    pub id: u32,
    pub parent: u32,
}

/// A field cut out of an instruction token.
#[derive(Debug, Clone)]
pub struct TokenField {
    pub big_endian: bool,
    pub signed: bool,
    pub start_bit: u64,
    pub end_bit: u64,
    pub start_byte: u64,
    pub end_byte: u64,
    pub shift: u64,
}

/// A field cut out of the context register. The same layout as a token field
/// without the endianness, since the context register has only one.
#[derive(Debug, Clone)]
pub struct ContextField {
    pub signed: bool,
    pub start_bit: u64,
    pub end_bit: u64,
    pub start_byte: u64,
    pub end_byte: u64,
    pub shift: u64,
}

/// Where a symbol reads its value from: a slice of the instruction stream, or
/// a slice of the context register. Both shapes occur for `value`, `name`,
/// `valuemap` and `attach variables` symbols.
#[derive(Debug, Clone)]
pub enum FieldDef {
    /// A field of an instruction token.
    Token(TokenField),
    /// A field of the context register.
    Context(ContextField),
}

impl FieldDef {
    /// The token field, if this is one.
    #[must_use]
    pub fn token(&self) -> Option<&TokenField> {
        match self {
            Self::Token(t) => Some(t),
            Self::Context(_) => None,
        }
    }

    /// The context field, if this is one.
    #[must_use]
    pub fn context(&self) -> Option<&ContextField> {
        match self {
            Self::Context(c) => Some(c),
            Self::Token(_) => None,
        }
    }
}

/// An operator inside a pattern expression, which is what a disassembly
/// action computes with. Element ids 47 to 57 in alphabetical order of the
/// operator's name, each settled by compiling a spec that uses only it; see
/// `docs/sla-format.md`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PatternOp {
    /// `$and`, two operands.
    And,
    /// `/`, two operands.
    Div,
    /// `<<`, two operands.
    LeftShift,
    /// Unary `-`, one operand.
    Minus,
    /// `*`, two operands.
    Mult,
    /// Unary `~`, one operand.
    Not,
    /// `$or`, two operands.
    Or,
    /// `+`, two operands.
    Plus,
    /// `>>`, two operands.
    RightShift,
    /// `-`, two operands.
    Sub,
    /// `$xor`, two operands.
    Xor,
}

impl PatternOp {
    /// The element id that carries it.
    #[must_use]
    pub fn element(self) -> u32 {
        match self {
            Self::And => el::PEXP_AND,
            Self::Div => el::PEXP_DIV,
            Self::LeftShift => el::PEXP_LSHIFT,
            Self::Minus => el::PEXP_MINUS,
            Self::Mult => el::PEXP_MULT,
            Self::Not => el::PEXP_NOT,
            Self::Or => el::PEXP_OR,
            Self::Plus => el::PEXP_PLUS,
            Self::RightShift => el::PEXP_RSHIFT,
            Self::Sub => el::PEXP_SUB,
            Self::Xor => el::PEXP_XOR,
        }
    }

    /// The operator an element id stands for, if it is one.
    #[must_use]
    pub fn from_element(id: u32) -> Option<Self> {
        Some(match id {
            el::PEXP_AND => Self::And,
            el::PEXP_DIV => Self::Div,
            el::PEXP_LSHIFT => Self::LeftShift,
            el::PEXP_MINUS => Self::Minus,
            el::PEXP_MULT => Self::Mult,
            el::PEXP_NOT => Self::Not,
            el::PEXP_OR => Self::Or,
            el::PEXP_PLUS => Self::Plus,
            el::PEXP_RSHIFT => Self::RightShift,
            el::PEXP_SUB => Self::Sub,
            el::PEXP_XOR => Self::Xor,
            _ => return None,
        })
    }
}

/// A pattern expression: what a disassembly action computes, evaluated when an
/// instruction is decoded rather than when it runs.
#[derive(Debug, Clone)]
pub enum Expr {
    /// The value of operand `index` of constructor `ct` in table `table`.
    OperandValue {
        index: u64,
        table: u64,
        ct: u64,
    },
    Constant(i128),
    /// A context field read inline, carrying its own bit layout rather than
    /// naming a symbol.
    Context(ContextField),
    /// A token field read inline. This is how an operand body names the bits
    /// it is cut from.
    TokenField(TokenField),
    /// The address of the instruction being decoded.
    InstStart,
    /// The address after it.
    InstNext,
    /// The address after that. Appears in no file Ghidra ships; it was found
    /// by writing a spec that uses it.
    InstNext2,
    /// An operator and its operands, left to right.
    Op {
        op: PatternOp,
        operands: Vec<Expr>,
    },
    /// An element id with no established meaning. Nothing in the corpus
    /// produces one any more, and it is kept so a future format still reads.
    Unknown {
        element: u32,
        operands: Vec<Expr>,
    },
}

/// One `(mask, value)` word of a pattern, read big-endian from the instruction
/// or context bytes at `PatternBlock::offset`.
#[derive(Debug, Clone, Copy)]
pub struct PatternWord {
    pub mask: u64,
    pub value: u64,
}

/// A run of pattern words starting at a byte offset into the stream.
#[derive(Debug, Clone)]
pub struct PatternBlock {
    pub offset: u64,
    pub bytes: u64,
    pub words: Vec<PatternWord>,
}

/// What one branch of the decision tree matches on.
///
/// A file carries either half alone or both wrapped in a `combine_pattern`,
/// and an empty block list is not the same bytes as an absent half, so the
/// shape is recorded rather than flattened.
#[derive(Debug, Clone, Default)]
pub struct Pattern {
    pub context: Vec<PatternBlock>,
    pub instruction: Vec<PatternBlock>,
    /// The two halves were wrapped in a `combine_pattern`.
    pub combined: bool,
    pub has_context: bool,
    pub has_instruction: bool,
}

/// The decision tree a subtable uses to pick a constructor. `start_bit` counts
/// from the most significant bit of the first instruction byte.
#[derive(Debug, Clone)]
pub struct Decision {
    pub number: u64,
    pub on_context: bool,
    pub start_bit: u64,
    pub num_bits: u64,
    pub children: Vec<Decision>,
    pub pairs: Vec<(u32, Pattern)>,
}

/// One piece of a constructor's display form.
#[derive(Debug, Clone)]
pub enum PrintPiece {
    Literal(String),
    /// Print operand `index` of this constructor.
    Operand(u64),
}

/// A leaf of a varnode template: where the space, offset or size comes from.
#[derive(Debug, Clone)]
pub enum ConstTemplate {
    Real(i128),
    SpaceId(u32),
    /// Field `select` (0 space, 1 offset, 2 size) of operand `index`'s handle.
    Handle {
        index: u64,
        select: u64,
        extra: Option<u128>,
    },
    /// A label, by index.
    Relative(i128),
    /// The address of the instruction.
    InstStart,
    /// The address after the instruction.
    InstNext,
    /// The address after that.
    InstNext2,
    /// In a space slot: the space the instruction was decoded from, rather
    /// than a fixed space index. Always paired with [`ConstTemplate::CurSpaceSize`].
    CurSpace,
    /// In a size slot: how many bytes an address in that space takes.
    CurSpaceSize,
    /// A leaf whose element id has no established meaning.
    Unknown(u32),
}

#[derive(Debug, Clone)]
pub struct VarnodeTemplate {
    pub space: ConstTemplate,
    pub offset: ConstTemplate,
    pub size: ConstTemplate,
}

/// One p-code operation. `opcode` is the published p-code opcode number.
#[derive(Debug, Clone)]
pub struct OpTemplate {
    pub opcode: u64,
    pub output: Option<VarnodeTemplate>,
    pub inputs: Vec<VarnodeTemplate>,
}

/// The p-code a constructor contributes, plus the handle it exports.
#[derive(Debug, Clone, Default)]
pub struct ConstructTemplate {
    pub section: Option<i64>,
    pub labels: Option<u64>,
    pub delay: Option<i64>,
    /// The seven `ConstTemplate` parts of an exported handle, when there is one.
    pub result: Option<Vec<ConstTemplate>>,
    pub ops: Vec<OpTemplate>,
}

/// What a constructor does to the context register, in the order the file
/// lists it. A disassembly action can both change context for the rest of the
/// current parse and publish a change from an address onwards, and the two are
/// different records.
#[derive(Debug, Clone)]
pub enum ContextOp {
    /// `field = expr` in a disassembly action: element 32.
    Set {
        /// Which 32-bit word of the context register.
        word: u64,
        /// Right shift that brings the field to bit zero.
        shift: u64,
        /// Which bits of that word the field owns.
        mask: u64,
        /// The value, as a pattern expression.
        value: Vec<Expr>,
    },
    /// `globalset(address, field)`: element 79.
    Commit {
        /// Symbol id of the address argument.
        symbol: u32,
        /// Which 32-bit word of the context register.
        word: u64,
        /// Which bits of that word are published.
        mask: u64,
        /// False when the field was declared `noflow`.
        flow: bool,
    },
}

#[derive(Debug, Clone)]
pub struct Constructor {
    /// Symbol id of the subtable this constructor belongs to.
    pub parent: u32,
    /// Index into [`SourceFile`], and the line in that file.
    pub source: u64,
    pub line: u64,
    /// Instruction length in bytes, before any operand extends it.
    pub length: u64,
    /// Where the mnemonic ends among the print pieces. Negative values occur.
    pub flowthru: i64,
    /// Symbol ids of the operands, in definition order.
    pub operands: Vec<u32>,
    pub print: Vec<PrintPiece>,
    /// Context changes and `globalset` commits, in file order.
    pub context_ops: Vec<ContextOp>,
    pub templates: Vec<ConstructTemplate>,
}

/// The body of a symbol. The variants are the symbol kinds observed in the
/// corpus; `Unknown` keeps the element id of anything else.
#[derive(Debug, Clone)]
pub enum SymbolBody {
    /// A register or other fixed varnode.
    Varnode {
        space: u32,
        offset: u64,
        size: u64,
    },
    /// A `define pcodeop`.
    UserOp {
        index: u64,
    },
    /// A token field used directly as a value.
    Value {
        field: Option<FieldDef>,
    },
    /// `attach values`.
    ValueMap {
        field: Option<FieldDef>,
        values: Vec<i128>,
    },
    /// `attach names`. A `None` entry is an encoding the attachment leaves
    /// undefined, which the file writes as an entry with no name at all.
    Name {
        field: Option<FieldDef>,
        names: Vec<Option<String>>,
    },
    /// `attach variables`: the varnode symbol id per field value, `None` for a
    /// hole in the list.
    VarnodeList {
        field: Option<FieldDef>,
        entries: Vec<Option<u32>>,
    },
    /// A field of the context register.
    Context {
        varnode: u32,
        low: u64,
        high: u64,
        flow: bool,
        field: Option<ContextField>,
    },
    /// An operand of a constructor.
    Operand {
        index: u64,
        offset: u64,
        sub_symbol: Option<u32>,
        /// Attribute 19: the operand this one's offset is measured from the
        /// end of, with -1 meaning the start of the instruction.
        base: i64,
        /// Attribute 18. It equals the width of the operand's token in every
        /// case observed, and no experiment isolated it, so it is carried
        /// rather than named.
        min_length: u64,
        /// Attribute 7, a flag present on a minority of operands. Not
        /// isolated by any experiment, so it is carried and not named.
        flag: Option<bool>,
        expr: Vec<Expr>,
    },
    /// `inst_start`.
    Start,
    /// `inst_next`.
    End,
    /// `inst_next2`.
    Next2,
    Subtable {
        constructors: Vec<Constructor>,
        decision: Option<Decision>,
    },
    Unknown {
        element: u32,
    },
}

#[derive(Debug, Clone)]
pub struct Symbol {
    pub id: u32,
    /// Names come from the header records, which precede the bodies; a symbol
    /// with no header keeps `None` rather than an invented name.
    pub name: Option<String>,
    pub scope: Option<u32>,
    pub body: SymbolBody,
}

/// How much of a file this reader turned into the model above.
#[derive(Debug, Clone, Default)]
pub struct Coverage {
    /// Bytes of the decompressed payload.
    pub total: usize,
    /// Bytes belonging to elements whose meaning is established.
    pub interpreted: usize,
    /// Bytes belonging to elements that are kept as raw nodes.
    pub raw: usize,
    /// Each unnamed element id, how many there are and how many bytes.
    pub unknown: Vec<UnknownElement>,
}

#[derive(Debug, Clone, Copy)]
pub struct UnknownElement {
    pub id: u32,
    pub count: usize,
    pub bytes: usize,
}

impl Coverage {
    /// Fraction of the payload the model accounts for, in the range 0..=1.
    #[must_use]
    pub fn fraction(&self) -> f64 {
        if self.total == 0 {
            return 1.0;
        }
        self.interpreted as f64 / self.total as f64
    }

    pub(crate) fn measure(root: &Node) -> Self {
        let mut cov = Self {
            total: root.len(),
            ..Self::default()
        };
        let mut unknown: Vec<UnknownElement> = Vec::new();
        root.visit(&mut |n| {
            let own = n.own_len();
            if element_name(n.id).is_some() {
                cov.interpreted += own;
            } else {
                cov.raw += own;
                match unknown.iter_mut().find(|u| u.id == n.id) {
                    Some(u) => {
                        u.count += 1;
                        u.bytes += own;
                    }
                    None => unknown.push(UnknownElement {
                        id: n.id,
                        count: 1,
                        bytes: own,
                    }),
                }
            }
        });
        unknown.sort_by_key(|u| u.id);
        cov.unknown = unknown;
        cov
    }
}

// Small readers. Every one takes a default rather than failing, because a
// missing attribute is a fact about the file and should show up in the model
// and in the coverage number, not as an error that hides the rest of the file.

fn u64_of(n: &Node, id: u32) -> Option<u64> {
    n.attr(id).and_then(Value::as_u64)
}

fn i64_of(n: &Node, id: u32) -> Option<i64> {
    n.attr(id).and_then(Value::as_i64)
}

fn bool_of(n: &Node, id: u32) -> bool {
    n.attr(id).and_then(Value::as_bool).unwrap_or(false)
}

fn text_of(n: &Node, id: u32) -> Option<String> {
    n.attr(id).and_then(Value::as_str).map(str::to_owned)
}

fn i128_of(n: &Node, id: u32) -> i128 {
    match n.attr(id) {
        Some(Value::Signed(v)) => *v,
        Some(Value::Unsigned(v)) => i128::try_from(*v).unwrap_or(i128::MAX),
        Some(Value::Space(v)) => i128::from(*v),
        Some(Value::Bool(b)) => i128::from(*b),
        _ => 0,
    }
}

fn token_field(n: &Node) -> TokenField {
    TokenField {
        big_endian: bool_of(n, at::BIGENDIAN),
        signed: bool_of(n, at::SIGNBIT),
        start_bit: u64_of(n, at::STARTBIT).unwrap_or(0),
        end_bit: u64_of(n, at::ENDBIT).unwrap_or(0),
        start_byte: u64_of(n, at::STARTBYTE).unwrap_or(0),
        end_byte: u64_of(n, at::ENDBYTE).unwrap_or(0),
        shift: u64_of(n, at::SHIFT).unwrap_or(0),
    }
}

fn context_field(n: &Node) -> ContextField {
    ContextField {
        signed: bool_of(n, at::SIGNBIT),
        start_bit: u64_of(n, at::STARTBIT).unwrap_or(0),
        end_bit: u64_of(n, at::ENDBIT).unwrap_or(0),
        start_byte: u64_of(n, at::STARTBYTE).unwrap_or(0),
        end_byte: u64_of(n, at::ENDBYTE).unwrap_or(0),
        shift: u64_of(n, at::SHIFT).unwrap_or(0),
    }
}

/// The field element a symbol body carries, whichever of the two it is.
fn field_def(n: &Node) -> Option<FieldDef> {
    n.children.iter().find_map(|c| match c.id {
        el::TOKEN_FIELD => Some(FieldDef::Token(token_field(c))),
        el::CONTEXT_FIELD => Some(FieldDef::Context(context_field(c))),
        _ => None,
    })
}

fn expr(n: &Node) -> Expr {
    if let Some(op) = PatternOp::from_element(n.id) {
        return Expr::Op {
            op,
            operands: n.children.iter().map(expr).collect(),
        };
    }
    match n.id {
        el::OPERAND_VALUE => Expr::OperandValue {
            index: u64_of(n, at::INDEX).unwrap_or(0),
            table: u64_of(n, at::TABLE).unwrap_or(0),
            ct: u64_of(n, at::CT).unwrap_or(0),
        },
        el::PEXP_CONSTANT => Expr::Constant(i128_of(n, at::VAL)),
        el::CONTEXT_FIELD => Expr::Context(context_field(n)),
        el::TOKEN_FIELD => Expr::TokenField(token_field(n)),
        el::PEXP_INST_START => Expr::InstStart,
        el::PEXP_INST_NEXT => Expr::InstNext,
        el::PEXP_INST_NEXT2 => Expr::InstNext2,
        other => Expr::Unknown {
            element: other,
            operands: n.children.iter().map(expr).collect(),
        },
    }
}

fn const_template(n: &Node) -> ConstTemplate {
    match n.id {
        el::CONST_REAL => ConstTemplate::Real(i128_of(n, at::VAL)),
        el::CONST_SPACEID => ConstTemplate::SpaceId(
            n.attr(at::SPACE)
                .and_then(Value::as_space)
                .unwrap_or(u32::MAX),
        ),
        el::CONST_HANDLE => ConstTemplate::Handle {
            index: u64_of(n, at::VAL).unwrap_or(0),
            select: u64_of(n, at::SELECT).unwrap_or(0),
            extra: n.attr(28).and_then(|v| match v {
                Value::Unsigned(u) => Some(*u),
                Value::Signed(s) => u128::try_from(*s).ok(),
                _ => None,
            }),
        },
        el::CONST_RELATIVE => ConstTemplate::Relative(i128_of(n, at::VAL)),
        el::CONST_INST_START => ConstTemplate::InstStart,
        el::CONST_INST_NEXT => ConstTemplate::InstNext,
        el::CONST_INST_NEXT2 => ConstTemplate::InstNext2,
        el::CONST_CURSPACE => ConstTemplate::CurSpace,
        el::CONST_CURSPACE_SIZE => ConstTemplate::CurSpaceSize,
        other => ConstTemplate::Unknown(other),
    }
}

fn varnode_template(n: &Node) -> VarnodeTemplate {
    let mut parts = n.children.iter().map(const_template);
    VarnodeTemplate {
        space: parts.next().unwrap_or(ConstTemplate::Unknown(0)),
        offset: parts.next().unwrap_or(ConstTemplate::Unknown(0)),
        size: parts.next().unwrap_or(ConstTemplate::Unknown(0)),
    }
}

fn op_template(n: &Node) -> OpTemplate {
    let mut out = None;
    let mut inputs = Vec::new();
    // The first child is the output: a varnode template, or `null` when the
    // operation has no output.
    for (i, c) in n.children.iter().enumerate() {
        match (i, c.id) {
            (0, el::NULL) => {}
            (0, el::VARNODE_TPL) => out = Some(varnode_template(c)),
            (_, el::VARNODE_TPL) => inputs.push(varnode_template(c)),
            _ => {}
        }
    }
    OpTemplate {
        opcode: u64_of(n, at::CODE).unwrap_or(0),
        output: out,
        inputs,
    }
}

fn construct_template(n: &Node) -> ConstructTemplate {
    let mut t = ConstructTemplate {
        section: i64_of(n, at::SECTION),
        labels: u64_of(n, at::LABELS),
        delay: i64_of(n, at::DELAY),
        ..ConstructTemplate::default()
    };
    for c in &n.children {
        match c.id {
            el::HANDLE_TPL => t.result = Some(c.children.iter().map(const_template).collect()),
            el::OP_TPL => t.ops.push(op_template(c)),
            _ => {}
        }
    }
    t
}

fn pattern_block(n: &Node) -> PatternBlock {
    PatternBlock {
        offset: u64_of(n, at::OFF).unwrap_or(0),
        bytes: u64_of(n, at::NBYTES).unwrap_or(0),
        words: n
            .children
            .iter()
            .filter(|c| c.id == el::PATTERN_WORD)
            .map(|c| PatternWord {
                mask: u64_of(c, at::MASK).unwrap_or(0),
                value: u64_of(c, at::VAL).unwrap_or(0),
            })
            .collect(),
    }
}

fn pattern(n: &Node, out: &mut Pattern) {
    match n.id {
        el::CONTEXT_PATTERN => {
            out.has_context = true;
            out.context.extend(
                n.children
                    .iter()
                    .filter(|c| c.id == el::PATTERN_BLOCK)
                    .map(pattern_block),
            );
        }
        el::INSTRUCTION_PATTERN => {
            out.has_instruction = true;
            out.instruction.extend(
                n.children
                    .iter()
                    .filter(|c| c.id == el::PATTERN_BLOCK)
                    .map(pattern_block),
            );
        }
        el::COMBINE_PATTERN => {
            out.combined = true;
            for c in &n.children {
                pattern(c, out);
            }
        }
        _ => {}
    }
}

fn decision(n: &Node) -> Decision {
    let mut d = Decision {
        number: u64_of(n, at::NUMBER).unwrap_or(0),
        on_context: bool_of(n, at::CONTEXT),
        start_bit: u64_of(n, at::STARTBIT).unwrap_or(0),
        num_bits: u64_of(n, at::SIZE).unwrap_or(0),
        children: Vec::new(),
        pairs: Vec::new(),
    };
    for c in &n.children {
        match c.id {
            el::DECISION => d.children.push(decision(c)),
            el::DECISION_PAIR => {
                let mut p = Pattern::default();
                for g in &c.children {
                    pattern(g, &mut p);
                }
                let idx = u64_of(c, at::ID).unwrap_or(0);
                d.pairs.push((u32::try_from(idx).unwrap_or(u32::MAX), p));
            }
            _ => {}
        }
    }
    d
}

fn constructor(n: &Node) -> Constructor {
    let mut c = Constructor {
        parent: u64_of(n, at::PARENT)
            .and_then(|v| u32::try_from(v).ok())
            .unwrap_or(0),
        source: u64_of(n, at::SOURCE).unwrap_or(0),
        line: u64_of(n, at::LINE).unwrap_or(0),
        length: u64_of(n, at::LENGTH).unwrap_or(0),
        flowthru: i64_of(n, at::FLOWTHRU).unwrap_or(0),
        operands: Vec::new(),
        print: Vec::new(),
        context_ops: Vec::new(),
        templates: Vec::new(),
    };
    for k in &n.children {
        match k.id {
            el::CONSTRUCTOR_OPERAND => {
                if let Some(v) = u64_of(k, at::ID).and_then(|v| u32::try_from(v).ok()) {
                    c.operands.push(v);
                }
            }
            el::PRINT_LITERAL => {
                c.print.push(PrintPiece::Literal(
                    text_of(k, at::PIECE).unwrap_or_default(),
                ));
            }
            el::PRINT_OPERAND => c
                .print
                .push(PrintPiece::Operand(u64_of(k, at::ID).unwrap_or(0))),
            el::CONTEXT_CHANGE => c.context_ops.push(ContextOp::Set {
                word: u64_of(k, at::WORD).unwrap_or(0),
                shift: u64_of(k, at::SHIFT).unwrap_or(0),
                mask: u64_of(k, at::MASK).unwrap_or(0),
                value: k.children.iter().map(expr).collect(),
            }),
            el::GLOBALSET => c.context_ops.push(ContextOp::Commit {
                symbol: u64_of(k, at::ID)
                    .and_then(|v| u32::try_from(v).ok())
                    .unwrap_or(u32::MAX),
                word: u64_of(k, at::NUMBER).unwrap_or(0),
                mask: u64_of(k, at::MASK).unwrap_or(0),
                flow: bool_of(k, at::FLOW),
            }),
            el::CONSTRUCT_TPL => c.templates.push(construct_template(k)),
            _ => {}
        }
    }
    c
}

fn symbol_body(n: &Node) -> SymbolBody {
    match n.id {
        el::VARNODE_SYM => SymbolBody::Varnode {
            space: n
                .attr(at::SPACE)
                .and_then(Value::as_space)
                .unwrap_or(u32::MAX),
            offset: u64_of(n, at::OFF).unwrap_or(0),
            size: u64_of(n, at::SIZE).unwrap_or(0),
        },
        el::USEROP_SYM => SymbolBody::UserOp {
            index: u64_of(n, at::INDEX).unwrap_or(0),
        },
        el::VALUE_SYM => SymbolBody::Value {
            field: field_def(n),
        },
        el::VALUEMAP_SYM => SymbolBody::ValueMap {
            field: field_def(n),
            values: n
                .children
                .iter()
                .filter(|c| c.id == el::VALUEMAP_ENTRY)
                .map(|c| i128_of(c, at::VAL))
                .collect(),
        },
        el::NAME_SYM => SymbolBody::Name {
            field: field_def(n),
            names: n
                .children
                .iter()
                .filter(|c| c.id == el::NAME_ENTRY)
                .map(|c| text_of(c, at::NAME))
                .collect(),
        },
        el::VARNODE_LIST_SYM => SymbolBody::VarnodeList {
            field: field_def(n),
            entries: n
                .children
                .iter()
                .filter(|c| c.id == el::VARNODE_LIST_ENTRY || c.id == el::NULL)
                .map(|c| {
                    if c.id == el::NULL {
                        None
                    } else {
                        u64_of(c, at::ID).and_then(|v| u32::try_from(v).ok())
                    }
                })
                .collect(),
        },
        el::CONTEXT_SYM => SymbolBody::Context {
            varnode: u64_of(n, at::VARNODE)
                .and_then(|v| u32::try_from(v).ok())
                .unwrap_or(u32::MAX),
            low: u64_of(n, at::LOW).unwrap_or(0),
            high: u64_of(n, at::HIGH).unwrap_or(0),
            flow: bool_of(n, at::FLOW),
            field: n.child(el::CONTEXT_FIELD).map(context_field),
        },
        el::OPERAND_SYM => SymbolBody::Operand {
            index: u64_of(n, at::INDEX).unwrap_or(0),
            offset: u64_of(n, at::OFF).unwrap_or(0),
            sub_symbol: u64_of(n, at::SUBSYM).and_then(|v| u32::try_from(v).ok()),
            base: i64_of(n, at::OPERAND_19).unwrap_or(-1),
            min_length: u64_of(n, at::OPERAND_18).unwrap_or(0),
            flag: n.attr(at::CODE).and_then(Value::as_bool),
            expr: n.children.iter().map(expr).collect(),
        },
        el::START_SYM => SymbolBody::Start,
        el::END_SYM => SymbolBody::End,
        el::NEXT2_SYM => SymbolBody::Next2,
        el::SUBTABLE_SYM => SymbolBody::Subtable {
            constructors: n
                .children
                .iter()
                .filter(|c| c.id == el::CONSTRUCTOR)
                .map(constructor)
                .collect(),
            decision: n.child(el::DECISION).map(decision),
        },
        other => SymbolBody::Unknown { element: other },
    }
}

/// Symbol header elements sit one id below their body element, in every pair
/// observed. Headers carry the name and the scope; bodies carry everything
/// else and come later in the same table.
fn header_body_of(id: u32) -> Option<u32> {
    const HEADERS: [u32; 12] = [14, 24, 26, 40, 42, 44, 65, 68, 70, 72, 74, 77];
    HEADERS.contains(&id).then(|| id - 1)
}

pub(crate) fn build(root: &Node) -> Program {
    let mut p = Program {
        version: u64_of(root, at::VERSION),
        big_endian: bool_of(root, at::BIGENDIAN),
        alignment: u64_of(root, at::ALIGN).unwrap_or(1),
        unique_base: u64_of(root, at::UNIQBASE).unwrap_or(0),
        extra_root_attrs: root
            .attrs
            .iter()
            .filter(|(a, _)| !matches!(*a, at::VERSION | at::BIGENDIAN | at::ALIGN | at::UNIQBASE))
            .cloned()
            .collect(),
        ..Program::default()
    };
    for top in &root.children {
        match top.id {
            el::SOURCEFILES => {
                for f in top.children.iter().filter(|c| c.id == el::SOURCEFILE) {
                    p.source_files.push(SourceFile {
                        name: text_of(f, at::NAME).unwrap_or_default(),
                        index: u64_of(f, at::INDEX).unwrap_or(0),
                    });
                }
            }
            el::SPACES => {
                p.default_space = text_of(top, at::DEFAULTSPACE);
                for s in &top.children {
                    let kind = match s.id {
                        el::SPACE => SpaceKind::Normal,
                        el::SPACE_OTHER => SpaceKind::Other,
                        el::SPACE_UNIQUE => SpaceKind::Unique,
                        _ => continue,
                    };
                    p.spaces.push(Space {
                        kind,
                        name: text_of(s, at::NAME).unwrap_or_default(),
                        index: u64_of(s, at::INDEX)
                            .and_then(|v| u32::try_from(v).ok())
                            .unwrap_or(u32::MAX),
                        big_endian: bool_of(s, at::BIGENDIAN),
                        delay: u64_of(s, at::DELAY).unwrap_or(0),
                        size: u64_of(s, at::SIZE).unwrap_or(0),
                        word_size: u64_of(s, at::WORDSIZE).unwrap_or(1),
                        physical: bool_of(s, at::PHYSICAL),
                    });
                }
            }
            el::SYMBOL_TABLE => {
                p.declared_scopes = u64_of(top, at::SCOPESIZE);
                p.declared_symbols = u64_of(top, at::SYMBOLSIZE);
                let mut names: Vec<(u32, String, Option<u32>)> = Vec::new();
                for s in &top.children {
                    if s.id == el::SCOPE {
                        p.scopes.push(Scope {
                            id: u64_of(s, at::ID)
                                .and_then(|v| u32::try_from(v).ok())
                                .unwrap_or(0),
                            parent: u64_of(s, at::PARENT)
                                .and_then(|v| u32::try_from(v).ok())
                                .unwrap_or(0),
                        });
                    } else if header_body_of(s.id).is_some() {
                        names.push((
                            u64_of(s, at::ID)
                                .and_then(|v| u32::try_from(v).ok())
                                .unwrap_or(0),
                            text_of(s, at::NAME).unwrap_or_default(),
                            u64_of(s, at::SCOPE).and_then(|v| u32::try_from(v).ok()),
                        ));
                    } else {
                        let id = u64_of(s, at::ID)
                            .and_then(|v| u32::try_from(v).ok())
                            .unwrap_or(u32::MAX);
                        p.symbols.push(Symbol {
                            id,
                            name: None,
                            scope: None,
                            body: symbol_body(s),
                        });
                    }
                }
                // A linear search per header would be quadratic, and a real
                // language has hundreds of thousands of symbols. Index once.
                let mut by_id: Vec<(u32, usize)> = p
                    .symbols
                    .iter()
                    .enumerate()
                    .map(|(i, s)| (s.id, i))
                    .collect();
                by_id.sort_unstable();
                for (id, name, scope) in names {
                    if let Ok(k) = by_id.binary_search_by_key(&id, |(i, _)| *i) {
                        let sym = &mut p.symbols[by_id[k].1];
                        sym.name = Some(name);
                        sym.scope = scope;
                    }
                }
                p.symbol_index = by_id;
            }
            _ => {}
        }
    }
    p
}

/// Everything the model understands about one `.sla`.
#[derive(Debug, Clone, Default)]
pub struct Program {
    /// The `version` attribute on the root element, 4 in every file seen.
    pub version: Option<u64>,
    pub big_endian: bool,
    pub alignment: u64,
    pub unique_base: u64,
    /// Attributes on the root element beyond the four that are established.
    /// Thirteen of the shipped files carry attribute 38 and one carries 39 and
    /// 40; nothing says what they mean, so they are carried through rather
    /// than dropped, and the writer puts them back where they were.
    pub extra_root_attrs: Vec<(u32, Value)>,
    pub source_files: Vec<SourceFile>,
    pub default_space: Option<String>,
    pub spaces: Vec<Space>,
    pub scopes: Vec<Scope>,
    pub symbols: Vec<Symbol>,
    /// The symbol table's own count attributes, kept so a reader can check
    /// them against what it actually found rather than trusting either.
    pub declared_scopes: Option<u64>,
    pub declared_symbols: Option<u64>,
    /// `(symbol id, index into symbols)` sorted by id. Symbol ids are dense in
    /// every file seen, but nothing in the format says they must be, so the
    /// lookup is a binary search rather than an index.
    symbol_index: Vec<(u32, usize)>,
}

impl Program {
    /// An empty program, for a compiler to fill in.
    ///
    /// Every field is public except the symbol id index, which has to stay in
    /// step with `symbols`; [`Program::reindex`] is how that is said.
    #[must_use]
    pub fn empty() -> Self {
        Self::default()
    }

    /// Rebuild the symbol id index.
    ///
    /// A program that was read from a file has one already. A program a
    /// compiler built has to say when its symbol list is final, and the index
    /// is not derived lazily because every lookup would then have to decide
    /// whether it is stale.
    pub fn reindex(&mut self) {
        let mut by_id: Vec<(u32, usize)> = self
            .symbols
            .iter()
            .enumerate()
            .map(|(i, s)| (s.id, i))
            .collect();
        by_id.sort_unstable();
        self.symbol_index = by_id;
    }

    #[must_use]
    pub fn symbol(&self, id: u32) -> Option<&Symbol> {
        let k = self
            .symbol_index
            .binary_search_by_key(&id, |(i, _)| *i)
            .ok()?;
        self.symbols.get(self.symbol_index[k].1)
    }

    /// Whether a symbol with this id exists, in logarithmic time.
    #[must_use]
    pub fn has_symbol(&self, id: u32) -> bool {
        self.symbol_index
            .binary_search_by_key(&id, |(i, _)| *i)
            .is_ok()
    }

    /// Registers, which are the varnode symbols in a register space.
    pub fn registers(&self) -> impl Iterator<Item = &Symbol> {
        self.symbols
            .iter()
            .filter(|s| matches!(s.body, SymbolBody::Varnode { .. }))
    }

    pub fn subtables(&self) -> impl Iterator<Item = &Symbol> {
        self.symbols
            .iter()
            .filter(|s| matches!(s.body, SymbolBody::Subtable { .. }))
    }

    /// Total constructors across every subtable.
    #[must_use]
    pub fn constructor_count(&self) -> usize {
        self.symbols
            .iter()
            .map(|s| match &s.body {
                SymbolBody::Subtable { constructors, .. } => constructors.len(),
                _ => 0,
            })
            .sum()
    }
}
