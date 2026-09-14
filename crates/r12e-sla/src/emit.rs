//! Turning a [`Program`] back into the tagged element tree a `.sla` holds.
//!
//! [`crate::encode`] writes a tree; this decides what the tree is. It is the
//! structured half of the writer and the half where the format document is
//! actually load bearing: which element carries which field, in which order,
//! with which value type. Getting any of that wrong produces a file our own
//! reader still likes, so the gate is not our reader. The gate is that every
//! `.sla` Ghidra ships, read into a [`Program`] and written back out through
//! here, is byte for byte the file it came from.
//!
//! Two things that gate found and that a writer has to get right:
//!
//! * the value type matters. An offset is written as an unsigned integer and a
//!   size as a signed one, in the same element, and the bytes differ. Every
//!   choice here was read off the corpus, one `(element, attribute)` pair at a
//!   time.
//! * an absent element is not an empty one. A pattern with no context half and
//!   a pattern whose context half holds no blocks are different files, so the
//!   model records which it saw rather than flattening them.

use crate::decode::{Node, Value};
use crate::encode::Build;
use crate::ids::{at, el};
use crate::model::{
    ConstTemplate, ConstructTemplate, Constructor, ContextField, ContextOp, Decision, Expr,
    FieldDef, OpTemplate, Pattern, PatternBlock, PrintPiece, Program, Space, SpaceKind, Symbol,
    SymbolBody, TokenField, VarnodeTemplate,
};

/// Something in the model that has no representation in the file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EmitError {
    /// A symbol the reader kept as an unnamed element. Its children were not
    /// interpreted, so they cannot be written back.
    UnknownSymbolBody { id: u32, element: u32 },
    /// A pattern expression or template leaf whose element id has no
    /// established meaning, for the same reason.
    UnknownElement { element: u32 },
}

impl core::fmt::Display for EmitError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::UnknownSymbolBody { id, element } => {
                write!(
                    f,
                    "symbol {id} has an uninterpreted body, element {element}"
                )
            }
            Self::UnknownElement { element } => {
                write!(f, "element {element} has no established meaning")
            }
        }
    }
}

impl std::error::Error for EmitError {}

type R<T> = Result<T, EmitError>;

/// The body element id for a symbol, and the header element id, which is one
/// above it in every pair.
fn body_element(b: &SymbolBody) -> u32 {
    match b {
        SymbolBody::Operand { .. } => el::OPERAND_SYM,
        SymbolBody::Varnode { .. } => el::VARNODE_SYM,
        SymbolBody::UserOp { .. } => el::USEROP_SYM,
        SymbolBody::Value { .. } => el::VALUE_SYM,
        SymbolBody::Context { .. } => el::CONTEXT_SYM,
        SymbolBody::End => el::END_SYM,
        SymbolBody::Name { .. } => el::NAME_SYM,
        SymbolBody::Next2 => el::NEXT2_SYM,
        SymbolBody::Start => el::START_SYM,
        SymbolBody::Subtable { .. } => el::SUBTABLE_SYM,
        SymbolBody::ValueMap { .. } => el::VALUEMAP_SYM,
        SymbolBody::VarnodeList { .. } => el::VARNODE_LIST_SYM,
        SymbolBody::Unknown { element } => *element,
    }
}

/// Build the whole tree for a program.
///
/// # Errors
/// Returns [`EmitError`] when the model holds a region the reader kept
/// uninterpreted, since there is nothing to write for it.
pub fn tree(p: &Program) -> R<Node> {
    let mut root = Build::new(el::SLEIGH)
        .attr(
            at::VERSION,
            Value::Signed(i128::from(p.version.unwrap_or(4))),
        )
        .bool(at::BIGENDIAN, p.big_endian)
        .attr(at::ALIGN, Value::Signed(i128::from(p.alignment)))
        .attr(at::UNIQBASE, Value::Unsigned(u128::from(p.unique_base)));
    for (id, v) in &p.extra_root_attrs {
        root = root.attr(*id, v.clone());
    }

    let mut files = Build::new(el::SOURCEFILES);
    for f in &p.source_files {
        files.push(
            Build::new(el::SOURCEFILE)
                .text(at::NAME, f.name.clone())
                .attr(at::INDEX, Value::Signed(i128::from(f.index))),
        );
    }
    root = root.child(files);

    let mut spaces = Build::new(el::SPACES);
    if let Some(d) = &p.default_space {
        spaces = spaces.text(at::DEFAULTSPACE, d.clone());
    }
    for s in &p.spaces {
        spaces.push(space(s));
    }
    root = root.child(spaces);

    let mut table = Build::new(el::SYMBOL_TABLE);
    if let Some(n) = p.declared_scopes {
        table = table.attr(at::SCOPESIZE, Value::Signed(i128::from(n)));
    }
    if let Some(n) = p.declared_symbols {
        table = table.attr(at::SYMBOLSIZE, Value::Signed(i128::from(n)));
    }
    for sc in &p.scopes {
        table.push(
            Build::new(el::SCOPE)
                .attr(at::ID, Value::Unsigned(u128::from(sc.id)))
                .attr(at::PARENT, Value::Unsigned(u128::from(sc.parent))),
        );
    }
    // Headers first, then bodies: two runs, not one interleaved one.
    for s in &p.symbols {
        table.push(header(s));
    }
    for s in &p.symbols {
        table.push(body(s)?);
    }
    Ok(root.child(table).finish())
}

fn space(s: &Space) -> Build {
    let id = match s.kind {
        SpaceKind::Normal => el::SPACE,
        SpaceKind::Other => el::SPACE_OTHER,
        SpaceKind::Unique => el::SPACE_UNIQUE,
    };
    let mut b = Build::new(id)
        .text(at::NAME, s.name.clone())
        .attr(at::INDEX, Value::Signed(i128::from(s.index)))
        .bool(at::BIGENDIAN, s.big_endian)
        .attr(at::DELAY, Value::Signed(i128::from(s.delay)))
        .attr(at::SIZE, Value::Signed(i128::from(s.size)));
    // A word size of one is the default and no file writes it.
    if s.word_size != 1 {
        b = b.attr(at::WORDSIZE, Value::Signed(i128::from(s.word_size)));
    }
    b.bool(at::PHYSICAL, s.physical)
}

fn header(s: &Symbol) -> Build {
    Build::new(body_element(&s.body) + 1)
        .text(at::NAME, s.name.clone().unwrap_or_default())
        .attr(at::ID, Value::Unsigned(u128::from(s.id)))
        .attr(at::SCOPE, Value::Unsigned(u128::from(s.scope.unwrap_or(0))))
}

fn token_field(f: &TokenField) -> Build {
    Build::new(el::TOKEN_FIELD)
        .bool(at::BIGENDIAN, f.big_endian)
        .bool(at::SIGNBIT, f.signed)
        .attr(at::STARTBIT, Value::Signed(i128::from(f.start_bit)))
        .attr(at::ENDBIT, Value::Signed(i128::from(f.end_bit)))
        .attr(at::STARTBYTE, Value::Signed(i128::from(f.start_byte)))
        .attr(at::ENDBYTE, Value::Signed(i128::from(f.end_byte)))
        .attr(at::SHIFT, Value::Signed(i128::from(f.shift)))
}

fn context_field(f: &ContextField) -> Build {
    Build::new(el::CONTEXT_FIELD)
        .bool(at::SIGNBIT, f.signed)
        .attr(at::STARTBIT, Value::Signed(i128::from(f.start_bit)))
        .attr(at::ENDBIT, Value::Signed(i128::from(f.end_bit)))
        .attr(at::STARTBYTE, Value::Signed(i128::from(f.start_byte)))
        .attr(at::ENDBYTE, Value::Signed(i128::from(f.end_byte)))
        .attr(at::SHIFT, Value::Signed(i128::from(f.shift)))
}

fn field(f: &FieldDef) -> Build {
    match f {
        FieldDef::Token(t) => token_field(t),
        FieldDef::Context(c) => context_field(c),
    }
}

fn expr(e: &Expr) -> R<Build> {
    Ok(match e {
        Expr::OperandValue { index, table, ct } => Build::new(el::OPERAND_VALUE)
            .attr(at::INDEX, Value::Signed(i128::from(*index)))
            .attr(at::TABLE, Value::Unsigned(u128::from(*table)))
            .attr(at::CT, Value::Unsigned(u128::from(*ct))),
        Expr::Constant(v) => Build::new(el::PEXP_CONSTANT).attr(at::VAL, Value::Signed(*v)),
        Expr::Context(c) => context_field(c),
        Expr::TokenField(t) => token_field(t),
        Expr::InstStart => Build::new(el::PEXP_INST_START),
        Expr::InstNext => Build::new(el::PEXP_INST_NEXT),
        Expr::InstNext2 => Build::new(el::PEXP_INST_NEXT2),
        Expr::Op { op, operands } => {
            let mut b = Build::new(op.element());
            for o in operands {
                b.push(expr(o)?);
            }
            b
        }
        Expr::Unknown { element, .. } => {
            return Err(EmitError::UnknownElement { element: *element });
        }
    })
}

fn const_template(c: &ConstTemplate) -> R<Build> {
    Ok(match c {
        ConstTemplate::Real(v) => Build::new(el::CONST_REAL).attr(
            at::VAL,
            Value::Unsigned(u128::try_from(*v).unwrap_or_default()),
        ),
        ConstTemplate::SpaceId(ix) => Build::new(el::CONST_SPACEID).space(at::SPACE, *ix),
        ConstTemplate::Handle {
            index,
            select,
            extra,
        } => {
            let b = Build::new(el::CONST_HANDLE)
                .attr(at::VAL, Value::Signed(i128::from(*index)))
                .attr(at::SELECT, Value::Signed(i128::from(*select)));
            match extra {
                Some(x) => b.attr(at::HANDLE_28, Value::Unsigned(*x)),
                None => b,
            }
        }
        ConstTemplate::Relative(v) => Build::new(el::CONST_RELATIVE).attr(
            at::VAL,
            Value::Unsigned(u128::try_from(*v).unwrap_or_default()),
        ),
        ConstTemplate::InstStart => Build::new(el::CONST_INST_START),
        ConstTemplate::InstNext => Build::new(el::CONST_INST_NEXT),
        ConstTemplate::InstNext2 => Build::new(el::CONST_INST_NEXT2),
        ConstTemplate::CurSpace => Build::new(el::CONST_CURSPACE),
        ConstTemplate::CurSpaceSize => Build::new(el::CONST_CURSPACE_SIZE),
        ConstTemplate::Unknown(element) => {
            return Err(EmitError::UnknownElement { element: *element });
        }
    })
}

fn varnode_template(v: &VarnodeTemplate) -> R<Build> {
    Ok(Build::new(el::VARNODE_TPL)
        .child(const_template(&v.space)?)
        .child(const_template(&v.offset)?)
        .child(const_template(&v.size)?))
}

fn op_template(o: &OpTemplate) -> R<Build> {
    let mut b = Build::new(el::OP_TPL).attr(at::CODE, Value::Signed(i128::from(o.opcode)));
    match &o.output {
        Some(v) => b.push(varnode_template(v)?),
        None => b.push(Build::new(el::NULL)),
    }
    for i in &o.inputs {
        b.push(varnode_template(i)?);
    }
    Ok(b)
}

fn construct_template(t: &ConstructTemplate) -> R<Build> {
    let mut b = Build::new(el::CONSTRUCT_TPL);
    if let Some(d) = t.delay {
        b = b.attr(at::DELAY, Value::Signed(i128::from(d)));
    }
    if let Some(s) = t.section {
        b = b.attr(at::SECTION, Value::Signed(i128::from(s)));
    }
    if let Some(l) = t.labels {
        b = b.attr(at::LABELS, Value::Signed(i128::from(l)));
    }
    // The export slot is always written, and always first: a handle when the
    // constructor exports one, an explicit `null` when it does not. All
    // 128,421 of them in the corpus have it, so an absent slot is not a shape
    // the format has.
    match &t.result {
        Some(parts) => {
            let mut h = Build::new(el::HANDLE_TPL);
            for c in parts {
                h.push(const_template(c)?);
            }
            b.push(h);
        }
        None => b.push(Build::new(el::NULL)),
    }
    for o in &t.ops {
        b.push(op_template(o)?);
    }
    Ok(b)
}

fn pattern_block(p: &PatternBlock) -> Build {
    let mut b = Build::new(el::PATTERN_BLOCK)
        .attr(at::OFF, Value::Signed(i128::from(p.offset)))
        .attr(at::NBYTES, Value::Signed(i128::from(p.bytes)));
    for w in &p.words {
        b.push(
            Build::new(el::PATTERN_WORD)
                .attr(at::MASK, Value::Unsigned(u128::from(w.mask)))
                .attr(at::VAL, Value::Unsigned(u128::from(w.value))),
        );
    }
    b
}

fn half(id: u32, blocks: &[PatternBlock]) -> Build {
    let mut b = Build::new(id);
    for blk in blocks {
        b.push(pattern_block(blk));
    }
    b
}

fn pattern(p: &Pattern) -> Build {
    if p.combined {
        return Build::new(el::COMBINE_PATTERN)
            .child(half(el::CONTEXT_PATTERN, &p.context))
            .child(half(el::INSTRUCTION_PATTERN, &p.instruction));
    }
    if p.has_context {
        return half(el::CONTEXT_PATTERN, &p.context);
    }
    half(el::INSTRUCTION_PATTERN, &p.instruction)
}

fn decision(d: &Decision) -> Build {
    let mut b = Build::new(el::DECISION)
        .attr(at::NUMBER, Value::Signed(i128::from(d.number)))
        .bool(at::CONTEXT, d.on_context)
        .attr(at::STARTBIT, Value::Signed(i128::from(d.start_bit)))
        .attr(at::SIZE, Value::Signed(i128::from(d.num_bits)));
    for c in &d.children {
        b.push(decision(c));
    }
    for (ix, pat) in &d.pairs {
        b.push(
            Build::new(el::DECISION_PAIR)
                .attr(at::ID, Value::Signed(i128::from(*ix)))
                .child(pattern(pat)),
        );
    }
    b
}

fn constructor(c: &Constructor) -> R<Build> {
    let mut b = Build::new(el::CONSTRUCTOR)
        .attr(at::PARENT, Value::Unsigned(u128::from(c.parent)))
        .attr(at::FLOWTHRU, Value::Signed(i128::from(c.flowthru)))
        .attr(at::LENGTH, Value::Signed(i128::from(c.length)))
        .attr(at::SOURCE, Value::Signed(i128::from(c.source)))
        .attr(at::LINE, Value::Signed(i128::from(c.line)));
    for o in &c.operands {
        b.push(Build::new(el::CONSTRUCTOR_OPERAND).attr(at::ID, Value::Unsigned(u128::from(*o))));
    }
    for piece in &c.print {
        b.push(match piece {
            PrintPiece::Literal(s) => Build::new(el::PRINT_LITERAL).text(at::PIECE, s.clone()),
            PrintPiece::Operand(i) => {
                Build::new(el::PRINT_OPERAND).attr(at::ID, Value::Signed(i128::from(*i)))
            }
        });
    }
    for op in &c.context_ops {
        b.push(match op {
            ContextOp::Set {
                word,
                shift,
                mask,
                value,
            } => {
                let mut n = Build::new(el::CONTEXT_CHANGE)
                    .attr(at::WORD, Value::Signed(i128::from(*word)))
                    .attr(at::SHIFT, Value::Signed(i128::from(*shift)))
                    .attr(at::MASK, Value::Unsigned(u128::from(*mask)));
                for v in value {
                    n.push(expr(v)?);
                }
                n
            }
            ContextOp::Commit {
                symbol,
                word,
                mask,
                flow,
            } => Build::new(el::GLOBALSET)
                .attr(at::ID, Value::Unsigned(u128::from(*symbol)))
                .attr(at::NUMBER, Value::Signed(i128::from(*word)))
                .attr(at::MASK, Value::Unsigned(u128::from(*mask)))
                .bool(at::FLOW, *flow),
        });
    }
    for t in &c.templates {
        b.push(construct_template(t)?);
    }
    Ok(b)
}

fn body(s: &Symbol) -> R<Build> {
    let id = Value::Unsigned(u128::from(s.id));
    Ok(match &s.body {
        SymbolBody::Varnode {
            space,
            offset,
            size,
        } => Build::new(el::VARNODE_SYM)
            .attr(at::ID, id)
            .space(at::SPACE, *space)
            .attr(at::OFF, Value::Unsigned(u128::from(*offset)))
            .attr(at::SIZE, Value::Signed(i128::from(*size))),
        SymbolBody::UserOp { index } => Build::new(el::USEROP_SYM)
            .attr(at::ID, id)
            .attr(at::INDEX, Value::Signed(i128::from(*index))),
        SymbolBody::Value { field: f } => {
            let mut b = Build::new(el::VALUE_SYM).attr(at::ID, id);
            if let Some(f) = f {
                b.push(field(f));
            }
            b
        }
        SymbolBody::ValueMap { field: f, values } => {
            let mut b = Build::new(el::VALUEMAP_SYM).attr(at::ID, id);
            if let Some(f) = f {
                b.push(field(f));
            }
            for v in values {
                b.push(Build::new(el::VALUEMAP_ENTRY).attr(at::VAL, Value::Signed(*v)));
            }
            b
        }
        SymbolBody::Name { field: f, names } => {
            let mut b = Build::new(el::NAME_SYM).attr(at::ID, id);
            if let Some(f) = f {
                b.push(field(f));
            }
            for n in names {
                b.push(match n {
                    Some(text) => Build::new(el::NAME_ENTRY).text(at::NAME, text.clone()),
                    None => Build::new(el::NAME_ENTRY),
                });
            }
            b
        }
        SymbolBody::VarnodeList { field: f, entries } => {
            let mut b = Build::new(el::VARNODE_LIST_SYM).attr(at::ID, id);
            if let Some(f) = f {
                b.push(field(f));
            }
            for e in entries {
                b.push(match e {
                    Some(v) => Build::new(el::VARNODE_LIST_ENTRY)
                        .attr(at::ID, Value::Unsigned(u128::from(*v))),
                    None => Build::new(el::NULL),
                });
            }
            b
        }
        SymbolBody::Context {
            varnode,
            low,
            high,
            flow,
            field: f,
        } => {
            let mut b = Build::new(el::CONTEXT_SYM)
                .attr(at::ID, id)
                .attr(at::VARNODE, Value::Unsigned(u128::from(*varnode)))
                .attr(at::LOW, Value::Signed(i128::from(*low)))
                .attr(at::HIGH, Value::Signed(i128::from(*high)))
                .bool(at::FLOW, *flow);
            if let Some(f) = f {
                b.push(context_field(f));
            }
            b
        }
        SymbolBody::Operand {
            index,
            offset,
            sub_symbol,
            base,
            min_length,
            flag,
            expr: exprs,
        } => {
            let mut b = Build::new(el::OPERAND_SYM).attr(at::ID, id);
            if let Some(sub) = sub_symbol {
                b = b.attr(at::SUBSYM, Value::Unsigned(u128::from(*sub)));
            }
            b = b
                .attr(at::OFF, Value::Signed(i128::from(*offset)))
                .attr(at::OPERAND_19, Value::Signed(i128::from(*base)))
                .attr(at::OPERAND_18, Value::Signed(i128::from(*min_length)));
            if let Some(f) = flag {
                b = b.bool(at::CODE, *f);
            }
            b = b.attr(at::INDEX, Value::Signed(i128::from(*index)));
            for e in exprs {
                b.push(expr(e)?);
            }
            b
        }
        SymbolBody::Start => Build::new(el::START_SYM).attr(at::ID, id),
        SymbolBody::End => Build::new(el::END_SYM).attr(at::ID, id),
        SymbolBody::Next2 => Build::new(el::NEXT2_SYM).attr(at::ID, id),
        SymbolBody::Subtable {
            constructors,
            decision: dec,
        } => {
            let mut b = Build::new(el::SUBTABLE_SYM)
                .attr(at::ID, id)
                .attr(at::NUMCT, Value::Signed(constructors.len() as i128));
            for c in constructors {
                b.push(constructor(c)?);
            }
            if let Some(d) = dec {
                b.push(decision(d));
            }
            b
        }
        SymbolBody::Unknown { element } => {
            return Err(EmitError::UnknownSymbolBody {
                id: s.id,
                element: *element,
            });
        }
    })
}

/// Rebuild a whole `.sla` file image from a program.
///
/// # Errors
/// See [`tree`], plus anything the tag encoding cannot carry.
pub fn write(p: &Program, version: u8, level: crate::Level) -> Result<Vec<u8>, crate::SlaError> {
    let t = tree(p).map_err(crate::SlaError::Emit)?;
    crate::write_sla(&t, version, level)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Sla;

    fn fixture(name: &str) -> Sla {
        let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/data")
            .join(name);
        Sla::open(p).expect("fixture reads")
    }

    /// The claim in the smallest possible form: what the reference compiler
    /// wrote for this spec is what we write for the model of it.
    #[test]
    fn a_fixture_rebuilds_to_the_same_payload() {
        for name in ["minimal.sla", "tokens.sla", "subtable.sla"] {
            let sla = fixture(name);
            let rebuilt = tree(&sla.program).expect("emits");
            let bytes = crate::encode::encode(&rebuilt).expect("encodes");
            let original = crate::encode::encode(&sla.tree).expect("encodes");
            assert_eq!(bytes, original, "{name}");
        }
    }

    #[test]
    fn a_rebuilt_file_reads_back() {
        let sla = fixture("tokens.sla");
        let bytes = write(&sla.program, 4, crate::Level::Fixed).expect("writes");
        let back = Sla::parse(&bytes).expect("reads");
        assert_eq!(back.program.symbols.len(), sla.program.symbols.len());
        assert!(back.check().is_empty());
    }
}
