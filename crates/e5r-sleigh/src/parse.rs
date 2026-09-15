//! Recursive descent over preprocessed SLEIGH text.
//!
//! The grammar is small but has three context sensitive corners, and each one
//! is handled by the parser telling the scanner what to do rather than by the
//! scanner guessing:
//!
//! * the display section is raw text until the keyword `is`, so the parser
//!   rewinds any lookahead and calls [`Lexer::display_section`];
//! * inside a bit pattern `&`, `|` and `;` combine patterns, so the expression
//!   parser for the right hand side of a constraint is told to leave them
//!   alone and take `$and`, `$or` and `$xor` instead;
//! * `v(4)` shaves bytes off a varnode while `op(4)` calls a user operation,
//!   which is decided by what the name resolves to.
//!
//! Names resolve as they are read, into [`SymbolRef`], so nothing downstream
//! has to carry a symbol table. Tables are the one forward reference the
//! language allows: an unknown name in a pattern creates an empty table, and a
//! table still empty at the end of the file is the error it always was.
//!
//! Reference: the SLEIGH manual, sections 2 through 9.

use std::collections::HashMap;

use crate::error::{Error, Limits, Location, Result};
use crate::lex::{Lexer, Spanned, Tok};
use crate::model::*;
use crate::pattern;
use crate::preprocess::Source;

/// The largest number of operands one constructor may have. The index is a
/// `u16` and no real constructor comes near this.
const MAX_OPERANDS: usize = 4096;
/// The largest list an `attach` statement may carry.
const MAX_ATTACH: usize = 1 << 16;
/// The largest register list one `define` statement may carry.
const MAX_REGISTERS: usize = 1 << 16;
/// The largest token, in bits.
const MAX_TOKEN_BITS: u32 = 1024;

/// Parse preprocessed text into a [`Spec`].
pub fn parse(source: &Source, limits: Limits) -> Result<Spec> {
    let p = Parser::new(source, limits);
    let mut spec = p.run()?;
    spec.warnings.extend(source.warnings().iter().cloned());
    Ok(spec)
}

/// What is in scope inside one constructor or macro.
#[derive(Default)]
struct Scope {
    operands: Vec<Operand>,
    operand_index: HashMap<String, u16>,
    locals: Vec<Local>,
    local_index: HashMap<String, u16>,
    labels: Vec<String>,
    label_index: HashMap<String, u16>,
    params: Vec<String>,
    param_index: HashMap<String, u16>,
    /// False for a `with` header, where there is no constructor to hang
    /// operands off and every name is global.
    allow_operands: bool,
}

impl Scope {
    fn constructor() -> Scope {
        Scope {
            allow_operands: true,
            ..Scope::default()
        }
    }

    fn global() -> Scope {
        Scope::default()
    }

    fn operand(&mut self, name: &str, source: OperandSource, invisible: bool) -> Result<u16> {
        if let Some(&i) = self.operand_index.get(name) {
            let slot = &mut self.operands[i as usize];
            if slot.source == OperandSource::Unbound {
                slot.source = source;
            }
            return Ok(i);
        }
        if self.operands.len() >= MAX_OPERANDS {
            return Err(Error::new(format!(
                "a constructor with more than {MAX_OPERANDS} operands"
            )));
        }
        let i = self.operands.len() as u16;
        self.operand_index.insert(name.to_string(), i);
        self.operands.push(Operand {
            name: name.to_string(),
            source,
            offset: Offset::default(),
            invisible,
        });
        Ok(i)
    }

    fn local(&mut self, name: &str, size: Option<u32>) -> Result<u16> {
        if let Some(&i) = self.local_index.get(name) {
            if size.is_some() {
                self.locals[i as usize].size = size;
            }
            return Ok(i);
        }
        if self.locals.len() >= MAX_OPERANDS {
            return Err(Error::new("a body with too many temporaries"));
        }
        let i = self.locals.len() as u16;
        self.local_index.insert(name.to_string(), i);
        self.locals.push(Local {
            name: name.to_string(),
            size,
        });
        Ok(i)
    }

    fn label(&mut self, name: &str) -> Result<u16> {
        if let Some(&i) = self.label_index.get(name) {
            return Ok(i);
        }
        if self.labels.len() >= MAX_OPERANDS {
            return Err(Error::new("a body with too many labels"));
        }
        let i = self.labels.len() as u16;
        self.label_index.insert(name.to_string(), i);
        self.labels.push(name.to_string());
        Ok(i)
    }
}

/// One open `with` block.
struct With {
    table: Option<TableId>,
    pattern: Option<PatternExpr>,
    disasm: Vec<DisasmStmt>,
}

struct Parser<'a> {
    lex: Lexer<'a>,
    source: &'a Source,
    peeked: Option<Spanned>,
    peeked_at: usize,
    limits: Limits,
    spec: Spec,
    withs: Vec<With>,
    depth: usize,
    /// Tables a bit pattern referred to. A table that is only ever named by
    /// `crossbuild` or a `<<table>>` section is filled in from the sections of
    /// other constructors and has no constructors of its own, so it is not the
    /// misspelling an empty pattern-referenced table would be.
    pattern_tables: HashMap<u32, Location>,
}

impl<'a> Parser<'a> {
    fn new(source: &'a Source, limits: Limits) -> Parser<'a> {
        let mut spec = Spec {
            alignment: 1,
            ..Spec::default()
        };
        // The root table and the two built-in spaces exist before any line of
        // the specification is read.
        spec.tables.push(Table {
            name: "instruction".into(),
            constructors: Vec::new(),
            min_length: 0,
            max_length: 0,
        });
        spec.symbols
            .insert("instruction".into(), Symbol::Table(TableId(0)));
        for (name, kind) in [
            ("const", SpaceKind::Constant),
            ("unique", SpaceKind::Unique),
        ] {
            let id = SpaceId(spec.spaces.len() as u32);
            spec.spaces.push(Space {
                name: name.into(),
                kind,
                size: 8,
                wordsize: 1,
                default: false,
            });
            spec.symbols.insert(name.into(), Symbol::Space(id));
        }
        for (name, b) in [
            ("inst_start", Builtin::InstStart),
            ("inst_next", Builtin::InstNext),
            ("inst_next2", Builtin::InstNext2),
            ("epsilon", Builtin::Epsilon),
        ] {
            spec.symbols.insert(name.into(), Symbol::Builtin(b));
        }
        Parser {
            lex: Lexer::new(source.text()),
            source,
            peeked: None,
            peeked_at: 0,
            limits,
            spec,
            withs: Vec::new(),
            depth: 0,
            pattern_tables: HashMap::new(),
        }
    }

    // ---- token plumbing ----

    fn fill(&mut self) -> Result<()> {
        if self.peeked.is_none() {
            self.peeked_at = self.lex.offset();
            let t = self.lex.next_token().map_err(|e| self.here(e))?;
            self.peeked = Some(t);
        }
        Ok(())
    }

    fn peek(&mut self) -> Result<&Tok> {
        self.fill()?;
        Ok(&self.peeked.as_ref().expect("filled").tok)
    }

    fn next(&mut self) -> Result<Spanned> {
        self.fill()?;
        Ok(self.peeked.take().expect("filled"))
    }

    /// Where the parser is, so an error can name a file and line.
    fn mark(&mut self) -> usize {
        match &self.peeked {
            Some(_) => self.peeked_at,
            None => self.lex.offset(),
        }
    }

    fn reset(&mut self, mark: usize) {
        self.peeked = None;
        self.lex.seek(mark);
    }

    fn location(&mut self) -> Location {
        let at = self.mark();
        self.source
            .location(at)
            .unwrap_or_else(|| Location::new("<input>", 0))
    }

    fn here(&mut self, e: Error) -> Error {
        let at = self.location();
        e.or_at(&at)
    }

    fn fail<T>(&mut self, message: impl Into<String>) -> Result<T> {
        let at = self.location();
        Err(Error::at(at, message))
    }

    fn at_op(&mut self, op: &str) -> Result<bool> {
        Ok(matches!(self.peek()?, Tok::Op(o) if *o == op))
    }

    fn at_ident(&mut self, name: &str) -> Result<bool> {
        Ok(matches!(self.peek()?, Tok::Ident(i) if i == name))
    }

    fn at_eof(&mut self) -> Result<bool> {
        Ok(matches!(self.peek()?, Tok::Eof))
    }

    fn eat_op(&mut self, op: &str) -> Result<bool> {
        if self.at_op(op)? {
            self.next()?;
            return Ok(true);
        }
        Ok(false)
    }

    fn eat_ident(&mut self, name: &str) -> Result<bool> {
        if self.at_ident(name)? {
            self.next()?;
            return Ok(true);
        }
        Ok(false)
    }

    fn expect_op(&mut self, op: &str) -> Result<()> {
        if self.eat_op(op)? {
            return Ok(());
        }
        let found = self.peek()?.to_string();
        self.fail(format!("expected {op:?}, found {found}"))
    }

    fn expect_ident(&mut self) -> Result<String> {
        match self.next()?.tok {
            Tok::Ident(name) => Ok(name),
            other => self.fail(format!("expected a name, found {other}")),
        }
    }

    fn expect_num(&mut self) -> Result<u64> {
        match self.next()?.tok {
            Tok::Num(n) => Ok(n),
            other => self.fail(format!("expected a number, found {other}")),
        }
    }

    fn expect_size(&mut self) -> Result<u32> {
        let n = self.expect_num()?;
        u32::try_from(n).map_err(|_| Error::new(format!("{n} is not a plausible size")))
    }

    fn enter(&mut self) -> Result<()> {
        self.depth += 1;
        if self.depth > self.limits.expr_depth {
            return self.fail("an expression nests too deep");
        }
        Ok(())
    }

    fn leave(&mut self) {
        self.depth -= 1;
    }

    /// Count one more term in a flat operator chain.
    ///
    /// `a & b & c` parses in a loop, so it costs the parser no stack, but the
    /// tree it builds leans one level per term and everything that walks or
    /// drops that tree recurses. The length therefore needs the same kind of
    /// ceiling `enter` puts on parenthesised nesting; the corpus maximum is
    /// forty five terms, and the limit is two thousand.
    fn link(&mut self, chain: &mut usize) -> Result<()> {
        *chain += 1;
        if *chain > self.limits.expr_chain {
            return self.fail("an operator chain with too many terms");
        }
        Ok(())
    }

    // ---- top level ----

    fn run(mut self) -> Result<Spec> {
        loop {
            if self.at_eof()? {
                break;
            }
            if self.eat_op("}")? {
                if self.withs.pop().is_none() {
                    return self.fail("a } with no with block to close");
                }
                continue;
            }
            if self.at_op(":")? {
                self.next()?;
                self.constructor(None)?;
                continue;
            }
            let word = match self.peek()? {
                Tok::Ident(name) => name.clone(),
                other => {
                    let other = other.to_string();
                    return self.fail(format!("{other} cannot start a statement"));
                }
            };
            match word.as_str() {
                "define" => {
                    self.next()?;
                    self.definition()?;
                }
                "attach" => {
                    self.next()?;
                    self.attach()?;
                }
                "macro" => {
                    self.next()?;
                    self.macro_def()?;
                }
                "with" => {
                    self.next()?;
                    self.with_block()?;
                }
                _ => {
                    self.next()?;
                    self.expect_op(":")?;
                    self.constructor(Some(word))?;
                }
            }
        }
        if !self.withs.is_empty() {
            return self.fail("a with block is never closed");
        }
        self.finish()
    }

    fn finish(mut self) -> Result<Spec> {
        // A table a bit pattern names but nothing ever defines is a
        // misspelling somewhere: the parser created it on a forward reference
        // that never arrived.
        let mut hollow = Vec::new();
        for (i, table) in self.spec.tables.iter().enumerate().skip(1) {
            if !table.constructors.is_empty() {
                continue;
            }
            if let Some(at) = self.pattern_tables.get(&(i as u32)) {
                return Err(Error::at(
                    at.clone(),
                    format!("{} is used as a table but never defined", table.name),
                ));
            }
            hollow.push(table.name.clone());
        }
        for name in hollow {
            self.spec
                .warnings
                .push(format!("the table {name} has no constructors of its own"));
        }
        if self.spec.default_space.is_none() {
            if let Some(i) = self.spec.spaces.iter().position(|s| s.default) {
                self.spec.default_space = Some(SpaceId(i as u32));
            }
        }
        self.settle_lengths();
        self.reduce_patterns();
        Ok(self.spec)
    }

    /// Work out how many bytes each table's constructors take.
    ///
    /// Tables are mutually recursive in real specifications, so this is a
    /// fixpoint rather than a traversal. The two bounds have to be approached
    /// from opposite ends. The maximum grows from zero, and a table that
    /// recurses through a `;` grows past the ceiling, which is how a table of
    /// unbounded width is recognised. The minimum has to shrink from the
    /// ceiling instead: x86 writes prefix constructors as
    /// `:^instruction is ctx & instruction`, which consumes nothing of its own
    /// and recurses through `&`, so a minimum grown from zero is pinned at
    /// zero by its own previous value and never reaches the one byte the
    /// non-recursive constructors need.
    fn settle_lengths(&mut self) {
        let cap = self.limits.pattern_bytes;
        let mut lengths: Vec<(usize, usize)> = self
            .spec
            .tables
            .iter()
            .map(|t| {
                if t.constructors.is_empty() {
                    (0, 0)
                } else {
                    (cap, 0)
                }
            })
            .collect();
        // Every round moves each bound towards the other, neither passes the
        // ceiling, and a round that moves nothing stops: the count is belt and
        // braces against an arithmetic mistake here, not the termination
        // argument.
        let rounds = self
            .spec
            .tables
            .len()
            .saturating_add(cap)
            .saturating_add(8)
            .min(4096);
        let mut converged = false;
        for _ in 0..rounds {
            let mut changed = false;
            for (index, table) in self.spec.tables.iter().enumerate() {
                if table.constructors.is_empty() {
                    if lengths[index] != (0, 0) {
                        lengths[index] = (0, 0);
                        changed = true;
                    }
                    continue;
                }
                let mut low = cap;
                let mut high = 0usize;
                for id in &table.constructors {
                    let c = &self.spec.constructors[id.index()];
                    let sources: Vec<OperandSource> = c.operands.iter().map(|o| o.source).collect();
                    let (lo, hi) = pattern::length_of(
                        &c.pattern,
                        &sources,
                        &self.spec.tokens,
                        &self.spec.fields,
                        &lengths,
                        cap,
                    );
                    low = low.min(lo);
                    high = high.max(hi);
                }
                if (low, high) != lengths[index] {
                    lengths[index] = (low, high);
                    changed = true;
                }
            }
            if !changed {
                converged = true;
                break;
            }
        }
        if !converged {
            self.spec
                .warnings
                .push("table widths did not settle; lengths are bounds only".into());
        }
        for (table, (low, high)) in self.spec.tables.iter_mut().zip(&lengths) {
            table.min_length = *low;
            // A table that reached the ceiling is recursive through a
            // concatenation and has no finite width; saying so is better than
            // claiming the ceiling is its length.
            table.max_length = if *high >= cap { usize::MAX } else { *high };
        }
    }

    /// Reduce every constructor's pattern to masks, now that table widths are
    /// known, and record where each operand's token sits.
    fn reduce_patterns(&mut self) {
        let cap = self.limits.pattern_bytes;
        let table_min: Vec<usize> = self.spec.tables.iter().map(|t| t.min_length).collect();
        let table_max: Vec<usize> = self
            .spec
            .tables
            .iter()
            .map(|t| t.max_length.min(cap))
            .collect();
        let table_fixed: Vec<bool> = self
            .spec
            .tables
            .iter()
            .map(|t| t.is_fixed_length())
            .collect();
        let context_bytes = self.spec.context_bytes();
        let mut patterns = std::mem::take(&mut self.spec.constructors);
        for c in &mut patterns {
            let sources: Vec<OperandSource> = c.operands.iter().map(|o| o.source).collect();
            let reduction = pattern::reduce(
                &c.pattern,
                &pattern::Context {
                    tokens: &self.spec.tokens,
                    fields: &self.spec.fields,
                    context_fields: &self.spec.context_fields,
                    context_bytes,
                    operands: &sources,
                    table_min: &table_min,
                    table_max: &table_max,
                    table_fixed: &table_fixed,
                    limits: &self.limits,
                },
            );
            for (operand, offset) in c.operands.iter_mut().zip(&reduction.offsets) {
                operand.offset = offset.unwrap_or_default();
            }
            c.order = pattern::operand_order(&c.pattern, c.operands.len());
            c.resolved = reduction.resolved;
        }
        self.spec.constructors = patterns;
    }

    // ---- definitions ----

    fn definition(&mut self) -> Result<()> {
        let word = self.expect_ident()?;
        match word.as_str() {
            "endian" => {
                self.expect_op("=")?;
                let value = self.expect_ident()?;
                self.spec.endian = match value.as_str() {
                    "big" => Endian::Big,
                    "little" => Endian::Little,
                    _ => return self.fail(format!("{value} is not an endianness")),
                };
                self.expect_op(";")
            }
            "alignment" => {
                self.expect_op("=")?;
                self.spec.alignment = self.expect_size()?.max(1);
                self.expect_op(";")
            }
            "space" => self.space_def(),
            "token" => self.token_def(),
            "context" => self.context_def(),
            "bitrange" => self.bitrange_def(),
            "pcodeop" => {
                loop {
                    let name = self.expect_ident()?;
                    let id = PcodeOpId(self.spec.pcodeops.len() as u32);
                    self.spec.pcodeops.push(PcodeOp { name: name.clone() });
                    self.spec.symbols.insert(name, Symbol::PcodeOp(id));
                    if !self.eat_op(",")? {
                        break;
                    }
                }
                self.expect_op(";")
            }
            other => self.varnode_def(other),
        }
    }

    fn space_def(&mut self) -> Result<()> {
        let name = self.expect_ident()?;
        let mut kind = SpaceKind::Ram;
        let mut size = 0u32;
        let mut wordsize = 1u32;
        let mut default = false;
        while !self.eat_op(";")? {
            let attr = self.expect_ident()?;
            match attr.as_str() {
                "default" => default = true,
                "type" => {
                    self.expect_op("=")?;
                    let value = self.expect_ident()?;
                    kind = match value.as_str() {
                        "ram_space" => SpaceKind::Ram,
                        "register_space" => SpaceKind::Register,
                        "rom_space" => SpaceKind::Rom,
                        _ => return self.fail(format!("{value} is not an address space type")),
                    };
                }
                "size" => {
                    self.expect_op("=")?;
                    size = self.expect_size()?;
                }
                "wordsize" => {
                    self.expect_op("=")?;
                    wordsize = self.expect_size()?.max(1);
                }
                _ => return self.fail(format!("{attr} is not a space attribute")),
            }
        }
        if size == 0 || size > 16 {
            return self.fail(format!(
                "space {name} has an implausible address size {size}"
            ));
        }
        let id = SpaceId(self.spec.spaces.len() as u32);
        self.spec.spaces.push(Space {
            name: name.clone(),
            kind,
            size,
            wordsize,
            default,
        });
        if default {
            self.spec.default_space = Some(id);
        }
        self.spec.symbols.insert(name, Symbol::Space(id));
        Ok(())
    }

    fn varnode_def(&mut self, space_name: &str) -> Result<()> {
        let Some(Symbol::Space(space)) = self.spec.lookup(space_name) else {
            return self.fail(format!("{space_name} is not a define keyword or a space"));
        };
        let mut offset = 0u64;
        let mut size = 0u32;
        while !self.at_op("[")? {
            if matches!(self.peek()?, Tok::Ident(_))
                && !self.at_ident("offset")?
                && !self.at_ident("size")?
            {
                break;
            }
            let attr = self.expect_ident()?;
            self.expect_op("=")?;
            match attr.as_str() {
                "offset" => offset = self.expect_num()?,
                "size" => size = self.expect_size()?,
                _ => return self.fail(format!("{attr} is not a register attribute")),
            }
        }
        if size == 0 || size > 1 << 16 {
            return self.fail("a register definition needs a plausible size");
        }
        let names = self.string_list(MAX_REGISTERS)?;
        for (index, name) in names.into_iter().enumerate() {
            let Some(name) = name else { continue };
            let at = offset
                .checked_add((index as u64).checked_mul(size as u64).ok_or_else(|| {
                    Error::new("a register list runs past the end of its address space")
                })?)
                .ok_or_else(|| {
                    Error::new("a register list runs past the end of its address space")
                })?;
            let id = VarnodeId(self.spec.varnodes.len() as u32);
            self.spec.varnodes.push(Varnode {
                name: name.clone(),
                space,
                offset: at,
                size,
            });
            self.spec.symbols.insert(name, Symbol::Varnode(id));
        }
        self.expect_op(";")
    }

    fn token_def(&mut self) -> Result<()> {
        let name = self.expect_ident()?;
        self.expect_op("(")?;
        let bits = self.expect_size()?;
        self.expect_op(")")?;
        if bits == 0 || bits % 8 != 0 || bits > MAX_TOKEN_BITS {
            return self.fail(format!(
                "token {name} is {bits} bits, which is not a whole number of bytes"
            ));
        }
        let mut endian = self.spec.endian;
        if self.eat_ident("endian")? {
            self.expect_op("=")?;
            let value = self.expect_ident()?;
            endian = match value.as_str() {
                "big" => Endian::Big,
                "little" => Endian::Little,
                _ => return self.fail(format!("{value} is not an endianness")),
            };
        }
        let token = TokenId(self.spec.tokens.len() as u32);
        self.spec.tokens.push(TokenDef {
            name: name.clone(),
            size: bits / 8,
            endian,
        });
        self.spec.symbols.insert(name, Symbol::Token(token));

        while !self.eat_op(";")? {
            let field = self.expect_ident()?;
            self.expect_op("=")?;
            self.expect_op("(")?;
            let low = self.expect_size()?;
            self.expect_op(",")?;
            let high = self.expect_size()?;
            self.expect_op(")")?;
            if low > high || high >= bits {
                return self.fail(format!(
                    "field {field} covers bits {low} to {high}, outside a {bits} bit token"
                ));
            }
            let (signed, base, _) = self.field_attributes()?;
            let id = FieldId(self.spec.fields.len() as u32);
            self.spec.fields.push(Field {
                name: field.clone(),
                token,
                low,
                high,
                signed,
                base,
                attach: Attach::None,
            });
            self.spec.symbols.insert(field, Symbol::Field(id));
        }
        Ok(())
    }

    fn context_def(&mut self) -> Result<()> {
        let register_name = self.expect_ident()?;
        let register = match self.spec.lookup(&register_name) {
            Some(Symbol::Varnode(id)) => id,
            _ => {
                return self.fail(format!(
                    "define context wants a register, and {register_name} is not one"
                ));
            }
        };
        self.spec.context_register = Some(register);
        let bits = self.spec.varnode(register).size * 8;
        while !self.eat_op(";")? {
            let field = self.expect_ident()?;
            self.expect_op("=")?;
            self.expect_op("(")?;
            let low = self.expect_size()?;
            self.expect_op(",")?;
            let high = self.expect_size()?;
            self.expect_op(")")?;
            if low > high || high >= bits {
                return self.fail(format!(
                    "context field {field} covers bits {low} to {high}, outside a {bits} bit register"
                ));
            }
            let (signed, base, noflow) = self.field_attributes()?;
            let id = ContextFieldId(self.spec.context_fields.len() as u32);
            self.spec.context_fields.push(ContextField {
                name: field.clone(),
                register,
                low,
                high,
                signed,
                base,
                noflow,
                attach: Attach::None,
            });
            self.spec.symbols.insert(field, Symbol::Context(id));
        }
        Ok(())
    }

    /// `signed`, `hex`, `dec` and `noflow`, in any order and any number.
    fn field_attributes(&mut self) -> Result<(bool, NumberBase, bool)> {
        let mut signed = false;
        let mut base = NumberBase::Hex;
        let mut noflow = false;
        loop {
            let word = match self.peek()? {
                Tok::Ident(w) => w.as_str(),
                _ => return Ok((signed, base, noflow)),
            };
            match word {
                "signed" => signed = true,
                "hex" => base = NumberBase::Hex,
                "dec" => base = NumberBase::Dec,
                "noflow" => noflow = true,
                _ => return Ok((signed, base, noflow)),
            }
            self.next()?;
        }
    }

    fn bitrange_def(&mut self) -> Result<()> {
        while !self.eat_op(";")? {
            let name = self.expect_ident()?;
            self.expect_op("=")?;
            let register_name = self.expect_ident()?;
            let Some(Symbol::Varnode(register)) = self.spec.lookup(&register_name) else {
                return self.fail(format!("{register_name} is not a register"));
            };
            self.expect_op("[")?;
            let low = self.expect_size()?;
            self.expect_op(",")?;
            let bits = self.expect_size()?;
            self.expect_op("]")?;
            if bits == 0 || low.saturating_add(bits) > self.spec.varnode(register).size * 8 {
                return self.fail(format!("bit range {name} does not fit in {register_name}"));
            }
            let id = BitRangeId(self.spec.bitranges.len() as u32);
            self.spec.bitranges.push(BitRange {
                name: name.clone(),
                register,
                low,
                bits,
            });
            self.spec.symbols.insert(name, Symbol::BitRange(id));
        }
        Ok(())
    }

    fn attach(&mut self) -> Result<()> {
        let kind = self.expect_ident()?;
        let fields = self.ident_list(MAX_ATTACH)?;
        let attach = match kind.as_str() {
            "variables" => {
                let names = self.string_list(MAX_ATTACH)?;
                let mut out = Vec::with_capacity(names.len());
                for name in names {
                    match name {
                        None => out.push(None),
                        Some(n) => match self.spec.lookup(&n) {
                            Some(Symbol::Varnode(id)) => out.push(Some(id)),
                            _ => return self.fail(format!("{n} is not a register")),
                        },
                    }
                }
                Attach::Variables(out)
            }
            "names" => Attach::Names(self.string_list(MAX_ATTACH)?),
            "values" => Attach::Values(self.number_list(MAX_ATTACH)?),
            other => return self.fail(format!("attach {other} is not a kind of attachment")),
        };
        self.expect_op(";")?;
        for name in fields {
            match self.spec.lookup(&name) {
                Some(Symbol::Field(id)) => {
                    self.spec.fields[id.index()].attach = attach.clone();
                }
                Some(Symbol::Context(id)) => {
                    self.spec.context_fields[id.index()].attach = attach.clone();
                }
                _ => {
                    return self.fail(format!(
                        "{name} is not a field, so nothing can attach to it"
                    ));
                }
            }
        }
        Ok(())
    }

    /// `[ a b c ]` or a single name.
    fn ident_list(&mut self, limit: usize) -> Result<Vec<String>> {
        if !self.eat_op("[")? {
            return Ok(vec![self.expect_ident()?]);
        }
        let mut out = Vec::new();
        while !self.eat_op("]")? {
            if out.len() >= limit {
                return self.fail(format!("a list of more than {limit} names"));
            }
            if self.at_eof()? {
                return self.fail("a [ list is never closed");
            }
            out.push(self.expect_ident()?);
        }
        Ok(out)
    }

    /// The same, but entries may be quoted and `_` means a gap.
    fn string_list(&mut self, limit: usize) -> Result<Vec<Option<String>>> {
        let one = |t: Tok| match t {
            Tok::Ident(name) if name == "_" => Ok(None),
            Tok::Ident(name) => Ok(Some(name)),
            Tok::Str(text) => Ok(Some(text)),
            Tok::Num(n) => Ok(Some(n.to_string())),
            other => Err(other),
        };
        if !self.eat_op("[")? {
            let t = self.next()?.tok;
            return match one(t) {
                Ok(v) => Ok(vec![v]),
                Err(other) => self.fail(format!("expected a name, found {other}")),
            };
        }
        let mut out = Vec::new();
        while !self.eat_op("]")? {
            if out.len() >= limit {
                return self.fail(format!("a list of more than {limit} entries"));
            }
            if self.at_eof()? {
                return self.fail("a [ list is never closed");
            }
            let t = self.next()?.tok;
            match one(t) {
                Ok(v) => out.push(v),
                Err(other) => return self.fail(format!("expected a name, found {other}")),
            }
        }
        Ok(out)
    }

    fn number_list(&mut self, limit: usize) -> Result<Vec<Option<i64>>> {
        let bracketed = self.eat_op("[")?;
        let mut out = Vec::new();
        loop {
            if bracketed && self.eat_op("]")? {
                break;
            }
            if out.len() >= limit {
                return self.fail(format!("a list of more than {limit} entries"));
            }
            if self.at_eof()? {
                return self.fail("a [ list is never closed");
            }
            let negative = self.eat_op("-")?;
            match self.next()?.tok {
                Tok::Num(n) => {
                    let v = n as i64;
                    out.push(Some(if negative { -v } else { v }));
                }
                Tok::Ident(name) if name == "_" => out.push(None),
                other => return self.fail(format!("expected a number, found {other}")),
            }
            if !bracketed {
                break;
            }
        }
        Ok(out)
    }

    // ---- macros, with blocks, constructors ----

    fn macro_def(&mut self) -> Result<()> {
        let location = self.location();
        let name = self.expect_ident()?;
        let mut scope = Scope::constructor();
        self.expect_op("(")?;
        while !self.eat_op(")")? {
            if self.at_eof()? {
                return self.fail("a macro parameter list is never closed");
            }
            let param = self.expect_ident()?;
            let i = scope.params.len() as u16;
            if scope.params.len() >= MAX_OPERANDS {
                return self.fail("a macro with too many parameters");
            }
            scope.param_index.insert(param.clone(), i);
            scope.params.push(param);
            if !self.eat_op(",")? && !self.at_op(")")? {
                return self.fail("a macro parameter list wants commas between names");
            }
        }
        // Registered before the body so a macro may call itself, which the
        // language does not forbid even though expansion would not terminate.
        let id = MacroId(self.spec.macros.len() as u32);
        self.spec.macros.push(MacroDef {
            name: name.clone(),
            params: scope.params.clone(),
            locals: Vec::new(),
            labels: Vec::new(),
            body: Vec::new(),
            location: location.clone(),
        });
        self.spec.symbols.insert(name, Symbol::Macro(id));
        let body = self.body(&mut scope)?;
        let def = &mut self.spec.macros[id.index()];
        def.body = body;
        def.locals = scope.locals;
        def.labels = scope.labels;
        Ok(())
    }

    fn with_block(&mut self) -> Result<()> {
        if self.withs.len() >= self.limits.condition_depth {
            return self.fail("with blocks nest too deep");
        }
        let table = if self.at_op(":")? {
            None
        } else {
            let name = self.expect_ident()?;
            Some(self.table_named(&name))
        };
        self.expect_op(":")?;
        let mut scope = Scope::global();
        let pattern = if self.at_op("[")? || self.at_op("{")? {
            None
        } else {
            Some(self.pattern(&mut scope)?)
        };
        let disasm = if self.at_op("[")? {
            self.disasm_section(&mut scope)?
        } else {
            Vec::new()
        };
        self.expect_op("{")?;
        self.withs.push(With {
            table,
            pattern,
            disasm,
        });
        Ok(())
    }

    fn table_named(&mut self, name: &str) -> TableId {
        if let Some(Symbol::Table(id)) = self.spec.lookup(name) {
            return id;
        }
        let id = TableId(self.spec.tables.len() as u32);
        self.spec.tables.push(Table {
            name: name.to_string(),
            constructors: Vec::new(),
            min_length: 0,
            max_length: 0,
        });
        self.spec
            .symbols
            .insert(name.to_string(), Symbol::Table(id));
        id
    }

    fn constructor(&mut self, table_name: Option<String>) -> Result<()> {
        let location = self.location();
        let table = match &table_name {
            Some(name) => self.table_named(name),
            None => self
                .withs
                .iter()
                .rev()
                .find_map(|w| w.table)
                .unwrap_or(TableId(0)),
        };
        let root = table == TableId(0);

        // The display section is raw text, so any lookahead has to be undone
        // before the scanner is handed the source.
        let mark = self.mark();
        self.reset(mark);
        let raw = self.lex.display_section().map_err(|e| self.here(e))?;

        let mut scope = Scope::constructor();
        let display = self.display(&raw, root, &mut scope)?;

        let mut expr = self.pattern(&mut scope)?;
        for with in self.withs.iter().rev() {
            if let Some(p) = &with.pattern {
                expr = PatternExpr::And(Box::new(p.clone()), Box::new(expr));
            }
        }

        let mut disasm: Vec<DisasmStmt> =
            self.withs.iter().flat_map(|w| w.disasm.clone()).collect();
        if self.at_op("[")? {
            let own = self.disasm_section(&mut scope)?;
            disasm.extend(own);
        }

        let body = if self.eat_ident("unimpl")? {
            None
        } else {
            Some(self.body(&mut scope)?)
        };

        // The pattern is reduced to masks only once the whole file has been
        // read, because how many bytes a subtable takes is not known until its
        // own constructors are in.
        let id = ConstructorId(self.spec.constructors.len() as u32);
        self.spec.constructors.push(Constructor {
            table,
            display,
            operands: scope.operands,
            order: Vec::new(),
            locals: scope.locals,
            labels: scope.labels,
            pattern: expr,
            resolved: ResolvedPattern::default(),
            disasm,
            body,
            location,
        });
        self.spec.tables[table.index()].constructors.push(id);
        Ok(())
    }

    // ---- display ----

    fn display(&mut self, raw: &str, root: bool, scope: &mut Scope) -> Result<Display> {
        let pieces = display_pieces(raw);
        let mut i = 0;
        let mut mnemonic = None;
        // Leading white space is not part of the display.
        while matches!(pieces.get(i), Some(Piece::Space)) {
            i += 1;
        }
        if root {
            if matches!(pieces.get(i), Some(Piece::Caret)) {
                // A leading `^` says the first name is an operand, not a
                // mnemonic.
                i += 1;
            } else {
                let mut text = String::new();
                while let Some(p) = pieces.get(i) {
                    match p {
                        Piece::Space | Piece::Caret => break,
                        Piece::Lit(s) | Piece::Id(s) => text.push_str(s),
                    }
                    i += 1;
                }
                if !text.is_empty() {
                    mnemonic = Some(text);
                }
            }
        }

        let mut end = pieces.len();
        while end > i && matches!(pieces.get(end - 1), Some(Piece::Space)) {
            end -= 1;
        }

        let mut out: Vec<DisplayPiece> = Vec::new();
        let mut literal = String::new();
        for piece in &pieces[i..end] {
            match piece {
                Piece::Caret => {}
                Piece::Space => literal.push(' '),
                Piece::Lit(s) => literal.push_str(s),
                Piece::Id(name) => {
                    if !literal.is_empty() {
                        out.push(DisplayPiece::Literal(std::mem::take(&mut literal)));
                    }
                    let index = scope
                        .operand(name, OperandSource::Unbound, false)
                        .map_err(|e| self.here(e))?;
                    out.push(DisplayPiece::Operand(index));
                }
            }
        }
        if !literal.is_empty() {
            out.push(DisplayPiece::Literal(literal));
        }
        Ok(Display {
            mnemonic,
            pieces: out,
        })
    }

    // ---- bit patterns ----

    fn pattern(&mut self, scope: &mut Scope) -> Result<PatternExpr> {
        self.enter()?;
        let mut left = self.pattern_or(scope)?;
        let mut chain = 0usize;
        while self.eat_op(";")? {
            let right = self.pattern_or(scope)?;
            self.link(&mut chain)?;
            left = PatternExpr::Cat(Box::new(left), Box::new(right));
        }
        self.leave();
        Ok(left)
    }

    fn pattern_or(&mut self, scope: &mut Scope) -> Result<PatternExpr> {
        self.enter()?;
        let mut left = self.pattern_and(scope)?;
        let mut chain = 0usize;
        while self.eat_op("|")? {
            let right = self.pattern_and(scope)?;
            self.link(&mut chain)?;
            left = PatternExpr::Or(Box::new(left), Box::new(right));
        }
        self.leave();
        Ok(left)
    }

    fn pattern_and(&mut self, scope: &mut Scope) -> Result<PatternExpr> {
        self.enter()?;
        let mut left = self.pattern_ellipsis(scope)?;
        let mut chain = 0usize;
        while self.eat_op("&")? {
            let right = self.pattern_ellipsis(scope)?;
            self.link(&mut chain)?;
            left = PatternExpr::And(Box::new(left), Box::new(right));
        }
        self.leave();
        Ok(left)
    }

    fn pattern_ellipsis(&mut self, scope: &mut Scope) -> Result<PatternExpr> {
        let mut leading = 0usize;
        while self.eat_op("...")? {
            leading += 1;
            if leading > self.limits.expr_depth {
                return self.fail("a run of ... with nothing to apply to");
            }
        }
        let mut expr = self.pattern_atom(scope)?;
        for _ in 0..leading {
            expr = PatternExpr::EllipsisLeft(Box::new(expr));
        }
        let mut trailing = 0usize;
        while self.eat_op("...")? {
            trailing += 1;
            if trailing > self.limits.expr_depth {
                return self.fail("a run of ... with nothing to apply to");
            }
            expr = PatternExpr::EllipsisRight(Box::new(expr));
        }
        Ok(expr)
    }

    fn pattern_atom(&mut self, scope: &mut Scope) -> Result<PatternExpr> {
        self.enter()?;
        let value = self.pattern_atom_inner(scope);
        self.leave();
        value
    }

    fn pattern_atom_inner(&mut self, scope: &mut Scope) -> Result<PatternExpr> {
        if self.eat_op("(")? {
            let inner = self.pattern(scope)?;
            self.expect_op(")")?;
            return Ok(inner);
        }
        let name = match self.next()?.tok {
            Tok::Ident(name) => name,
            other => return self.fail(format!("{other} cannot appear in a bit pattern")),
        };
        let op = match self.peek()? {
            Tok::Op("=") => Some(ConstraintOp::Equal),
            Tok::Op("!=") => Some(ConstraintOp::NotEqual),
            Tok::Op("<") => Some(ConstraintOp::Less),
            Tok::Op("<=") => Some(ConstraintOp::LessEqual),
            Tok::Op(">") => Some(ConstraintOp::Greater),
            Tok::Op(">=") => Some(ConstraintOp::GreaterEqual),
            _ => None,
        };
        let Some(op) = op else {
            // A bare name uses the bits without restricting them, and that is
            // what defines an operand.
            if name == "epsilon" {
                return Ok(PatternExpr::Epsilon);
            }
            let sym = self.pattern_operand(&name, scope, true)?;
            return Ok(PatternExpr::Symbol(sym));
        };
        self.next()?;
        let lhs = self.pattern_operand(&name, scope, false)?;
        let rhs = self.disasm_expr(scope, true)?;
        Ok(PatternExpr::Constraint { lhs, op, rhs })
    }

    /// Resolve a name inside a bit pattern. `defines` is set for a bare name,
    /// which is what creates an operand; the left hand side of a constraint
    /// only binds an operand that the display section already named.
    fn pattern_operand(
        &mut self,
        name: &str,
        scope: &mut Scope,
        defines: bool,
    ) -> Result<SymbolRef> {
        let known = scope.operand_index.get(name).copied();
        let global = self.spec.lookup(name);
        let source = match global {
            Some(Symbol::Field(id)) => OperandSource::Field(id),
            Some(Symbol::Context(id)) => OperandSource::Context(id),
            Some(Symbol::Table(id)) => OperandSource::Table(id),
            Some(Symbol::Varnode(id)) => OperandSource::Varnode(id),
            Some(Symbol::BitRange(id)) => OperandSource::BitRange(id),
            Some(Symbol::Builtin(_)) => OperandSource::Computed,
            Some(_) => {
                return self.fail(format!("{name} cannot be used in a bit pattern"));
            }
            // The one forward reference the language allows: an unknown name
            // here is a table defined further down the file.
            None => OperandSource::Table(self.table_named(name)),
        };
        if let OperandSource::Table(id) = source {
            let at = self.location();
            self.pattern_tables.entry(id.0).or_insert(at);
        }
        if let Some(i) = known {
            let slot = &mut scope.operands[i as usize];
            if slot.source == OperandSource::Unbound {
                slot.source = source;
            }
            return Ok(SymbolRef::Operand(i));
        }
        if !defines || !scope.allow_operands {
            return Ok(match global {
                Some(Symbol::Field(id)) => SymbolRef::Field(id),
                Some(Symbol::Context(id)) => SymbolRef::Context(id),
                Some(Symbol::Table(id)) => SymbolRef::Table(id),
                Some(Symbol::Varnode(id)) => SymbolRef::Varnode(id),
                Some(Symbol::BitRange(id)) => SymbolRef::BitRange(id),
                Some(Symbol::Builtin(b)) => SymbolRef::Builtin(b),
                _ => match source {
                    OperandSource::Table(id) => SymbolRef::Table(id),
                    _ => SymbolRef::Builtin(Builtin::Epsilon),
                },
            });
        }
        let i = scope
            .operand(name, source, true)
            .map_err(|e| self.here(e))?;
        Ok(SymbolRef::Operand(i))
    }

    // ---- disassembly actions ----

    fn disasm_section(&mut self, scope: &mut Scope) -> Result<Vec<DisasmStmt>> {
        self.expect_op("[")?;
        let mut out = Vec::new();
        while !self.eat_op("]")? {
            if self.at_eof()? {
                return self.fail("a disassembly action section is never closed");
            }
            if self.eat_op(";")? {
                continue;
            }
            if self.eat_ident("globalset")? {
                self.expect_op("(")?;
                let address = self.disasm_expr(scope, false)?;
                self.expect_op(",")?;
                let name = self.expect_ident()?;
                let Some(Symbol::Context(context)) = self.spec.lookup(&name) else {
                    return self.fail(format!(
                        "globalset wants a context field, and {name} is not one"
                    ));
                };
                self.expect_op(")")?;
                out.push(DisasmStmt::GlobalSet { address, context });
                continue;
            }
            let name = self.expect_ident()?;
            let target = match self.spec.lookup(&name) {
                Some(Symbol::Context(id)) if !scope.operand_index.contains_key(&name) => {
                    DisasmTarget::Context(id)
                }
                _ => {
                    let i = scope
                        .operand(&name, OperandSource::Computed, false)
                        .map_err(|e| self.here(e))?;
                    if scope.operands[i as usize].source == OperandSource::Unbound {
                        scope.operands[i as usize].source = OperandSource::Computed;
                    }
                    DisasmTarget::Operand(i)
                }
            };
            self.expect_op("=")?;
            let value = self.disasm_expr(scope, false)?;
            out.push(DisasmStmt::Assign { target, value });
        }
        Ok(out)
    }

    /// The expression language of disassembly actions and constraint right
    /// hand sides. Inside a bit pattern `&`, `|` and `;` belong to the pattern
    /// itself, so `in_pattern` leaves them for the caller.
    fn disasm_expr(&mut self, scope: &mut Scope, in_pattern: bool) -> Result<DisasmExpr> {
        self.enter()?;
        let value = self.disasm_or(scope, in_pattern);
        self.leave();
        value
    }

    fn disasm_or(&mut self, scope: &mut Scope, in_pattern: bool) -> Result<DisasmExpr> {
        let mut left = self.disasm_xor(scope, in_pattern)?;
        let mut chain = 0usize;
        loop {
            // `$or` everywhere, `|` only outside a bit pattern, where it
            // would otherwise be the pattern's own disjunction.
            if !self.eat_op("$or")? && !(!in_pattern && self.eat_op("|")?) {
                return Ok(left);
            }
            let op = DisasmBinOp::Or;
            let right = self.disasm_xor(scope, in_pattern)?;
            self.link(&mut chain)?;
            left = DisasmExpr::Binary(op, Box::new(left), Box::new(right));
        }
    }

    fn disasm_xor(&mut self, scope: &mut Scope, in_pattern: bool) -> Result<DisasmExpr> {
        let mut left = self.disasm_and(scope, in_pattern)?;
        let mut chain = 0usize;
        while self.eat_op("$xor")? || self.eat_op("^")? {
            let right = self.disasm_and(scope, in_pattern)?;
            self.link(&mut chain)?;
            left = DisasmExpr::Binary(DisasmBinOp::Xor, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn disasm_and(&mut self, scope: &mut Scope, in_pattern: bool) -> Result<DisasmExpr> {
        let mut left = self.disasm_shift(scope, in_pattern)?;
        let mut chain = 0usize;
        loop {
            if !self.eat_op("$and")? && !(!in_pattern && self.eat_op("&")?) {
                return Ok(left);
            }
            let op = DisasmBinOp::And;
            let right = self.disasm_shift(scope, in_pattern)?;
            self.link(&mut chain)?;
            left = DisasmExpr::Binary(op, Box::new(left), Box::new(right));
        }
    }

    fn disasm_shift(&mut self, scope: &mut Scope, in_pattern: bool) -> Result<DisasmExpr> {
        let mut left = self.disasm_add(scope, in_pattern)?;
        let mut chain = 0usize;
        loop {
            let op = if self.eat_op("<<")? {
                DisasmBinOp::Shl
            } else if self.eat_op(">>")? {
                DisasmBinOp::Shr
            } else {
                return Ok(left);
            };
            let right = self.disasm_add(scope, in_pattern)?;
            self.link(&mut chain)?;
            left = DisasmExpr::Binary(op, Box::new(left), Box::new(right));
        }
    }

    fn disasm_add(&mut self, scope: &mut Scope, in_pattern: bool) -> Result<DisasmExpr> {
        let mut left = self.disasm_mul(scope, in_pattern)?;
        let mut chain = 0usize;
        loop {
            let op = if self.eat_op("+")? {
                DisasmBinOp::Add
            } else if self.eat_op("-")? {
                DisasmBinOp::Sub
            } else {
                return Ok(left);
            };
            let right = self.disasm_mul(scope, in_pattern)?;
            self.link(&mut chain)?;
            left = DisasmExpr::Binary(op, Box::new(left), Box::new(right));
        }
    }

    fn disasm_mul(&mut self, scope: &mut Scope, in_pattern: bool) -> Result<DisasmExpr> {
        let mut left = self.disasm_unary(scope, in_pattern)?;
        let mut chain = 0usize;
        loop {
            let op = if self.eat_op("*")? {
                DisasmBinOp::Mul
            } else if self.eat_op("/")? {
                DisasmBinOp::Div
            } else {
                return Ok(left);
            };
            let right = self.disasm_unary(scope, in_pattern)?;
            self.link(&mut chain)?;
            left = DisasmExpr::Binary(op, Box::new(left), Box::new(right));
        }
    }

    fn disasm_unary(&mut self, scope: &mut Scope, in_pattern: bool) -> Result<DisasmExpr> {
        self.enter()?;
        let value = (|| {
            if self.eat_op("-")? {
                let inner = self.disasm_unary(scope, in_pattern)?;
                return Ok(DisasmExpr::Unary(DisasmUnOp::Negate, Box::new(inner)));
            }
            if self.eat_op("~")? {
                let inner = self.disasm_unary(scope, in_pattern)?;
                return Ok(DisasmExpr::Unary(DisasmUnOp::Not, Box::new(inner)));
            }
            if self.eat_op("(")? {
                let inner = self.disasm_expr(scope, in_pattern)?;
                self.expect_op(")")?;
                return Ok(inner);
            }
            match self.next()?.tok {
                Tok::Num(n) => Ok(DisasmExpr::Num(n as i64)),
                Tok::Ident(name) => {
                    let sym = self.disasm_symbol(&name, scope)?;
                    Ok(DisasmExpr::Symbol(sym))
                }
                other => self.fail(format!("{other} cannot appear in a disassembly expression")),
            }
        })();
        self.leave();
        value
    }

    fn disasm_symbol(&mut self, name: &str, scope: &mut Scope) -> Result<SymbolRef> {
        if let Some(&i) = scope.operand_index.get(name) {
            return Ok(SymbolRef::Operand(i));
        }
        match self.spec.lookup(name) {
            Some(Symbol::Field(id)) => Ok(SymbolRef::Field(id)),
            Some(Symbol::Context(id)) => Ok(SymbolRef::Context(id)),
            Some(Symbol::Varnode(id)) => Ok(SymbolRef::Varnode(id)),
            Some(Symbol::BitRange(id)) => Ok(SymbolRef::BitRange(id)),
            Some(Symbol::Builtin(b)) => Ok(SymbolRef::Builtin(b)),
            Some(Symbol::Table(id)) => Ok(SymbolRef::Table(id)),
            _ => self.fail(format!("{name} has no integer meaning at disassembly time")),
        }
    }

    // ---- semantics ----

    fn body(&mut self, scope: &mut Scope) -> Result<Vec<Stmt>> {
        self.expect_op("{")?;
        let mut out = Vec::new();
        loop {
            if self.eat_op("}")? {
                return Ok(out);
            }
            if self.at_eof()? {
                return self.fail("a semantic body is never closed");
            }
            if let Some(stmt) = self.statement(scope)? {
                out.push(stmt);
            }
        }
    }

    fn statement(&mut self, scope: &mut Scope) -> Result<Option<Stmt>> {
        if self.eat_op(";")? {
            return Ok(None);
        }
        if self.eat_op("<<")? {
            let name = self.expect_ident()?;
            self.expect_op(">>")?;
            let table = self.table_named(&name);
            return Ok(Some(Stmt::CrossBuildSection(table)));
        }
        if self.eat_op("<")? {
            let name = self.expect_ident()?;
            self.expect_op(">")?;
            let i = scope.label(&name).map_err(|e| self.here(e))?;
            return Ok(Some(Stmt::Label(i)));
        }
        if self.at_op("*")? {
            let (space, size) = self.deref_modifiers()?;
            let addr = self.expr(scope)?;
            self.expect_op("=")?;
            let value = self.expr(scope)?;
            self.expect_op(";")?;
            return Ok(Some(Stmt::Assign {
                local: false,
                dest: Lvalue::Store {
                    space,
                    size,
                    addr: Box::new(addr),
                },
                value,
            }));
        }

        let word = match self.peek()? {
            Tok::Ident(name) => name.clone(),
            other => {
                let other = other.to_string();
                return self.fail(format!("{other} cannot start a semantic statement"));
            }
        };

        match word.as_str() {
            "local" => {
                self.next()?;
                return self.local_statement(scope).map(Some);
            }
            "build" => {
                self.next()?;
                let name = self.expect_ident()?;
                self.expect_op(";")?;
                let Some(&i) = scope.operand_index.get(&name) else {
                    return self.fail(format!("build wants an operand, and {name} is not one"));
                };
                return Ok(Some(Stmt::Build(i)));
            }
            "crossbuild" => {
                self.next()?;
                let addr = self.expr(scope)?;
                self.expect_op(",")?;
                let name = self.expect_ident()?;
                self.expect_op(";")?;
                let table = self.table_named(&name);
                return Ok(Some(Stmt::CrossBuild { addr, table }));
            }
            "delayslot" => {
                self.next()?;
                self.expect_op("(")?;
                let n = self.expect_num()?;
                self.expect_op(")")?;
                self.expect_op(";")?;
                return Ok(Some(Stmt::DelaySlot(n)));
            }
            "export" => {
                self.next()?;
                let export = if self.at_op("*")? {
                    let (space, size) = self.deref_modifiers()?;
                    let addr = self.expr(scope)?;
                    Export::Deref { space, size, addr }
                } else {
                    Export::Value(self.expr(scope)?)
                };
                self.expect_op(";")?;
                return Ok(Some(Stmt::Export(export)));
            }
            "goto" | "call" => {
                self.next()?;
                let target = self.jump_target(scope)?;
                self.expect_op(";")?;
                return Ok(Some(if word == "goto" {
                    Stmt::Goto(target)
                } else {
                    Stmt::Call(target)
                }));
            }
            "return" => {
                self.next()?;
                let had_brackets = self.eat_op("[")?;
                let value = self.expr(scope)?;
                if had_brackets {
                    self.expect_op("]")?;
                }
                self.expect_op(";")?;
                return Ok(Some(Stmt::Return(value)));
            }
            "if" => {
                self.next()?;
                let cond = self.expr(scope)?;
                if !self.eat_ident("goto")? {
                    return self.fail("an if in a semantic body must be followed by goto");
                }
                let target = self.jump_target(scope)?;
                self.expect_op(";")?;
                return Ok(Some(Stmt::CondGoto { cond, target }));
            }
            _ => {}
        }

        self.next()?;
        // A name followed by `(` is a call unless it is a varnode having bytes
        // shaved off it, which cannot start a statement.
        if self.at_op("(")? {
            if let Some(sym) = self.spec.lookup(&word) {
                match sym {
                    Symbol::Macro(mac) => {
                        let args = self.arguments(scope)?;
                        self.expect_op(";")?;
                        return Ok(Some(Stmt::MacroCall { mac, args }));
                    }
                    Symbol::PcodeOp(op) => {
                        let args = self.arguments(scope)?;
                        self.expect_op(";")?;
                        return Ok(Some(Stmt::UserOp { op, args }));
                    }
                    _ => {}
                }
            }
            return self.fail(format!(
                "{word} is called here but is not a macro or a pcodeop"
            ));
        }

        let dest = self.lvalue(&word, scope)?;
        self.expect_op("=")?;
        let value = self.expr(scope)?;
        self.expect_op(";")?;
        Ok(Some(Stmt::Assign {
            local: false,
            dest,
            value,
        }))
    }

    fn local_statement(&mut self, scope: &mut Scope) -> Result<Stmt> {
        let name = self.expect_ident()?;
        let size = if self.eat_op(":")? {
            Some(self.expect_size()?)
        } else {
            None
        };
        let i = scope.local(&name, size).map_err(|e| self.here(e))?;
        if self.eat_op(";")? {
            return Ok(Stmt::Declare(i));
        }
        self.expect_op("=")?;
        let value = self.expr(scope)?;
        self.expect_op(";")?;
        Ok(Stmt::Assign {
            local: true,
            dest: Lvalue::Symbol {
                symbol: SymbolRef::Local(i),
                size,
            },
            value,
        })
    }

    fn lvalue(&mut self, name: &str, scope: &mut Scope) -> Result<Lvalue> {
        if self.eat_op(":")? {
            let size = self.expect_size()?;
            let symbol = self.semantic_symbol(name, scope, true)?;
            if let SymbolRef::Local(i) = symbol {
                scope.locals[i as usize].size = Some(size);
            }
            return Ok(Lvalue::Symbol {
                symbol,
                size: Some(size),
            });
        }
        // `r1[3,1] = ...` fills a bit range. Anything else after the name is
        // not an lvalue.
        let mark = self.mark();
        if self.eat_op("[")? {
            if matches!(self.peek()?, Tok::Num(_)) {
                let lsb = self.expect_size()?;
                self.expect_op(",")?;
                let bits = self.expect_size()?;
                self.expect_op("]")?;
                let symbol = self.semantic_symbol(name, scope, false)?;
                return Ok(Lvalue::BitRange { symbol, lsb, bits });
            }
            self.reset(mark);
        }
        let symbol = self.semantic_symbol(name, scope, true)?;
        Ok(Lvalue::Symbol { symbol, size: None })
    }

    fn jump_target(&mut self, scope: &mut Scope) -> Result<JumpTarget> {
        if self.eat_op("[")? {
            let inner = self.expr(scope)?;
            self.expect_op("]")?;
            return Ok(JumpTarget::Indirect(inner));
        }
        if self.eat_op("<")? {
            let name = self.expect_ident()?;
            self.expect_op(">")?;
            let i = scope.label(&name).map_err(|e| self.here(e))?;
            return Ok(JumpTarget::Label(i));
        }
        let addr = self.expr(scope)?;
        let mut space = None;
        let mark = self.mark();
        if self.eat_op("[")? {
            match self.next()?.tok {
                Tok::Ident(name) => match self.spec.lookup(&name) {
                    Some(Symbol::Space(id)) => {
                        space = Some(id);
                        self.expect_op("]")?;
                    }
                    _ => {
                        self.reset(mark);
                    }
                },
                _ => self.reset(mark),
            }
        }
        Ok(JumpTarget::Direct { addr, space })
    }

    /// The `[space]` and `:size` that may follow a `*`.
    fn deref_modifiers(&mut self) -> Result<(Option<SpaceId>, SizeHint)> {
        self.expect_op("*")?;
        let mut space = None;
        if self.eat_op("[")? {
            let name = self.expect_ident()?;
            let Some(Symbol::Space(id)) = self.spec.lookup(&name) else {
                return self.fail(format!("{name} is not an address space"));
            };
            space = Some(id);
            self.expect_op("]")?;
        }
        let mut size = None;
        if self.eat_op(":")? {
            size = Some(self.expect_size()?);
        }
        Ok((space, size))
    }

    fn arguments(&mut self, scope: &mut Scope) -> Result<Vec<Expr>> {
        self.expect_op("(")?;
        let mut out = Vec::new();
        while !self.eat_op(")")? {
            if self.at_eof()? {
                return self.fail("an argument list is never closed");
            }
            if out.len() > MAX_OPERANDS {
                return self.fail("an argument list with too many arguments");
            }
            out.push(self.expr(scope)?);
            if !self.eat_op(",")? && !self.at_op(")")? {
                return self.fail("an argument list wants commas between arguments");
            }
        }
        Ok(out)
    }

    fn semantic_symbol(
        &mut self,
        name: &str,
        scope: &mut Scope,
        define: bool,
    ) -> Result<SymbolRef> {
        if let Some(&i) = scope.param_index.get(name) {
            return Ok(SymbolRef::Param(i));
        }
        if let Some(&i) = scope.operand_index.get(name) {
            return Ok(SymbolRef::Operand(i));
        }
        if let Some(&i) = scope.local_index.get(name) {
            return Ok(SymbolRef::Local(i));
        }
        match self.spec.lookup(name) {
            Some(Symbol::Varnode(id)) => return Ok(SymbolRef::Varnode(id)),
            Some(Symbol::Field(id)) => return Ok(SymbolRef::Field(id)),
            Some(Symbol::Context(id)) => return Ok(SymbolRef::Context(id)),
            Some(Symbol::BitRange(id)) => return Ok(SymbolRef::BitRange(id)),
            Some(Symbol::Table(id)) => return Ok(SymbolRef::Table(id)),
            Some(Symbol::Space(id)) => return Ok(SymbolRef::Space(id)),
            Some(Symbol::Builtin(b)) => return Ok(SymbolRef::Builtin(b)),
            _ => {}
        }
        if !define {
            return self.fail(format!("{name} is not anything this constructor can see"));
        }
        // The language creates a temporary for any new name on the left of an
        // assignment, with or without the `local` keyword.
        let i = scope.local(name, None).map_err(|e| self.here(e))?;
        Ok(SymbolRef::Local(i))
    }

    // ---- semantic expressions ----

    fn expr(&mut self, scope: &mut Scope) -> Result<Expr> {
        self.enter()?;
        let value = self.bool_or(scope);
        self.leave();
        value
    }

    fn bool_or(&mut self, scope: &mut Scope) -> Result<Expr> {
        let mut left = self.bool_and(scope)?;
        let mut chain = 0usize;
        while self.eat_op("||")? {
            let right = self.bool_and(scope)?;
            self.link(&mut chain)?;
            left = Expr::Binary(BinOp::BoolOr, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn bool_and(&mut self, scope: &mut Scope) -> Result<Expr> {
        let mut left = self.bool_xor(scope)?;
        let mut chain = 0usize;
        while self.eat_op("&&")? {
            let right = self.bool_xor(scope)?;
            self.link(&mut chain)?;
            left = Expr::Binary(BinOp::BoolAnd, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn bool_xor(&mut self, scope: &mut Scope) -> Result<Expr> {
        let mut left = self.int_or(scope)?;
        let mut chain = 0usize;
        while self.eat_op("^^")? {
            let right = self.int_or(scope)?;
            self.link(&mut chain)?;
            left = Expr::Binary(BinOp::BoolXor, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn int_or(&mut self, scope: &mut Scope) -> Result<Expr> {
        let mut left = self.int_xor(scope)?;
        let mut chain = 0usize;
        while self.eat_op("|")? {
            let right = self.int_xor(scope)?;
            self.link(&mut chain)?;
            left = Expr::Binary(BinOp::Or, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn int_xor(&mut self, scope: &mut Scope) -> Result<Expr> {
        let mut left = self.int_and(scope)?;
        let mut chain = 0usize;
        while self.eat_op("^")? {
            let right = self.int_and(scope)?;
            self.link(&mut chain)?;
            left = Expr::Binary(BinOp::Xor, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn int_and(&mut self, scope: &mut Scope) -> Result<Expr> {
        let mut left = self.equality(scope)?;
        let mut chain = 0usize;
        while self.eat_op("&")? {
            let right = self.equality(scope)?;
            self.link(&mut chain)?;
            left = Expr::Binary(BinOp::And, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn equality(&mut self, scope: &mut Scope) -> Result<Expr> {
        let mut left = self.relational(scope)?;
        let mut chain = 0usize;
        loop {
            let op = if self.eat_op("==")? {
                BinOp::Equal
            } else if self.eat_op("!=")? {
                BinOp::NotEqual
            } else if self.eat_op("f==")? {
                BinOp::FloatEqual
            } else if self.eat_op("f!=")? {
                BinOp::FloatNotEqual
            } else {
                return Ok(left);
            };
            let right = self.relational(scope)?;
            self.link(&mut chain)?;
            left = Expr::Binary(op, Box::new(left), Box::new(right));
        }
    }

    fn relational(&mut self, scope: &mut Scope) -> Result<Expr> {
        let mut left = self.shift(scope)?;
        let mut chain = 0usize;
        loop {
            // `a > b` is the same operation as `b < a`, so the model keeps one
            // spelling and swaps the operands.
            let (op, swap) = if self.eat_op("<")? {
                (BinOp::Less, false)
            } else if self.eat_op("<=")? {
                (BinOp::LessEqual, false)
            } else if self.eat_op(">")? {
                (BinOp::Less, true)
            } else if self.eat_op(">=")? {
                (BinOp::LessEqual, true)
            } else if self.eat_op("s<")? {
                (BinOp::SLess, false)
            } else if self.eat_op("s<=")? {
                (BinOp::SLessEqual, false)
            } else if self.eat_op("s>")? {
                (BinOp::SLess, true)
            } else if self.eat_op("s>=")? {
                (BinOp::SLessEqual, true)
            } else if self.eat_op("f<")? {
                (BinOp::FloatLess, false)
            } else if self.eat_op("f<=")? {
                (BinOp::FloatLessEqual, false)
            } else if self.eat_op("f>")? {
                (BinOp::FloatLess, true)
            } else if self.eat_op("f>=")? {
                (BinOp::FloatLessEqual, true)
            } else {
                return Ok(left);
            };
            let right = self.shift(scope)?;
            self.link(&mut chain)?;
            left = if swap {
                Expr::Binary(op, Box::new(right), Box::new(left))
            } else {
                Expr::Binary(op, Box::new(left), Box::new(right))
            };
        }
    }

    fn shift(&mut self, scope: &mut Scope) -> Result<Expr> {
        let mut left = self.additive(scope)?;
        let mut chain = 0usize;
        loop {
            let op = if self.eat_op("<<")? {
                BinOp::Left
            } else if self.eat_op(">>")? {
                BinOp::Right
            } else if self.eat_op("s>>")? {
                BinOp::SRight
            } else {
                return Ok(left);
            };
            let right = self.additive(scope)?;
            self.link(&mut chain)?;
            left = Expr::Binary(op, Box::new(left), Box::new(right));
        }
    }

    fn additive(&mut self, scope: &mut Scope) -> Result<Expr> {
        let mut left = self.multiplicative(scope)?;
        let mut chain = 0usize;
        loop {
            let op = if self.eat_op("+")? {
                BinOp::Add
            } else if self.eat_op("-")? {
                BinOp::Sub
            } else if self.eat_op("f+")? {
                BinOp::FloatAdd
            } else if self.eat_op("f-")? {
                BinOp::FloatSub
            } else {
                return Ok(left);
            };
            let right = self.multiplicative(scope)?;
            self.link(&mut chain)?;
            left = Expr::Binary(op, Box::new(left), Box::new(right));
        }
    }

    fn multiplicative(&mut self, scope: &mut Scope) -> Result<Expr> {
        let mut left = self.unary(scope)?;
        let mut chain = 0usize;
        loop {
            let op = if self.eat_op("*")? {
                BinOp::Mult
            } else if self.eat_op("/")? {
                BinOp::Div
            } else if self.eat_op("s/")? {
                BinOp::SDiv
            } else if self.eat_op("%")? {
                BinOp::Rem
            } else if self.eat_op("s%")? {
                BinOp::SRem
            } else if self.eat_op("f*")? {
                BinOp::FloatMult
            } else if self.eat_op("f/")? {
                BinOp::FloatDiv
            } else {
                return Ok(left);
            };
            let right = self.unary(scope)?;
            self.link(&mut chain)?;
            left = Expr::Binary(op, Box::new(left), Box::new(right));
        }
    }

    fn unary(&mut self, scope: &mut Scope) -> Result<Expr> {
        self.enter()?;
        let value = self.unary_inner(scope);
        self.leave();
        value
    }

    fn unary_inner(&mut self, scope: &mut Scope) -> Result<Expr> {
        if self.at_op("*")? {
            let (space, size) = self.deref_modifiers()?;
            let addr = self.unary(scope)?;
            return Ok(Expr::Load {
                space,
                size,
                addr: Box::new(addr),
            });
        }
        if self.eat_op("&")? {
            let size = if self.eat_op(":")? {
                Some(self.expect_size()?)
            } else {
                None
            };
            let inner = self.unary(scope)?;
            return Ok(Expr::AddressOf {
                value: Box::new(inner),
                size,
            });
        }
        for (op, kind) in [
            ("!", UnOp::BoolNegate),
            ("~", UnOp::Negate),
            ("-", UnOp::TwosComp),
            ("f-", UnOp::FloatNeg),
        ] {
            if self.eat_op(op)? {
                let inner = self.unary(scope)?;
                return Ok(Expr::Unary(kind, Box::new(inner)));
            }
        }
        let primary = self.primary(scope)?;
        self.postfix(primary, scope)
    }

    fn postfix(&mut self, mut value: Expr, scope: &mut Scope) -> Result<Expr> {
        let mut steps = 0usize;
        loop {
            steps += 1;
            if steps > self.limits.expr_depth {
                return self.fail("too many modifiers on one value");
            }
            if self.eat_op(":")? {
                let bytes = self.expect_size()?;
                value = match value {
                    // A size on a literal states the constant's width rather
                    // than truncating it.
                    Expr::Num { value: n, .. } => Expr::Num {
                        value: n,
                        size: Some(bytes),
                    },
                    other => Expr::Truncate {
                        value: Box::new(other),
                        bytes,
                    },
                };
                continue;
            }
            let mark = self.mark();
            if self.eat_op("(")? {
                if let Tok::Num(n) = self.peek()?.clone() {
                    self.next()?;
                    if self.eat_op(")")? {
                        let bytes = u32::try_from(n)
                            .map_err(|_| Error::new(format!("{n} is not a plausible size")))?;
                        value = Expr::Shave {
                            value: Box::new(value),
                            bytes,
                        };
                        continue;
                    }
                }
                self.reset(mark);
                return Ok(value);
            }
            if self.eat_op("[")? {
                if matches!(self.peek()?, Tok::Num(_)) {
                    let lsb = self.expect_size()?;
                    self.expect_op(",")?;
                    let bits = self.expect_size()?;
                    self.expect_op("]")?;
                    value = Expr::BitRange {
                        value: Box::new(value),
                        lsb,
                        bits,
                    };
                    continue;
                }
                self.reset(mark);
                return Ok(value);
            }
            let _ = scope;
            return Ok(value);
        }
    }

    fn primary(&mut self, scope: &mut Scope) -> Result<Expr> {
        if self.eat_op("(")? {
            let inner = self.expr(scope)?;
            self.expect_op(")")?;
            return Ok(inner);
        }
        match self.next()?.tok {
            Tok::Num(value) => Ok(Expr::Num { value, size: None }),
            Tok::Ident(name) => {
                if self.at_op("(")? {
                    if let Some(op) = Intrinsic::from_name(&name) {
                        let args = self.arguments(scope)?;
                        return Ok(Expr::Intrinsic { op, args });
                    }
                    if let Some(Symbol::PcodeOp(op)) = self.spec.lookup(&name) {
                        let args = self.arguments(scope)?;
                        return Ok(Expr::UserOp { op, args });
                    }
                }
                let sym = self.semantic_symbol(&name, scope, false)?;
                Ok(Expr::Symbol(sym))
            }
            other => self.fail(format!("{other} cannot appear in an expression")),
        }
    }
}

/// One raw element of a display section.
enum Piece {
    Lit(String),
    Id(String),
    Space,
    Caret,
}

/// Split display text into literals, identifiers, white space and `^`.
///
/// Quotes make their contents literal, which is the only way to print a word
/// that would otherwise name an operand.
fn display_pieces(raw: &str) -> Vec<Piece> {
    let bytes = raw.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i];
        if c.is_ascii_whitespace() {
            while i < bytes.len() && bytes[i].is_ascii_whitespace() {
                i += 1;
            }
            out.push(Piece::Space);
            continue;
        }
        if c == b'"' {
            i += 1;
            let start = i;
            while i < bytes.len() && bytes[i] != b'"' {
                i += 1;
            }
            out.push(Piece::Lit(raw[start..i].to_string()));
            if i < bytes.len() {
                i += 1;
            }
            continue;
        }
        if c == b'^' {
            out.push(Piece::Caret);
            i += 1;
            continue;
        }
        if c.is_ascii_alphabetic() || c == b'_' {
            let start = i;
            while i < bytes.len()
                && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_' || bytes[i] == b'.')
            {
                i += 1;
            }
            out.push(Piece::Id(raw[start..i].to_string()));
            continue;
        }
        let start = i;
        // Every other run is literal text. The loop always takes at least the
        // character it started on, so it cannot stall.
        i += 1;
        while i < bytes.len() {
            let b = bytes[i];
            if b.is_ascii_whitespace()
                || b == b'"'
                || b == b'^'
                || b.is_ascii_alphabetic()
                || b == b'_'
            {
                break;
            }
            i += 1;
        }
        // A run ending in `.` is an instruction suffix such as `].B`, not
        // punctuation followed by an operand, so it swallows the word after
        // it rather than naming one.
        if bytes[i - 1] == b'.' {
            while i < bytes.len()
                && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_' || bytes[i] == b'.')
            {
                i += 1;
            }
        }
        out.push(Piece::Lit(raw[start..i].to_string()));
    }
    out
}

#[cfg(test)]
mod tests {
    use crate::model::*;
    use crate::{Limits, parse_str};

    /// Enough of a specification to hang a constructor off.
    const HEAD: &str = "
        define endian=little;
        define space ram type=ram_space size=4 default;
        define space register type=register_space size=4;
        define register offset=0 size=4 [ r0 r1 r2 r3 sp pc statusreg ];
        define token instr(16) op=(10,15) cc=(8,9) rd=(4,7) rs=(0,3) simm8=(0,7) signed;
        define token ext(16) imm16=(0,15);
        attach variables [ rd rs ] [ r0 r1 r2 r3 ];
    ";

    fn spec(tail: &str) -> Spec {
        parse_str(&format!("{HEAD}{tail}")).expect("parses")
    }

    fn only(tail: &str) -> Constructor {
        let s = spec(tail);
        let root = s.table(s.root());
        assert_eq!(root.constructors.len(), 1);
        s.constructor(root.constructors[0]).clone()
    }

    #[test]
    fn the_first_word_of_a_root_display_is_the_mnemonic() {
        let c = only(":and rd,rs is op=1 & rd & rs { rd = rd & rs; }");
        assert_eq!(c.display.mnemonic.as_deref(), Some("and"));
        assert_eq!(c.operands.len(), 2);
        assert_eq!(c.operands[0].name, "rd");
    }

    #[test]
    fn a_caret_glues_an_operand_to_the_mnemonic() {
        let c = only(":bra^cc rd,rs is op=1 & cc & rd & rs { }");
        assert_eq!(c.display.mnemonic.as_deref(), Some("bra"));
        let names: Vec<&str> = c.operands.iter().map(|o| o.name.as_str()).collect();
        assert_eq!(names, ["cc", "rd", "rs"]);
        // The `^` leaves no gap, so `cc` follows the mnemonic with no literal
        // between them.
        assert_eq!(c.display.pieces[0], DisplayPiece::Operand(0));
    }

    #[test]
    fn a_leading_caret_means_there_is_no_mnemonic() {
        let c = only(":^rd is op=1 & rd { }");
        assert_eq!(c.display.mnemonic, None);
        assert_eq!(c.operands.len(), 1);
    }

    #[test]
    fn a_quoted_word_in_a_display_is_literal() {
        let c = only(":mov \"sp\",rd is op=1 & rd { }");
        assert_eq!(c.display.mnemonic.as_deref(), Some("mov"));
        assert_eq!(c.operands.len(), 1, "sp is quoted, so it is not an operand");
        assert_eq!(
            c.display.pieces[0],
            DisplayPiece::Literal(" sp,".into()),
            "{:?}",
            c.display.pieces
        );
    }

    #[test]
    fn a_subtable_constructor_has_no_mnemonic() {
        let s = spec("mode: rd is op=1 & rd { export rd; }\n:x mode is op=2 & mode { }");
        let Some(Symbol::Table(id)) = s.lookup("mode") else {
            panic!("mode should be a table");
        };
        let c = s.constructor(s.table(id).constructors[0]);
        assert_eq!(c.display.mnemonic, None);
        assert_eq!(c.operands.len(), 1);
    }

    #[test]
    fn an_operand_used_only_in_the_pattern_is_invisible() {
        let c = only(":jmp is op=1 & simm8 { }");
        assert_eq!(c.operands.len(), 1);
        assert!(c.operands[0].invisible);
        assert!(matches!(c.operands[0].source, OperandSource::Field(_)));
    }

    #[test]
    fn an_operand_the_action_section_computes_is_marked_so() {
        let s = spec(
            "dest: rel is simm8 [ rel = inst_next + simm8 * 4; ] { export *[ram]:4 rel; }\n:b dest is op=1 & dest { goto dest; }",
        );
        let Some(Symbol::Table(id)) = s.lookup("dest") else {
            panic!("dest should be a table");
        };
        let c = s.constructor(s.table(id).constructors[0]);
        let rel = c.operands.iter().find(|o| o.name == "rel").expect("rel");
        assert_eq!(rel.source, OperandSource::Computed);
        assert_eq!(c.disasm.len(), 1);
        let DisasmStmt::Assign { target, value } = &c.disasm[0] else {
            panic!("expected an assignment");
        };
        assert_eq!(*target, DisasmTarget::Operand(0));
        assert!(matches!(value, DisasmExpr::Binary(DisasmBinOp::Add, ..)));
    }

    #[test]
    fn a_with_block_supplies_a_table_and_a_pattern() {
        let s = spec(
            "define context statusreg mode=(0,1);\n\
             with mode1 : mode=1 {\n\
               :a rd is op=1 & rd { }\n\
               :b rd is op=2 & rd { }\n\
             }",
        );
        let Some(Symbol::Table(id)) = s.lookup("mode1") else {
            panic!("mode1 should be a table");
        };
        assert_eq!(s.table(id).constructors.len(), 2);
        let c = s.constructor(s.table(id).constructors[0]);
        // The with block's constraint is joined on with `&`.
        assert!(matches!(c.pattern, PatternExpr::And(..)));
        assert_eq!(c.resolved.alternatives[0].context.mask, vec![0xc0]);
        assert_eq!(c.resolved.alternatives[0].context.value, vec![0x40]);
    }

    #[test]
    fn with_blocks_nest_and_the_innermost_header_wins() {
        let s =
            spec("with outer : op=1 {\n with inner : rd=2 {\n : x is rs { }\n }\n :y is rd { }\n}");
        let Some(Symbol::Table(inner)) = s.lookup("inner") else {
            panic!("inner should be a table");
        };
        let Some(Symbol::Table(outer)) = s.lookup("outer") else {
            panic!("outer should be a table");
        };
        assert_eq!(s.table(inner).constructors.len(), 1);
        assert_eq!(s.table(outer).constructors.len(), 1);
        let c = s.constructor(s.table(inner).constructors[0]);
        let alt = &c.resolved.alternatives[0];
        // op=1 from the outer block and rd=2 from the inner one, both applied.
        assert_eq!(alt.instr.mask, vec![0xf0, 0xfc]);
    }

    #[test]
    fn unimpl_leaves_the_body_missing_rather_than_empty() {
        let c = only(":cache rd is op=1 & rd unimpl");
        assert!(c.is_unimplemented());
        let empty = only(":nop is op=2 { }");
        assert_eq!(empty.body.as_deref(), Some(&[][..]));
    }

    #[test]
    fn a_macro_takes_parameters_by_name() {
        let s = spec(
            "macro flags(v) { statusreg = (v == 0); }\n:add rd,rs is op=1 & rd & rs { rd = rd + rs; flags(rd); }",
        );
        let Some(Symbol::Macro(id)) = s.lookup("flags") else {
            panic!("flags should be a macro");
        };
        let def = s.macro_def(id);
        assert_eq!(def.params, vec!["v".to_string()]);
        let Stmt::Assign { value, .. } = &def.body[0] else {
            panic!("expected an assignment");
        };
        let Expr::Binary(BinOp::Equal, left, _) = value else {
            panic!("expected a comparison");
        };
        assert_eq!(**left, Expr::Symbol(SymbolRef::Param(0)));

        let c = s.constructor(s.table(s.root()).constructors[0]);
        let body = c.body.as_ref().expect("a body");
        assert!(matches!(body[1], Stmt::MacroCall { mac, .. } if mac == id));
    }

    #[test]
    fn temporaries_are_created_by_assignment_with_or_without_local() {
        let c = only(":x rd is op=1 & rd { local t:4 = rd; u = t + 1; rd = u; }");
        let names: Vec<&str> = c.locals.iter().map(|l| l.name.as_str()).collect();
        assert_eq!(names, ["t", "u"]);
        assert_eq!(c.locals[0].size, Some(4));
        assert_eq!(c.locals[1].size, None, "u never states its size");
    }

    #[test]
    fn a_bare_local_declares_without_assigning() {
        let c = only(":x rd is op=1 & rd { local t:4; rd = t; }");
        assert_eq!(c.body.as_ref().expect("a body")[0], Stmt::Declare(0));
        assert_eq!(c.locals[0].size, Some(4));
    }

    #[test]
    fn loads_and_stores_carry_their_space_and_size() {
        let c = only(":x rd,rs is op=1 & rd & rs { rd = *[ram]:2 rs; *:4 rs = rd; }");
        let body = c.body.as_ref().expect("a body");
        let Stmt::Assign { value, .. } = &body[0] else {
            panic!("expected an assignment");
        };
        let Expr::Load { space, size, .. } = value else {
            panic!("expected a load, found {value:?}");
        };
        assert!(space.is_some());
        assert_eq!(*size, Some(2));
        let Stmt::Assign {
            dest: Lvalue::Store { space, size, .. },
            ..
        } = &body[1]
        else {
            panic!("expected a store, found {:?}", body[1]);
        };
        assert_eq!(*space, None, "no override means the default space");
        assert_eq!(*size, Some(4));
    }

    #[test]
    fn truncation_and_shaving_are_different_operators() {
        let c = only(":x rd,rs is op=1 & rd & rs { rd = rs:2; rs = rd(2); }");
        let body = c.body.as_ref().expect("a body");
        let Stmt::Assign { value, .. } = &body[0] else {
            panic!("expected an assignment");
        };
        assert!(matches!(value, Expr::Truncate { bytes: 2, .. }));
        let Stmt::Assign { value, .. } = &body[1] else {
            panic!("expected an assignment");
        };
        assert!(matches!(value, Expr::Shave { bytes: 2, .. }));
    }

    #[test]
    fn a_sized_literal_is_not_a_truncation() {
        let c = only(":x rd is op=1 & rd { rd = 0:4; }");
        let Stmt::Assign { value, .. } = &c.body.as_ref().expect("a body")[0] else {
            panic!("expected an assignment");
        };
        assert_eq!(
            *value,
            Expr::Num {
                value: 0,
                size: Some(4)
            }
        );
    }

    #[test]
    fn bit_ranges_work_on_both_sides_of_an_assignment() {
        let c = only(":x rd,rs is op=1 & rd & rs { rd = zext(rs[3,1]); rs[3,1] = 1; }");
        let body = c.body.as_ref().expect("a body");
        let Stmt::Assign { value, .. } = &body[0] else {
            panic!("expected an assignment");
        };
        let Expr::Intrinsic { op, args } = value else {
            panic!("expected zext");
        };
        assert_eq!(*op, Intrinsic::Zext);
        assert!(matches!(
            args[0],
            Expr::BitRange {
                lsb: 3,
                bits: 1,
                ..
            }
        ));
        assert!(matches!(
            body[1],
            Stmt::Assign {
                dest: Lvalue::BitRange {
                    lsb: 3,
                    bits: 1,
                    ..
                },
                ..
            }
        ));
    }

    #[test]
    fn branches_come_in_all_six_forms() {
        let c = only(
            ":x rd is op=1 & rd { \
               goto 0x1000; \
               goto [rd]; \
               call 0x2000; \
               call [rd]; \
               if (rd == 0) goto <done>; \
               <done> \
               return [rd]; }",
        );
        let body = c.body.as_ref().expect("a body");
        assert!(matches!(body[0], Stmt::Goto(JumpTarget::Direct { .. })));
        assert!(matches!(body[1], Stmt::Goto(JumpTarget::Indirect(_))));
        assert!(matches!(body[2], Stmt::Call(JumpTarget::Direct { .. })));
        assert!(matches!(body[3], Stmt::Call(JumpTarget::Indirect(_))));
        assert!(matches!(
            body[4],
            Stmt::CondGoto {
                target: JumpTarget::Label(0),
                ..
            }
        ));
        assert_eq!(body[5], Stmt::Label(0));
        assert!(matches!(body[6], Stmt::Return(_)));
        assert_eq!(c.labels, vec!["done".to_string()]);
    }

    #[test]
    fn a_branch_may_name_another_address_space() {
        let s = spec("define space code type=ram_space size=4;\n:x is op=1 { goto 0x0[code]; }");
        let c = s.constructor(s.table(s.root()).constructors[0]);
        let Some(Stmt::Goto(JumpTarget::Direct { space, .. })) = c.body.as_ref().map(|b| &b[0])
        else {
            panic!("expected a direct branch");
        };
        assert!(space.is_some(), "the [code] override should have been read");
    }

    #[test]
    fn build_delayslot_and_crossbuild_are_statements() {
        let s = spec(
            "cc: \"c\" is cc=1 { } \n\
             :x cc,rd is op=1 & cc & rd { build cc; delayslot(1); crossbuild inst_next, cc; }",
        );
        let c = s.constructor(s.table(s.root()).constructors[0]);
        let body = c.body.as_ref().expect("a body");
        assert_eq!(body[0], Stmt::Build(0));
        assert_eq!(body[1], Stmt::DelaySlot(1));
        assert!(matches!(body[2], Stmt::CrossBuild { .. }));
    }

    #[test]
    fn exports_come_as_values_or_as_dynamic_references() {
        let s = spec(
            "a: rd is op=1 & rd { export rd; }\n\
             b: rd is op=2 & rd { export *[ram]:4 rd; }\n\
             :x a,b is op=3 & a & b { }",
        );
        for (name, dynamic) in [("a", false), ("b", true)] {
            let Some(Symbol::Table(id)) = s.lookup(name) else {
                panic!("{name} should be a table");
            };
            let c = s.constructor(s.table(id).constructors[0]);
            let Some(Stmt::Export(export)) = c.body.as_ref().and_then(|b| b.last()) else {
                panic!("{name} should export");
            };
            assert_eq!(matches!(export, Export::Deref { .. }), dynamic);
        }
    }

    #[test]
    fn a_user_operation_is_a_call_in_an_expression_and_a_statement() {
        let s = spec(
            "define pcodeop arctan;\n:x rd,rs is op=1 & rd & rs { rd = arctan(rs); arctan(rd); }",
        );
        let c = s.constructor(s.table(s.root()).constructors[0]);
        let body = c.body.as_ref().expect("a body");
        let Stmt::Assign { value, .. } = &body[0] else {
            panic!("expected an assignment");
        };
        assert!(matches!(value, Expr::UserOp { .. }));
        assert!(matches!(body[1], Stmt::UserOp { .. }));
    }

    #[test]
    fn comparisons_written_backwards_become_the_same_operator() {
        let c = only(":x rd,rs is op=1 & rd & rs { rd = rs s> rd; }");
        let Stmt::Assign { value, .. } = &c.body.as_ref().expect("a body")[0] else {
            panic!("expected an assignment");
        };
        let Expr::Binary(BinOp::SLess, left, right) = value else {
            panic!("a s> b should be b s< a, found {value:?}");
        };
        assert_eq!(**left, Expr::Symbol(SymbolRef::Operand(0)));
        assert_eq!(**right, Expr::Symbol(SymbolRef::Operand(1)));
    }

    #[test]
    fn arithmetic_binds_tighter_than_comparison() {
        let c = only(":x rd,rs is op=1 & rd & rs { rd = rd + rs == 0; }");
        let Stmt::Assign { value, .. } = &c.body.as_ref().expect("a body")[0] else {
            panic!("expected an assignment");
        };
        let Expr::Binary(BinOp::Equal, left, _) = value else {
            panic!("the comparison should be outermost, found {value:?}");
        };
        assert!(matches!(**left, Expr::Binary(BinOp::Add, ..)));
    }

    #[test]
    fn attachments_of_every_kind_land_on_their_fields() {
        let s = spec(
            "attach names [ cc ] [ \"eq\" \"ne\" _ \"cc\" ];\n\
             attach values [ simm8 ] [ 1 2 -3 ];\n\
             :x cc is op=1 & cc { }",
        );
        let Some(Symbol::Field(cc)) = s.lookup("cc") else {
            panic!("cc should be a field");
        };
        let Attach::Names(names) = &s.field(cc).attach else {
            panic!("cc should have names attached");
        };
        assert_eq!(names[0].as_deref(), Some("eq"));
        assert_eq!(names[2], None, "an underscore leaves a gap");
        let Some(Symbol::Field(simm8)) = s.lookup("simm8") else {
            panic!("simm8 should be a field");
        };
        let Attach::Values(values) = &s.field(simm8).attach else {
            panic!("simm8 should have values attached");
        };
        assert_eq!(values, &[Some(1), Some(2), Some(-3)]);
    }

    #[test]
    fn a_token_may_override_the_specification_endianness() {
        let s = parse_str(
            "define endian=big;\n\
             define space ram type=ram_space size=4 default;\n\
             define token t(32) endian = little a=(0,7);\n\
             :x a is a { }",
        )
        .expect("parses");
        assert_eq!(s.endian, Endian::Big);
        assert_eq!(s.tokens[0].endian, Endian::Little);
    }

    #[test]
    fn a_bitrange_is_defined_over_a_register() {
        let s = spec("define bitrange zf=statusreg[10,1];\n:x is op=1 { zf = 1; }");
        let Some(Symbol::BitRange(id)) = s.lookup("zf") else {
            panic!("zf should be a bit range");
        };
        assert_eq!(s.bitranges[id.index()].low, 10);
        assert_eq!(s.bitranges[id.index()].bits, 1);
    }

    #[test]
    fn a_register_list_skips_the_underscores() {
        let s = parse_str(
            "define endian=little;\n\
             define space ram type=ram_space size=4 default;\n\
             define space register type=register_space size=4;\n\
             define register offset=0 size=1 [ AL AH _ _ CL ];\n\
             define token t(8) f=(0,7);\n\
             :x is f=1 { }",
        )
        .expect("parses");
        assert_eq!(s.varnodes.len(), 3);
        let Some(Symbol::Varnode(cl)) = s.lookup("CL") else {
            panic!("CL should be a register");
        };
        assert_eq!(s.varnode(cl).offset, 4, "two skipped names still take room");
    }

    #[test]
    fn globalset_names_the_context_field_it_publishes() {
        let s = spec(
            "define context statusreg mode=(0,1) noflow;\n\
             :m is op=1 [ mode=1; globalset(inst_next,mode); ] { }",
        );
        let c = s.constructor(s.table(s.root()).constructors[0]);
        assert!(matches!(
            c.disasm[0],
            DisasmStmt::Assign {
                target: DisasmTarget::Context(_),
                ..
            }
        ));
        assert!(matches!(c.disasm[1], DisasmStmt::GlobalSet { .. }));
        assert!(s.context_fields[0].noflow);
    }

    #[test]
    fn epsilon_matches_everything_and_consumes_nothing() {
        let c = only(":nothing is epsilon { }");
        assert_eq!(c.pattern, PatternExpr::Epsilon);
        assert_eq!(c.resolved.alternatives[0].length, 0);
        assert!(c.resolved.alternatives[0].instr.is_empty());
    }

    // ---- the failures a specification can contain ----

    #[test]
    fn a_table_that_is_never_defined_is_an_error() {
        let e = parse_str(&format!("{HEAD}:x nosuch is op=1 & nosuch {{ }}")).unwrap_err();
        assert!(e.message.contains("never defined"), "{e}");
    }

    #[test]
    fn a_name_a_body_cannot_see_is_an_error() {
        let e = parse_str(&format!("{HEAD}:x rd is op=1 & rd {{ rd = nosuch; }}")).unwrap_err();
        assert!(e.message.contains("can see"), "{e}");
    }

    #[test]
    fn a_field_outside_its_token_is_an_error() {
        let e = parse_str(
            "define endian=little;\n\
             define space ram type=ram_space size=4 default;\n\
             define token t(8) f=(0,15);\n",
        )
        .unwrap_err();
        assert!(e.message.contains("outside"), "{e}");
    }

    #[test]
    fn a_token_that_is_not_whole_bytes_is_an_error() {
        let e = parse_str(
            "define endian=little;\n\
             define space ram type=ram_space size=4 default;\n\
             define token t(12) f=(0,7);\n",
        )
        .unwrap_err();
        assert!(e.message.contains("whole number of bytes"), "{e}");
    }

    #[test]
    fn an_error_names_the_file_and_line() {
        let e = parse_str(&format!("{HEAD}\n\n:x is op=1 & nosuchfield=2 {{ }}")).unwrap_err();
        let at = e.at.expect("a position");
        assert_eq!(&*at.file, "<input>");
        assert!(at.line > 1, "{at}");
    }

    #[test]
    fn the_limits_are_the_caller_s_to_set() {
        let mut loader =
            crate::preprocess::MemoryLoader::new().with("a.slaspec", "@include \"a.slaspec\"\n");
        let limits = Limits {
            include_depth: 2,
            ..Limits::default()
        };
        let e = crate::parse_with(std::path::Path::new("a.slaspec"), &mut loader, limits, &[])
            .unwrap_err();
        assert!(e.message.contains("more than 2 deep"), "{e}");
    }

    #[test]
    fn a_definition_may_come_from_the_caller() {
        let mut loader = crate::preprocess::MemoryLoader::new().with(
            "a.slaspec",
            "define endian=$(ENDIAN);\ndefine space ram type=ram_space size=4 default;\n",
        );
        let spec = crate::parse_with(
            std::path::Path::new("a.slaspec"),
            &mut loader,
            Limits::default(),
            &[("ENDIAN", "big")],
        )
        .expect("parses");
        assert_eq!(spec.endian, Endian::Big);
    }
}
