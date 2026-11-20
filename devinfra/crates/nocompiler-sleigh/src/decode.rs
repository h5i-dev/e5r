//! The decode walk: bytes and a context at an address to a constructor tree.
//!
//! This is the half of a SLEIGH runtime that turns [`crate::model::Spec`] into
//! instructions. The walk is the one [`crate::model`] describes:
//!
//! 1. Start at [`Spec::root`] and try each constructor in the table's own
//!    order, because an earlier constructor wins an overlap.
//! 2. Reject on the byte masks first. That is
//!    [`crate::model::ResolvedPattern::may_match`] and it is the fast path.
//! 3. Walk [`Constructor::order`], not [`Constructor::operands`]: operands are
//!    numbered in display order and arrive in stream order, and only the
//!    second resolves an [`Offset`] whose base is another operand.
//! 4. Re-evaluate [`Constructor::pattern`] whenever the masks are only a
//!    filter, which [`crate::model::ResolvedPattern::approximation`] and a
//!    non-empty [`crate::model::PatternAlt::residual`] both say.
//! 5. Run the disassembly actions, publish any `globalset`, render, and hand
//!    back the tree.
//!
//! # Context
//!
//! A constructor's `[ ctx = value; ]` changes how the rest of the *same*
//! instruction parses, so it runs during the descent, before the subtables
//! below it are matched. That is the whole mechanism ARM uses to reach most of
//! its instruction set: two constructors at the root set `ARMcond` and
//! `ARMcondCk` and then build `instruction` again, and without executing the
//! assignment the second pass matches nothing. `globalset` is different: it
//! applies to a *future* address, so it goes in [`ContextDb`] rather than into
//! the image being carried.
//!
//! # Trust
//!
//! A specification is input, and so are the bytes. Every recursion is depth
//! bounded, every walk is step bounded, every slice is checked, and the
//! rendered text has a ceiling. A decode either produces a tree or returns a
//! typed error; it does not panic and it does not run away.

use std::fmt;

use crate::context::{Commit, Context, ContextDb};
use crate::index::Index;
use crate::model::{
    Attach, Builtin, ConstraintOp, Constructor, ConstructorId, ContextFieldId, DisasmBinOp,
    DisasmExpr, DisasmStmt, DisasmTarget, DisasmUnOp, DisplayPiece, FieldId, NumberBase,
    OperandSource, PatternAlt, PatternExpr, Spec, Stmt, SymbolRef, TableId, VarnodeId,
};

/// What stopped a decode.
///
/// Every one of these is a bound being reached or an input being short, never
/// an internal invariant, because a decoder fed a hostile specification and
/// hostile bytes has to be able to say which.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DecodeError {
    /// Nothing in the root table matched the bytes.
    NoMatch,
    /// The specification has no `instruction` table at all.
    NoRootTable,
    /// The constructor tree nested deeper than [`DecodeLimits::max_depth`].
    TooDeep,
    /// More constructors were tried than [`DecodeLimits::max_steps`] allows.
    TooManySteps,
    /// The tree grew past [`DecodeLimits::max_nodes`].
    TooManyNodes,
    /// The match ran past [`DecodeLimits::max_bytes`].
    TooLong,
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            DecodeError::NoMatch => "no constructor matched",
            DecodeError::NoRootTable => "the specification has no instruction table",
            DecodeError::TooDeep => "the constructor tree nested too deeply",
            DecodeError::TooManySteps => "too many constructors were tried",
            DecodeError::TooManyNodes => "the constructor tree grew too large",
            DecodeError::TooLong => "the instruction ran past the length ceiling",
        };
        f.write_str(s)
    }
}

impl std::error::Error for DecodeError {}

/// The ceilings a decode runs under.
///
/// All of them are far above what the published corpus needs: the deepest
/// constructor tree Ghidra ships is well under twenty, and the longest
/// instruction any of its specifications encodes is x86's fifteen bytes plus
/// the slack a specification is allowed. They exist so a corrupted
/// specification costs an error rather than a stack overflow.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodeLimits {
    /// Deepest subtable nesting.
    pub max_depth: usize,
    /// Most constructors in one instruction's tree.
    pub max_nodes: usize,
    /// Most constructors tried, matched or not, for one instruction.
    pub max_steps: usize,
    /// Longest instruction in bytes.
    pub max_bytes: usize,
    /// Longest rendered text in bytes.
    pub max_text: usize,
}

impl Default for DecodeLimits {
    fn default() -> DecodeLimits {
        DecodeLimits {
            max_depth: 64,
            max_nodes: 256,
            max_steps: 200_000,
            max_bytes: 64,
            max_text: 4096,
        }
    }
}

/// What one operand of a matched constructor resolved to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    /// An integer: a token field, a context field, or a value a disassembly
    /// action computed. Already through `attach values` where there was one.
    Int(i64),
    /// A register, either named in the pattern or selected by
    /// `attach variables`.
    Var(VarnodeId),
    /// A display string selected by `attach names`.
    Name(String),
    /// A subtable, at this index into [`Decoded::nodes`].
    Sub(u32),
    /// Nothing in the constructor binds it. The specification's own mistake,
    /// kept rather than guessed at.
    Unresolved,
}

/// One operand of a matched constructor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedOperand {
    /// Byte offset from the instruction's own address where its bits begin.
    pub start: usize,
    /// Byte offset just past its match. Equal to `start` for anything that
    /// consumes no instruction bytes, which is what [`Offset::resolve`] wants
    /// from the operand it is measured against.
    pub end: usize,
    /// What it resolved to.
    pub value: Value,
    /// The integer the bits held before any attachment, which is what a
    /// disassembly action and a pattern constraint see.
    pub raw: i64,
}

impl Default for ResolvedOperand {
    fn default() -> ResolvedOperand {
        ResolvedOperand {
            start: 0,
            end: 0,
            value: Value::Unresolved,
            raw: 0,
        }
    }
}

/// One matched constructor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    /// Which constructor matched.
    pub constructor: ConstructorId,
    /// Byte offset from the instruction's address where it begins.
    pub start: usize,
    /// Byte offset just past everything it and its subtables matched.
    pub end: usize,
    /// Its operands, indexed the way [`Constructor::operands`] is.
    pub operands: Vec<ResolvedOperand>,
}

/// A decoded instruction: the constructor tree, its length, and the context it
/// was decoded under.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decoded {
    /// Where it starts.
    pub addr: u64,
    /// How many bytes it occupies.
    pub len: usize,
    /// The tree. Index zero is the root table's constructor.
    pub nodes: Vec<Node>,
    /// The context image the match ran under, after any `[ ctx = ... ]` the
    /// tree executed.
    pub context: Context,
    /// Values `globalset` published, and where.
    pub commits: Vec<(u64, Commit)>,
}

impl Decoded {
    /// The root constructor.
    pub fn root(&self) -> &Node {
        &self.nodes[0]
    }

    /// One past the last byte.
    pub fn end(&self) -> u64 {
        self.addr.wrapping_add(self.len as u64)
    }

    /// The mnemonic, when the root constructor named one. A constructor whose
    /// display begins with `^` has none.
    pub fn mnemonic<'a>(&self, spec: &'a Spec) -> Option<&'a str> {
        spec.constructor(self.nodes[0].constructor)
            .display
            .mnemonic
            .as_deref()
    }

    /// Render the whole instruction the way the specification's display
    /// sections say.
    pub fn text(&self, spec: &Spec) -> String {
        self.text_with(spec, &DecodeLimits::default())
    }

    /// The same, under an explicit text ceiling.
    pub fn text_with(&self, spec: &Spec, limits: &DecodeLimits) -> String {
        let mut out = String::new();
        let c = spec.constructor(self.nodes[0].constructor);
        if let Some(m) = &c.display.mnemonic {
            out.push_str(m);
        }
        self.render_into(spec, 0, &mut out, limits.max_text, 0);
        out
    }

    /// Render one node of the tree, without its mnemonic.
    pub fn render(&self, spec: &Spec, node: u32) -> String {
        let mut out = String::new();
        if let Some(m) = &spec
            .constructor(self.nodes[node as usize].constructor)
            .display
            .mnemonic
        {
            out.push_str(m);
        }
        self.render_into(spec, node, &mut out, DecodeLimits::default().max_text, 0);
        out
    }

    fn render_into(&self, spec: &Spec, node: u32, out: &mut String, cap: usize, depth: usize) {
        if depth > 64 || out.len() >= cap {
            return;
        }
        let Some(n) = self.nodes.get(node as usize) else {
            return;
        };
        let c = spec.constructor(n.constructor);
        for piece in &c.display.pieces {
            if out.len() >= cap {
                return;
            }
            match piece {
                DisplayPiece::Literal(s) => out.push_str(s),
                DisplayPiece::Operand(i) => {
                    let Some(op) = n.operands.get(*i as usize) else {
                        continue;
                    };
                    match &op.value {
                        Value::Sub(child) => {
                            if let Some(m) = &spec
                                .constructor(self.nodes[*child as usize].constructor)
                                .display
                                .mnemonic
                            {
                                out.push_str(m);
                            }
                            self.render_into(spec, *child, out, cap, depth + 1);
                        }
                        Value::Var(v) => out.push_str(&spec.varnode(*v).name),
                        Value::Name(s) => out.push_str(s),
                        Value::Int(v) => {
                            let base = operand_base(spec, c, *i as usize);
                            push_int(out, *v, base);
                        }
                        Value::Unresolved => out.push_str("<unresolved>"),
                    }
                }
            }
        }
    }

    /// Whether any constructor in the tree declined to model its semantics.
    pub fn is_unimplemented(&self, spec: &Spec) -> bool {
        self.nodes
            .iter()
            .any(|n| spec.constructor(n.constructor).is_unimplemented())
    }
}

/// How a field's integer prints, which is the field's own `hex`/`dec`.
fn operand_base(spec: &Spec, c: &Constructor, operand: usize) -> NumberBase {
    match c.operands.get(operand).map(|o| o.source) {
        Some(OperandSource::Field(id)) => spec.field(id).base,
        Some(OperandSource::Context(id)) => spec.context_field(id).base,
        _ => NumberBase::Hex,
    }
}

/// Print an integer the way a SLEIGH display does: hex with an `0x` prefix and
/// the sign outside it, or plain decimal.
fn push_int(out: &mut String, v: i64, base: NumberBase) {
    match base {
        NumberBase::Dec => {
            let _ = fmt::Write::write_fmt(out, format_args!("{v}"));
        }
        NumberBase::Hex if v < 0 => {
            let _ = fmt::Write::write_fmt(out, format_args!("-0x{:x}", v.unsigned_abs()));
        }
        NumberBase::Hex => {
            let _ = fmt::Write::write_fmt(out, format_args!("0x{v:x}"));
        }
    }
}

/// A decode engine over one specification.
///
/// Holds the context database, so a linear sweep sees the context a `globalset`
/// published earlier in the sweep. Decoding the same address twice gives the
/// same answer: a commit replaces rather than accumulates.
#[derive(Debug, Clone)]
pub struct Decoder<'a> {
    spec: &'a Spec,
    index: Index,
    limits: DecodeLimits,
    base: Context,
    db: ContextDb,
}

impl<'a> Decoder<'a> {
    /// A decoder over `spec`, with an all-zero starting context.
    pub fn new(spec: &'a Spec) -> Decoder<'a> {
        Decoder {
            base: Context::for_spec(spec),
            index: Index::build(spec),
            spec,
            limits: DecodeLimits::default(),
            db: ContextDb::default(),
        }
    }

    /// A decoder over `spec` reusing an index built earlier. Building the
    /// index walks every constructor, so a caller decoding with several
    /// decoders over one specification should build it once.
    pub fn with_index(spec: &'a Spec, index: Index) -> Decoder<'a> {
        Decoder {
            base: Context::for_spec(spec),
            index,
            spec,
            limits: DecodeLimits::default(),
            db: ContextDb::default(),
        }
    }

    /// The constructor order and prefilter this decoder uses.
    pub fn index(&self) -> &Index {
        &self.index
    }

    /// Replace the ceilings.
    pub fn with_limits(mut self, limits: DecodeLimits) -> Decoder<'a> {
        self.limits = limits;
        self
    }

    /// The specification being decoded against.
    pub fn spec(&self) -> &'a Spec {
        self.spec
    }

    /// The context every decode starts from, before anything the database
    /// published at the address. This is where a `.pspec` default, or a
    /// caller's knowledge that a region is Thumb, goes.
    pub fn base_context(&mut self) -> &mut Context {
        &mut self.base
    }

    /// Set one context field in the starting context, by name. Returns false
    /// when the specification has no such field, or the field does not fit.
    pub fn set_context(&mut self, name: &str, value: u64) -> bool {
        let Some(id) = self.context_field_id(name) else {
            return false;
        };
        let field = self.spec.context_field(id);
        self.base.set(field, value)
    }

    /// A context field's index, by name.
    pub fn context_field_id(&self, name: &str) -> Option<ContextFieldId> {
        match self.spec.lookup(name) {
            Some(crate::model::Symbol::Context(id)) => Some(id),
            _ => None,
        }
    }

    /// The database of published context values.
    pub fn context_db(&self) -> &ContextDb {
        &self.db
    }

    /// The same, mutably, so a caller can seed it or clear it between runs.
    pub fn context_db_mut(&mut self) -> &mut ContextDb {
        &mut self.db
    }

    /// Decode one instruction at `addr` from `bytes`, which start at `addr`.
    ///
    /// Any `globalset` the instruction performs is published into the context
    /// database before this returns, so a caller sweeping forwards sees it.
    pub fn decode(&mut self, bytes: &[u8], addr: u64) -> Result<Decoded, DecodeError> {
        let decoded = self.decode_at(bytes, addr)?;
        for (at, commit) in &decoded.commits {
            self.db.commit(*at, *commit);
        }
        Ok(decoded)
    }

    /// Decode without publishing, for a caller that wants to decide whether to
    /// believe the result first.
    pub fn decode_at(&self, bytes: &[u8], addr: u64) -> Result<Decoded, DecodeError> {
        if self.spec.tables.is_empty() {
            return Err(DecodeError::NoRootTable);
        }
        let mut ctx = self.base;
        self.db.apply(self.spec, addr, &mut ctx);

        let cap = bytes.len().min(self.limits.max_bytes);
        let mut walk = Walk {
            spec: self.spec,
            index: &self.index,
            bytes: &bytes[..cap],
            addr,
            limits: &self.limits,
            ctx,
            nodes: Vec::new(),
            steps: 0,
            commits: Vec::new(),
        };
        let root = walk
            .table(self.spec.root(), 0, 0)?
            .ok_or(DecodeError::NoMatch)?;
        debug_assert_eq!(root, 0, "the root constructor is always node zero");

        let len = walk.nodes[0].end;
        if len > self.limits.max_bytes {
            return Err(DecodeError::TooLong);
        }
        // Second pass: `inst_next` is only known now, and the disassembly
        // actions that compute operand values and publish context are written
        // against it. Children first, so a parent reads values its subtables
        // have already computed.
        walk.actions(0, len, 0);

        Ok(Decoded {
            addr,
            len,
            nodes: walk.nodes,
            context: walk.ctx,
            commits: walk.commits,
        })
    }

    /// Decode and render in one step, which is what a disassembly listing
    /// wants.
    pub fn disassemble(
        &mut self,
        bytes: &[u8],
        addr: u64,
    ) -> Result<(Decoded, String), DecodeError> {
        let d = self.decode(bytes, addr)?;
        let text = d.text_with(self.spec, &self.limits);
        Ok((d, text))
    }
}

/// What resolving one operand did.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Resolved {
    /// It has a place and a value.
    Yes,
    /// Its place is measured from a subtable not yet matched, so it waits for
    /// the pass after the disassembly actions have run.
    Deferred,
    /// The encoding is not this constructor's after all. An `attach variables`
    /// hole and a slice too short both land here.
    No,
}

/// The state of one instruction's walk.
struct Walk<'a> {
    spec: &'a Spec,
    index: &'a Index,
    bytes: &'a [u8],
    addr: u64,
    limits: &'a DecodeLimits,
    ctx: Context,
    nodes: Vec<Node>,
    steps: usize,
    commits: Vec<(u64, Commit)>,
}

impl Walk<'_> {
    /// Try every constructor of `table`, in the specification's order, at byte
    /// offset `at`.
    fn table(
        &mut self,
        table: TableId,
        at: usize,
        depth: usize,
    ) -> Result<Option<u32>, DecodeError> {
        if depth > self.limits.max_depth {
            return Err(DecodeError::TooDeep);
        }
        let stream = self.bytes.get(at..).unwrap_or(&[]);
        let ctx = self.ctx.word();
        // Most specific first, which is the order the containment rule in the
        // SLEIGH manual requires; see `crate::index`.
        let candidates = self.index.candidates(table, stream);
        for i in 0..candidates.len() {
            let cid = self.index.candidates(table, stream)[i];
            if !self.index.may_start(cid, stream, ctx) {
                continue;
            }
            if let Some(node) = self.constructor(cid, at, depth)? {
                return Ok(Some(node));
            }
        }
        Ok(None)
    }

    fn constructor(
        &mut self,
        cid: ConstructorId,
        at: usize,
        depth: usize,
    ) -> Result<Option<u32>, DecodeError> {
        self.steps += 1;
        if self.steps > self.limits.max_steps {
            return Err(DecodeError::TooManySteps);
        }
        let c = self.spec.constructor(cid);
        let stream = self.bytes.get(at..).unwrap_or(&[]);

        for alt in &c.resolved.alternatives {
            if !alt.instr.matches(stream) || !alt.context.matches(self.ctx.bytes()) {
                continue;
            }
            // Everything past here can fail, and a failure must leave no trace:
            // a half-built subtree and a half-applied context change would both
            // corrupt the next alternative's attempt.
            let mark = self.nodes.len();
            let saved = self.ctx;
            match self.try_alt(cid, c, alt, at, depth)? {
                Some(node) => return Ok(Some(node)),
                None => {
                    self.nodes.truncate(mark);
                    self.ctx = saved;
                }
            }
        }
        Ok(None)
    }

    fn try_alt(
        &mut self,
        cid: ConstructorId,
        c: &Constructor,
        alt: &PatternAlt,
        at: usize,
        depth: usize,
    ) -> Result<Option<u32>, DecodeError> {
        if self.nodes.len() >= self.limits.max_nodes {
            return Err(DecodeError::TooManyNodes);
        }
        let me = self.nodes.len() as u32;
        self.nodes.push(Node {
            constructor: cid,
            start: at,
            end: at.saturating_add(alt.length),
            operands: vec![ResolvedOperand::default(); c.operands.len()],
        });
        for op in &mut self.nodes[me as usize].operands {
            op.start = at;
            op.end = at;
        }

        // Operands not in `order` are ones a malformed specification left out
        // of its own pattern. They still need a place rather than being left
        // at zero, so the walk is `order` and then whatever it missed.
        let mut extra: Vec<u16>;
        let sequence: &[u16] = if c.order.len() == c.operands.len() {
            &c.order
        } else {
            extra = c.order.clone();
            for oi in 0..c.operands.len() as u16 {
                if !extra.contains(&oi) {
                    extra.push(oi);
                }
            }
            &extra
        };

        // A bitmask rather than a vector: no constructor in the published
        // corpus has anywhere near sixty-four operands, and the fallback keeps
        // one that does correct rather than fast.
        let mut done: u64 = 0;
        // Two passes, because a `[ ctx = ... ]` is written against the token
        // fields of the constructor it sits in and has to run before the
        // subtables below it are matched. AArch64 is the case that forces it:
        //
        //   :^instruction is ImmS_ImmR_TestSet=0 & ImmR & ImmS & instruction
        //   [ ImmS_LT_ImmR = ...ImmR...ImmS...; ImmS_ImmR_TestSet=1; ] {}
        //
        // The action reads two token fields and writes five context fields
        // that the second pass over `instruction` then matches against, which
        // is how `lsl` is preferred over `ubfm`. Running the action before the
        // fields are read computes it from nothing; running it after the
        // subtable is matched is too late.
        for &oi in sequence {
            let table = matches!(
                c.operands.get(oi as usize).map(|o| o.source),
                Some(OperandSource::Table(_))
            );
            if table {
                continue;
            }
            match self.operand(c, alt, me, oi, at, depth, true)? {
                Resolved::Yes if oi < 64 => done |= 1 << oi,
                Resolved::Yes => {}
                // Its offset is measured from a subtable that has not been
                // matched yet, so it waits for the second pass.
                Resolved::Deferred => {}
                Resolved::No => return Ok(None),
            }
        }

        self.apply_context_assigns(c, me);

        for &oi in sequence {
            if oi < 64 && done >> oi & 1 == 1 {
                continue;
            }
            if self.operand(c, alt, me, oi, at, depth, false)? != Resolved::Yes {
                return Ok(None);
            }
        }

        if c.resolved.approximation.is_some() || !alt.residual.is_empty() {
            let (ok, _) = self.eval_pattern(&c.pattern, me, at, 0, 0);
            if !ok {
                return Ok(None);
            }
        }
        Ok(Some(me))
    }

    /// Resolve one operand.
    ///
    /// `first_pass` asks for the operands a disassembly action can be written
    /// against: anything whose place is already known. In that pass an operand
    /// measured from a subtable that has not been matched yet is deferred
    /// rather than failed.
    #[allow(clippy::too_many_arguments)]
    fn operand(
        &mut self,
        c: &Constructor,
        alt: &PatternAlt,
        me: u32,
        oi: u16,
        at: usize,
        depth: usize,
        first_pass: bool,
    ) -> Result<Resolved, DecodeError> {
        let Some(spec_op) = c.operands.get(oi as usize) else {
            return Ok(Resolved::Yes);
        };
        let placement = alt
            .offsets
            .get(oi as usize)
            .copied()
            .unwrap_or(spec_op.offset);

        // Bases are measured from the constructor's own start, and
        // `Constructor::order` guarantees the base was resolved first.
        let ops = &self.nodes[me as usize].operands;
        let known = |i: u16| -> Option<usize> {
            let op = ops.get(i as usize)?;
            (!matches!(op.value, Value::Unresolved) || op.end != op.start).then(|| op.end - at)
        };
        let Some(rel) = placement.resolve(|i| {
            if first_pass {
                known(i)
            } else {
                ops.get(i as usize).map(|o| o.end - at)
            }
        }) else {
            return Ok(if first_pass {
                Resolved::Deferred
            } else {
                Resolved::No
            });
        };
        let start = at.saturating_add(rel);
        if start > self.limits.max_bytes {
            return Err(DecodeError::TooLong);
        }

        let (value, raw, end) = match spec_op.source {
            OperandSource::Field(fid) => {
                let field = self.spec.field(fid);
                let token = self.spec.token_of(fid);
                let Some(slice) = self.bytes.get(start..) else {
                    return Ok(Resolved::No);
                };
                let Some(raw) = field.extract(token, slice) else {
                    return Ok(Resolved::No);
                };
                let signed = if field.signed {
                    crate::model::sign_extend(raw, field.bits())
                } else {
                    raw as i64
                };
                let Some(v) = attached(&field.attach, raw, signed) else {
                    return Ok(Resolved::No);
                };
                (v, signed, start + token.size as usize)
            }
            OperandSource::Context(cid) => {
                let field = self.spec.context_field(cid);
                let Some(raw) = self.ctx.get(field) else {
                    return Ok(Resolved::No);
                };
                let signed = if field.signed {
                    crate::model::sign_extend(raw, field.bits())
                } else {
                    raw as i64
                };
                let Some(v) = attached(&field.attach, raw, signed) else {
                    return Ok(Resolved::No);
                };
                (v, signed, start)
            }
            OperandSource::Table(tid) => {
                let Some(child) = self.table(tid, start, depth + 1)? else {
                    return Ok(Resolved::No);
                };
                let end = self.nodes[child as usize].end;
                (Value::Sub(child), 0, end)
            }
            OperandSource::Varnode(vid) => (Value::Var(vid), 0, start),
            // A `define bitrange` names bits inside a register. It has no
            // encoding of its own, so there is nothing to read here; the
            // semantic body is where it means something.
            OperandSource::BitRange(_) => (Value::Unresolved, 0, start),
            // Filled in by the disassembly action pass, which needs a length
            // this walk has not established yet.
            OperandSource::Computed => (Value::Int(0), 0, start),
            OperandSource::Unbound => (Value::Unresolved, 0, start),
        };

        let node = &mut self.nodes[me as usize];
        node.operands[oi as usize] = ResolvedOperand {
            start,
            end,
            value,
            raw,
        };
        if end > node.end {
            node.end = end;
        }
        Ok(Resolved::Yes)
    }

    /// Execute the `[ ctx = ... ]` statements of a constructor, which are the
    /// only disassembly actions that have to run during the descent.
    fn apply_context_assigns(&mut self, c: &Constructor, me: u32) {
        for stmt in &c.disasm {
            let DisasmStmt::Assign {
                target: DisasmTarget::Context(cid),
                value,
            } = stmt
            else {
                continue;
            };
            // `inst_next` is not known during the descent. A value that needs
            // it is left alone rather than computed from a wrong length.
            let Some(v) = self.eval_disasm(value, me, None) else {
                continue;
            };
            let Some(field) = self.spec.context_fields.get(cid.index()) else {
                continue;
            };
            self.ctx.set(field, v as u64);
        }
    }

    /// The second pass: operand values and `globalset`, with the instruction's
    /// length known. Children first.
    fn actions(&mut self, node: u32, len: usize, depth: usize) {
        if depth > self.limits.max_depth {
            return;
        }
        let children: Vec<u32> = self.nodes[node as usize]
            .operands
            .iter()
            .filter_map(|o| match o.value {
                Value::Sub(c) => Some(c),
                _ => None,
            })
            .collect();
        for child in children {
            self.actions(child, len, depth + 1);
        }

        let c = self.spec.constructor(self.nodes[node as usize].constructor);
        let next = self.addr.wrapping_add(len as u64);
        for stmt in &c.disasm {
            match stmt {
                DisasmStmt::Assign {
                    target: DisasmTarget::Operand(oi),
                    value,
                } => {
                    let Some(v) = self.eval_disasm(value, node, Some(next)) else {
                        continue;
                    };
                    if let Some(op) = self.nodes[node as usize].operands.get_mut(*oi as usize) {
                        op.value = Value::Int(v);
                        op.raw = v;
                    }
                }
                DisasmStmt::Assign { .. } => {}
                DisasmStmt::GlobalSet { address, context } => {
                    let Some(target) = self.eval_disasm(address, node, Some(next)) else {
                        continue;
                    };
                    let Some(field) = self.spec.context_fields.get(context.index()) else {
                        continue;
                    };
                    let Some(value) = self.ctx.get(field) else {
                        continue;
                    };
                    if self.commits.len() < 256 {
                        self.commits.push((
                            target as u64,
                            Commit {
                                field: *context,
                                value,
                                noflow: field.noflow,
                            },
                        ));
                    }
                }
            }
        }
    }

    // ---- pattern re-evaluation ----

    /// Evaluate a constructor's pattern as written, for the cases where the
    /// masks are only a filter.
    ///
    /// Constraints on an *operand* are settled from the operand's resolved
    /// offset, which the front end computed with the whole concatenation in
    /// view. Only a constraint on a bare field, which is not an operand and so
    /// has no recorded offset, is settled positionally, by walking `;` from the
    /// constructor's start. That split is what makes x86's `... (m128 &
    /// XmmReg ...); XmmCondPD` decidable at all: the suffix byte is an operand
    /// and its place came from the reducer.
    ///
    /// Returns whether the pattern holds and where it ends, both relative to
    /// the constructor's start.
    fn eval_pattern(
        &self,
        expr: &PatternExpr,
        me: u32,
        at: usize,
        start: usize,
        depth: usize,
    ) -> (bool, usize) {
        if depth > self.limits.max_depth {
            return (true, start);
        }
        match expr {
            PatternExpr::Epsilon => (true, start),
            PatternExpr::Symbol(sym) => (true, self.width_of(*sym, me, start)),
            PatternExpr::And(a, b) => {
                let (oka, ea) = self.eval_pattern(a, me, at, start, depth + 1);
                let (okb, eb) = self.eval_pattern(b, me, at, start, depth + 1);
                (oka && okb, ea.max(eb))
            }
            PatternExpr::Or(a, b) => {
                let (oka, ea) = self.eval_pattern(a, me, at, start, depth + 1);
                if oka {
                    return (true, ea);
                }
                self.eval_pattern(b, me, at, start, depth + 1)
            }
            PatternExpr::Cat(a, b) => {
                let (oka, ea) = self.eval_pattern(a, me, at, start, depth + 1);
                let (okb, eb) = self.eval_pattern(b, me, at, ea, depth + 1);
                (oka && okb, eb)
            }
            // `a ...` left justifies a and stops it forcing the length, so it
            // holds where a holds and contributes no end of its own.
            PatternExpr::EllipsisRight(a) => {
                let (ok, _) = self.eval_pattern(a, me, at, start, depth + 1);
                (ok, start)
            }
            // `... a` right justifies a at a length this walk does not know.
            // Constraints inside it that name operands still decide, because
            // an operand carries its own resolved offset; anything positional
            // inside it is admitted rather than guessed at, which is the safe
            // direction.
            PatternExpr::EllipsisLeft(a) => {
                let (ok, _) = self.eval_pattern(a, me, at, start, depth + 1);
                (ok, start)
            }
            PatternExpr::Constraint { lhs, op, rhs } => {
                let end = self.width_of(*lhs, me, start);
                let (Some(left), Some(right)) = (
                    self.symbol_value(*lhs, me, at, start),
                    self.eval_disasm(rhs, me, None),
                ) else {
                    // Something the model does not give a value to. Admitting
                    // it keeps the filter a filter.
                    return (true, end);
                };
                let ok = match op {
                    ConstraintOp::Equal => left == right,
                    ConstraintOp::NotEqual => left != right,
                    ConstraintOp::Less => left < right,
                    ConstraintOp::LessEqual => left <= right,
                    ConstraintOp::Greater => left > right,
                    ConstraintOp::GreaterEqual => left >= right,
                };
                (ok, end)
            }
        }
    }

    /// Where a symbol's bits end, relative to the constructor's start, given
    /// that they begin at `start`.
    fn width_of(&self, sym: SymbolRef, me: u32, start: usize) -> usize {
        match sym {
            SymbolRef::Operand(i) => match self.nodes[me as usize].operands.get(i as usize) {
                Some(op) => op.end - self.nodes[me as usize].start,
                None => start,
            },
            SymbolRef::Field(f) => match self.spec.fields.get(f.index()) {
                Some(field) => start + self.spec.tokens[field.token.index()].size as usize,
                None => start,
            },
            _ => start,
        }
    }

    /// The integer a pattern constraint compares.
    fn symbol_value(&self, sym: SymbolRef, me: u32, at: usize, start: usize) -> Option<i64> {
        match sym {
            SymbolRef::Operand(i) => {
                let op = self.nodes[me as usize].operands.get(i as usize)?;
                match op.value {
                    // A subtable constrained by value is not something the
                    // model gives an integer for.
                    Value::Sub(_) | Value::Unresolved => None,
                    _ => Some(op.raw),
                }
            }
            SymbolRef::Field(f) => self.field_at(f, at + start),
            SymbolRef::Context(c) => {
                let field = self.spec.context_fields.get(c.index())?;
                let raw = self.ctx.get(field)?;
                Some(if field.signed {
                    crate::model::sign_extend(raw, field.bits())
                } else {
                    raw as i64
                })
            }
            _ => None,
        }
    }

    /// Read a token field at an absolute byte offset.
    fn field_at(&self, id: FieldId, offset: usize) -> Option<i64> {
        let field = self.spec.fields.get(id.index())?;
        let token = self.spec.tokens.get(field.token.index())?;
        let raw = field.extract(token, self.bytes.get(offset..)?)?;
        Some(if field.signed {
            crate::model::sign_extend(raw, field.bits())
        } else {
            raw as i64
        })
    }

    // ---- disassembly time arithmetic ----

    /// Evaluate a disassembly expression. `next` is the address after the
    /// instruction, which is only known in the second pass; `None` makes
    /// `inst_next` unavailable rather than wrong.
    fn eval_disasm(&self, e: &DisasmExpr, me: u32, next: Option<u64>) -> Option<i64> {
        self.eval_disasm_at(e, me, next, 0)
    }

    fn eval_disasm_at(
        &self,
        e: &DisasmExpr,
        me: u32,
        next: Option<u64>,
        depth: usize,
    ) -> Option<i64> {
        if depth > self.limits.max_depth {
            return None;
        }
        match e {
            DisasmExpr::Num(v) => Some(*v),
            DisasmExpr::Symbol(s) => match s {
                SymbolRef::Builtin(Builtin::InstStart) => Some(self.addr as i64),
                SymbolRef::Builtin(Builtin::InstNext) => next.map(|n| n as i64),
                // The address after the *next* instruction needs a decode this
                // one has not done. Delay slots are the only user.
                SymbolRef::Builtin(Builtin::InstNext2) => None,
                SymbolRef::Builtin(Builtin::Epsilon) => Some(0),
                SymbolRef::Operand(i) => {
                    let op = self.nodes[me as usize].operands.get(*i as usize)?;
                    match op.value {
                        Value::Unresolved => None,
                        _ => Some(op.raw),
                    }
                }
                SymbolRef::Field(f) => self.field_at(*f, self.nodes[me as usize].start),
                SymbolRef::Context(c) => {
                    let field = self.spec.context_fields.get(c.index())?;
                    let raw = self.ctx.get(field)?;
                    Some(if field.signed {
                        crate::model::sign_extend(raw, field.bits())
                    } else {
                        raw as i64
                    })
                }
                SymbolRef::Varnode(v) => self.spec.varnodes.get(v.index()).map(|n| n.offset as i64),
                _ => None,
            },
            DisasmExpr::Unary(op, a) => {
                let a = self.eval_disasm_at(a, me, next, depth + 1)?;
                Some(match op {
                    DisasmUnOp::Negate => a.wrapping_neg(),
                    DisasmUnOp::Not => !a,
                })
            }
            DisasmExpr::Binary(op, a, b) => {
                let a = self.eval_disasm_at(a, me, next, depth + 1)?;
                let b = self.eval_disasm_at(b, me, next, depth + 1)?;
                Some(match op {
                    DisasmBinOp::Add => a.wrapping_add(b),
                    DisasmBinOp::Sub => a.wrapping_sub(b),
                    DisasmBinOp::Mul => a.wrapping_mul(b),
                    DisasmBinOp::Div => {
                        if b == 0 {
                            return None;
                        }
                        a.wrapping_div(b)
                    }
                    // A shift count wider than the type is zero, not undefined
                    // behaviour and not a panic.
                    DisasmBinOp::Shl => {
                        if !(0..64).contains(&b) {
                            0
                        } else {
                            a.wrapping_shl(b as u32)
                        }
                    }
                    DisasmBinOp::Shr => {
                        if !(0..64).contains(&b) {
                            if a < 0 { -1 } else { 0 }
                        } else {
                            a.wrapping_shr(b as u32)
                        }
                    }
                    DisasmBinOp::And => a & b,
                    DisasmBinOp::Or => a | b,
                    DisasmBinOp::Xor => a ^ b,
                })
            }
        }
    }
}

/// Put a field's raw value through its `attach`, if it has one. `None` means
/// the attachment has a hole at this encoding, which makes the encoding
/// invalid rather than falling back to the integer.
fn attached(attach: &Attach, raw: u64, signed: i64) -> Option<Value> {
    match attach {
        Attach::None => Some(Value::Int(signed)),
        Attach::Variables(v) => match v.get(raw as usize) {
            Some(Some(id)) => Some(Value::Var(*id)),
            _ => None,
        },
        Attach::Names(v) => match v.get(raw as usize) {
            Some(Some(s)) => Some(Value::Name(s.clone())),
            _ => None,
        },
        Attach::Values(v) => match v.get(raw as usize) {
            Some(Some(n)) => Some(Value::Int(*n)),
            _ => None,
        },
    }
}

/// What an instruction does to control flow, read off the semantic bodies of
/// the constructors that matched.
///
/// This is not part of the SLEIGH model: the language says `goto`, `call` and
/// `return`, and what a caller wants is whether the next instruction is a
/// successor and where else control can go. Derived here rather than in the
/// lifter because a disassembly listing wants it without lifting anything.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct FlowSummary {
    /// A `goto` with no condition, or a `return`.
    pub unconditional: bool,
    /// A `goto` under an `if`.
    pub conditional: bool,
    /// A `call` of either kind.
    pub call: bool,
    /// A `return`.
    pub ret: bool,
    /// The target of a direct branch or call, when there was exactly one and
    /// it was a constant.
    pub target: Option<u64>,
    /// A `goto [v]` or `call [v]`, whose target is not known here.
    pub indirect: bool,
}

impl FlowSummary {
    /// Whether the instruction after this one in address order is a successor.
    pub fn falls_through(&self) -> bool {
        !(self.unconditional || self.ret)
    }
}

impl Decoded {
    /// Summarise what the matched constructors do to control flow.
    pub fn flow(&self, spec: &Spec) -> FlowSummary {
        let mut out = FlowSummary::default();
        for node in &self.nodes {
            let Some(body) = &spec.constructor(node.constructor).body else {
                continue;
            };
            summarise(body, &mut out, 0);
        }
        out
    }
}

fn summarise(body: &[Stmt], out: &mut FlowSummary, depth: usize) {
    if depth > 16 {
        return;
    }
    for stmt in body {
        match stmt {
            // A `goto <label>` stays inside the instruction and is not a
            // machine level branch, which is why the target kind matters here.
            Stmt::Goto(t) => match t {
                crate::model::JumpTarget::Label(_) => {}
                crate::model::JumpTarget::Indirect(_) => {
                    out.unconditional = true;
                    out.indirect = true;
                }
                crate::model::JumpTarget::Direct { .. } => out.unconditional = true,
            },
            Stmt::CondGoto { target, .. } => match target {
                crate::model::JumpTarget::Label(_) => {}
                crate::model::JumpTarget::Indirect(_) => {
                    out.conditional = true;
                    out.indirect = true;
                }
                crate::model::JumpTarget::Direct { .. } => out.conditional = true,
            },
            Stmt::Call(t) => {
                out.call = true;
                if matches!(t, crate::model::JumpTarget::Indirect(_)) {
                    out.indirect = true;
                }
            }
            Stmt::Return(_) => {
                out.ret = true;
                out.unconditional = true;
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const TOY: &str = r#"
define endian=little;
define space ram type=ram_space size=4 default;
define space register type=register_space size=4;
define register offset=0 size=4 [ r0 r1 r2 r3 ];
define token instr(16)
    op = (12,15)
    rd = (8,11)
    rs = (4,7)
    imm8 = (0,7)
    simm8 = (0,7) signed
;
attach variables [ rd rs ] [ r0 r1 r2 r3 ];

:add rd,rs is op=0 & rd & rs { rd = rd + rs; }
:mov rd,imm8 is op=1 & rd & imm8 { rd = imm8; }
:neg rd is op=2 & rd & rs=0 { rd = -rd; }
:br simm8 is op=3 & simm8 { goto inst_start; }
"#;

    fn spec() -> Spec {
        crate::parse_str(TOY).expect("the toy specification parses")
    }

    #[test]
    fn a_fixed_width_instruction_decodes_and_renders() {
        let s = spec();
        let mut d = Decoder::new(&s);
        // op=0 rd=1 rs=2  ->  0x0120, little endian.
        let (insn, text) = d.disassemble(&[0x20, 0x01], 0x1000).expect("decodes");
        assert_eq!(insn.len, 2);
        assert_eq!(text, "add r1,r2");
        assert_eq!(insn.mnemonic(&s), Some("add"));
    }

    #[test]
    fn an_immediate_renders_in_the_fields_base() {
        let s = spec();
        let mut d = Decoder::new(&s);
        let (_, text) = d.disassemble(&[0x2a, 0x13], 0x1000).expect("decodes");
        assert_eq!(text, "mov r3,0x2a");
    }

    #[test]
    fn constructors_are_tried_in_order_so_the_narrower_pattern_wins() {
        let s = spec();
        let mut d = Decoder::new(&s);
        // op=2 rd=1 rs=0 matches `neg`, which is declared before nothing else
        // that could take it.
        let (_, text) = d.disassemble(&[0x00, 0x21], 0x1000).expect("decodes");
        assert_eq!(text, "neg r1");
        // rs=1 fails the rs=0 constraint and nothing else takes op=2.
        assert_eq!(
            d.decode(&[0x10, 0x21], 0x1000).unwrap_err(),
            DecodeError::NoMatch
        );
    }

    #[test]
    fn a_signed_field_prints_signed() {
        let s = spec();
        let mut d = Decoder::new(&s);
        let (_, text) = d.disassemble(&[0xff, 0x30], 0x1000).expect("decodes");
        assert_eq!(text, "br -0x1");
    }

    #[test]
    fn a_short_slice_does_not_match_rather_than_panicking() {
        let s = spec();
        let mut d = Decoder::new(&s);
        assert_eq!(d.decode(&[0x20], 0x1000).unwrap_err(), DecodeError::NoMatch);
        assert_eq!(d.decode(&[], 0x1000).unwrap_err(), DecodeError::NoMatch);
    }

    #[test]
    fn an_attach_hole_makes_the_encoding_invalid() {
        let s = crate::parse_str(
            r#"
define endian=little;
define space ram type=ram_space size=4 default;
define space register type=register_space size=4;
define register offset=0 size=4 [ r0 r1 ];
define token instr(8) op=(6,7) rd=(0,1);
attach variables [ rd ] [ r0 r1 _ _ ];
:x rd is op=0 & rd { }
"#,
        )
        .expect("parses");
        let mut d = Decoder::new(&s);
        assert!(d.decode(&[0x01], 0).is_ok(), "rd=1 is r1");
        assert_eq!(
            d.decode(&[0x02], 0).unwrap_err(),
            DecodeError::NoMatch,
            "rd=2 is a hole in the attach list, so the encoding is not this one"
        );
    }

    #[test]
    fn flow_comes_off_the_semantic_body() {
        let s = spec();
        let mut d = Decoder::new(&s);
        let br = d.decode(&[0x00, 0x30], 0x1000).expect("decodes");
        assert!(br.flow(&s).unconditional);
        assert!(!br.flow(&s).falls_through());
        let add = d.decode(&[0x20, 0x01], 0x1000).expect("decodes");
        assert!(add.flow(&s).falls_through());
    }

    #[test]
    fn a_subtable_is_recursed_into_and_rendered_in_place() {
        let s = crate::parse_str(
            r#"
define endian=little;
define space ram type=ram_space size=4 default;
define space register type=register_space size=4;
define register offset=0 size=4 [ r0 r1 r2 r3 ];
define token instr(16) op=(12,15) mode=(10,11) rd=(8,9) imm=(0,7);
attach variables [ rd ] [ r0 r1 r2 r3 ];
Addr: rd is mode=0 & rd { export rd; }
Addr: imm is mode=1 & imm { local t:4 = imm; export t; }
:ld rd,Addr is op=7 & rd & Addr { rd = Addr; }
"#,
        )
        .expect("parses");
        let mut d = Decoder::new(&s);
        // op=7 mode=0 rd=1, so the subtable prints a register.
        let (_, text) = d.disassemble(&[0x00, 0x71], 0x100).expect("decodes");
        assert_eq!(text, "ld r1,r1");
        // op=7 mode=1 rd=2 imm=0x5a, so it prints the immediate.
        let (_, text) = d.disassemble(&[0x5a, 0x76], 0x100).expect("decodes");
        assert_eq!(text, "ld r2,0x5a");
    }

    #[test]
    fn a_disassembly_action_computes_a_branch_target() {
        let s = crate::parse_str(
            r#"
define endian=little;
define space ram type=ram_space size=4 default;
define space register type=register_space size=4;
define register offset=0 size=4 [ r0 ];
define token instr(16) op=(8,15) rel=(0,7) signed;
target: dest is rel [ dest = inst_next + rel * 2; ] { export *:4 dest; }
:jmp target is op=0x20 & target { goto target; }
"#,
        )
        .expect("parses");
        let mut d = Decoder::new(&s);
        // rel = 4, so the target is 0x1000 + 2 + 8.
        let (_, text) = d.disassemble(&[0x04, 0x20], 0x1000).expect("decodes");
        assert_eq!(text, "jmp 0x100a");
    }
}
