//! Turning a constructor's `is` expression into bits.
//!
//! The bit pattern section is a boolean expression over field constraints, and
//! a decoder wants a mask and a value it can compare bytes against. This
//! module does that reduction: it walks the expression bottom up, keeping a
//! list of conjunctive alternatives, and hands back a disjunction of
//! (mask, value) pairs over the instruction stream and over the context
//! register, plus the byte offset each operand's token sits at.
//!
//! Four things cannot be reduced to a fixed mask, and all four are reported
//! rather than guessed at:
//!
//! * a constraint that is not `field = constant`, which stays as a residual
//!   expression for the decoder to evaluate once the masks pass;
//! * bits written after a `;` that follows a subtable of varying width, whose
//!   place in the stream depends on which constructor of that subtable
//!   matched. The bits are dropped from the mask, so the mask stays a test
//!   everything the constructor matches still passes, and the operands after
//!   the subtable are given offsets measured from the end of it instead;
//! * a `...` on the left of an expression, which right justifies it at a
//!   length that is not known until the whole instruction is parsed;
//! * a disjunction that blows past the alternative budget, which collapses to
//!   the bits every alternative agrees on.
//!
//! The last three set [`ResolvedPattern::approximation`], which tells the
//! decoder the masks are a filter and the real test is
//! [`Constructor::pattern`].
//!
//! The direction of the approximation is the one that matters: a mask never
//! rejects an encoding the constructor would have matched. It only lets
//! through more than it should, which the caller resolves by evaluating the
//! pattern as written.
//!
//! Reference: the SLEIGH manual, "7.4. The Bit Pattern Section" and "7.4.3.
//! The '...' Operator".
//!
//! [`Constructor::pattern`]: crate::model::Constructor::pattern

use crate::error::Limits;
use crate::model::{
    Approximation, ConstraintOp, ContextField, DisasmExpr, Field, MaskValue, Offset, OperandSource,
    PatternAlt, PatternExpr, ResolvedPattern, SymbolRef, TokenDef,
};

/// What the reducer needs to know about the specification. Kept as a trait
/// object's worth of small queries so the reducer can run while the parser is
/// still building the arenas.
pub(crate) struct Context<'a> {
    /// Every token.
    pub tokens: &'a [TokenDef],
    /// Every token field.
    pub fields: &'a [Field],
    /// Every context field.
    pub context_fields: &'a [ContextField],
    /// The context register's size in bytes, zero when there is none.
    pub context_bytes: usize,
    /// What each operand of the constructor is bound to.
    pub operands: &'a [OperandSource],
    /// The shortest length of each table, by table index.
    pub table_min: &'a [usize],
    /// The longest, by table index, clamped to the byte ceiling.
    pub table_max: &'a [usize],
    /// Whether each table is fixed width, by table index. A subtable that is
    /// not fixed width leaves anything after a `;` at an unknown offset.
    pub table_fixed: &'a [bool],
    /// The bounds.
    pub limits: &'a Limits,
}

/// One conjunctive alternative, while it is being built.
#[derive(Clone, Default)]
struct Alt {
    instr: MaskValue,
    context: MaskValue,
    length: usize,
    /// The most bytes this part can reach, which is what says whether an end
    /// anchored to a subtable is really later than one at a fixed offset.
    max: usize,
    /// False when `length` is a lower bound rather than the real length, which
    /// is what a subtable operand produces.
    exact: bool,
    /// Where this part of the pattern ends, which is where anything after a
    /// `;` begins.
    end: Offset,
    residual: Vec<PatternExpr>,
    offsets: Vec<(u16, Offset)>,
}

impl Alt {
    fn empty() -> Alt {
        Alt {
            exact: true,
            ..Alt::default()
        }
    }

    /// Whether the bytes this part covers sit at offsets known here, which is
    /// what lets a following pattern's mask be placed at all.
    fn placeable(&self) -> bool {
        self.end.is_absolute() && self.exact
    }
}

/// The result of reducing one constructor's pattern.
pub(crate) struct Reduction {
    /// The byte tests.
    pub resolved: ResolvedPattern,
    /// Where each operand's token begins, by operand index. `None` when no
    /// alternative placed it.
    pub offsets: Vec<Option<Offset>>,
}

/// Reduce `expr` for a constructor with `ctx.operands` operands.
pub(crate) fn reduce(expr: &PatternExpr, ctx: &Context<'_>) -> Reduction {
    let mut r = Reducer {
        ctx,
        approximation: None,
    };
    let alts = r.walk(expr);
    let approximation = r.approximation;

    // The first offer for an operand wins the summary slot. Alternatives that
    // place the same operand differently are why `PatternAlt::offsets` exists.
    let mut offsets = vec![None; ctx.operands.len()];
    for alt in &alts {
        for &(operand, at) in &alt.offsets {
            let slot = &mut offsets[operand as usize];
            if slot.is_none() {
                *slot = Some(at);
            }
        }
    }

    let width = ctx.operands.len();
    let alternatives = alts
        .into_iter()
        .map(|a| {
            let mut per_alt = vec![Offset::default(); width];
            for &(operand, at) in &a.offsets {
                if let Some(slot) = per_alt.get_mut(operand as usize) {
                    *slot = at;
                }
            }
            PatternAlt {
                instr: a.instr,
                context: a.context,
                length: a.length,
                residual: a.residual,
                offsets: per_alt,
            }
        })
        .collect();

    Reduction {
        resolved: ResolvedPattern {
            alternatives,
            approximation,
        },
        offsets,
    }
}

struct Reducer<'a> {
    ctx: &'a Context<'a>,
    approximation: Option<Approximation>,
}

impl Reducer<'_> {
    /// The first reason recorded is kept: they are all the same instruction to
    /// the caller, which is to fall back on the pattern as written.
    fn give_up(&mut self, why: Approximation) {
        self.approximation.get_or_insert(why);
    }

    fn walk(&mut self, expr: &PatternExpr) -> Vec<Alt> {
        match expr {
            PatternExpr::And(a, b) => {
                let (left, right) = (self.walk(a), self.walk(b));
                self.budget(conjoin(&left, &right))
            }
            PatternExpr::Or(a, b) => {
                let (mut left, right) = (self.walk(a), self.walk(b));
                left.extend(right);
                self.budget(left)
            }
            PatternExpr::Cat(a, b) => {
                let (left, right) = (self.walk(a), self.walk(b));
                if left.iter().any(|a| !a.placeable()) {
                    // The left side ends where only the decoder knows, so the
                    // right side's bits cannot go into an absolute mask. Its
                    // operands are still placed, relative to the subtable that
                    // ended the left side.
                    self.give_up(Approximation::UnknownTokenOffset);
                }
                let cap = self.ctx.limits.pattern_bytes;
                self.budget(concat(&left, &right, cap))
            }
            // Left justified: the bits stay where they are and the length
            // grows to meet whatever the pattern is combined with, which the
            // conjunction already does by taking the larger side.
            PatternExpr::EllipsisRight(a) => self.walk(a),
            PatternExpr::EllipsisLeft(a) => {
                // Right justification puts the bits at an offset that depends
                // on the final instruction length. Nothing here can place it.
                self.give_up(Approximation::RightJustified);
                let mut alts = self.walk(a);
                for alt in &mut alts {
                    alt.exact = false;
                    alt.instr = MaskValue::default();
                    alt.offsets.clear();
                    alt.end = Offset::absolute(alt.length);
                }
                alts
            }
            PatternExpr::Epsilon => vec![Alt::empty()],
            PatternExpr::Symbol(sym) => vec![self.symbol(*sym, expr)],
            PatternExpr::Constraint { lhs, op, rhs } => self.constraint(*lhs, *op, rhs, expr),
        }
    }

    /// A bare symbol constrains nothing but does commit the bits it covers.
    fn symbol(&mut self, sym: SymbolRef, expr: &PatternExpr) -> Alt {
        let mut alt = Alt::empty();
        match self.resolve(sym) {
            Bound::Field(id) => {
                let field = &self.ctx.fields[id];
                alt.length = self.ctx.tokens[field.token.index()].size as usize;
                alt.max = alt.length;
                alt.end = Offset::absolute(alt.length);
            }
            Bound::Context(_) | Bound::Nothing => {}
            Bound::Subtable(id) => {
                // A subtable of fixed width contributes a known number of
                // bytes; one whose constructors differ in length leaves the
                // total a lower bound, and whatever follows is measured from
                // the end of this operand rather than from byte zero.
                alt.length = self.ctx.table_min.get(id).copied().unwrap_or(0);
                alt.max = self.ctx.table_max.get(id).copied().unwrap_or(0);
                alt.exact = self.ctx.table_fixed.get(id).copied().unwrap_or(false);
                alt.end = match (alt.exact, sym) {
                    (true, _) => Offset::absolute(alt.length),
                    (false, SymbolRef::Operand(i)) => Offset {
                        base: Some(i),
                        delta: 0,
                    },
                    (false, _) => Offset::absolute(alt.length),
                };
            }
        }
        if let SymbolRef::Operand(i) = sym {
            alt.offsets.push((i, Offset::default()));
        }
        if matches!(self.resolve(sym), Bound::Nothing) && !matches!(sym, SymbolRef::Operand(_)) {
            alt.residual.push(expr.clone());
        }
        alt
    }

    fn constraint(
        &mut self,
        lhs: SymbolRef,
        op: ConstraintOp,
        rhs: &DisasmExpr,
        expr: &PatternExpr,
    ) -> Vec<Alt> {
        let mut alt = Alt::empty();
        if let SymbolRef::Operand(i) = lhs {
            alt.offsets.push((i, Offset::default()));
        }
        let constant = match rhs {
            DisasmExpr::Num(v) => Some(*v),
            _ => None,
        };

        match self.resolve(lhs) {
            Bound::Field(id) => {
                let field = &self.ctx.fields[id];
                let token = &self.ctx.tokens[field.token.index()];
                alt.length = token.size as usize;
                alt.max = alt.length;
                alt.end = Offset::absolute(alt.length);
                if alt.length > self.ctx.limits.pattern_bytes {
                    self.give_up(Approximation::UnknownTokenOffset);
                    return vec![alt];
                }
                match (op, constant.and_then(|v| encode(field, v))) {
                    (ConstraintOp::Equal, Some(bits)) => {
                        if !place_field(&mut alt.instr, field, token, bits) {
                            return Vec::new();
                        }
                    }
                    _ => alt.residual.push(expr.clone()),
                }
            }
            Bound::Context(id) => {
                let field = &self.ctx.context_fields[id];
                match (op, constant) {
                    (ConstraintOp::Equal, Some(v)) if fits(v, field.bits(), field.signed) => {
                        let bits = mask_of(field.bits()) & v as u64;
                        if !place_context(&mut alt.context, field, bits, self.ctx.context_bytes) {
                            return Vec::new();
                        }
                    }
                    _ => alt.residual.push(expr.clone()),
                }
            }
            Bound::Subtable(id) => {
                alt.length = self.ctx.table_min.get(id).copied().unwrap_or(0);
                alt.max = self.ctx.table_max.get(id).copied().unwrap_or(0);
                alt.exact = self.ctx.table_fixed.get(id).copied().unwrap_or(false);
                alt.end = match (alt.exact, lhs) {
                    (true, _) => Offset::absolute(alt.length),
                    (false, SymbolRef::Operand(i)) => Offset {
                        base: Some(i),
                        delta: 0,
                    },
                    (false, _) => Offset::absolute(alt.length),
                };
                alt.residual.push(expr.clone());
            }
            Bound::Nothing => alt.residual.push(expr.clone()),
        }
        vec![alt]
    }

    fn resolve(&self, sym: SymbolRef) -> Bound {
        match sym {
            SymbolRef::Field(id) => Bound::Field(id.index()),
            SymbolRef::Context(id) => Bound::Context(id.index()),
            SymbolRef::Table(id) => Bound::Subtable(id.index()),
            SymbolRef::Operand(i) => match self.ctx.operands.get(i as usize) {
                Some(OperandSource::Field(id)) => Bound::Field(id.index()),
                Some(OperandSource::Context(id)) => Bound::Context(id.index()),
                Some(OperandSource::Table(id)) => Bound::Subtable(id.index()),
                _ => Bound::Nothing,
            },
            _ => Bound::Nothing,
        }
    }

    /// Keep the alternative list under its ceiling, collapsing to the bits
    /// every alternative agrees on rather than dropping any of them, so the
    /// result stays a superset of what the pattern matches.
    fn budget(&mut self, alts: Vec<Alt>) -> Vec<Alt> {
        if alts.len() <= self.ctx.limits.pattern_alternatives {
            return alts;
        }
        self.give_up(Approximation::TooManyAlternatives);
        let mut iter = alts.into_iter();
        let Some(first) = iter.next() else {
            return Vec::new();
        };
        let mut merged = Alt {
            instr: first.instr,
            context: first.context,
            length: first.length,
            max: first.max,
            exact: false,
            end: first.end,
            residual: Vec::new(),
            offsets: first.offsets,
        };
        for alt in iter {
            merged.instr = merged.instr.intersect(&alt.instr);
            merged.context = merged.context.intersect(&alt.context);
            merged.length = merged.length.min(alt.length);
            merged.max = merged.max.max(alt.max);
            if merged.end != alt.end {
                // The collapsed alternatives end in different places, so
                // nothing after them can be placed from here.
                merged.end = Offset::absolute(merged.length);
            }
        }
        vec![merged]
    }
}

enum Bound {
    Field(usize),
    Context(usize),
    Subtable(usize),
    Nothing,
}

fn conjoin(left: &[Alt], right: &[Alt]) -> Vec<Alt> {
    let mut out = Vec::with_capacity(left.len().saturating_mul(right.len()).min(1 << 16));
    for a in left {
        for b in right {
            let mut instr = a.instr.clone();
            if !instr.merge(&b.instr) {
                continue;
            }
            let mut context = a.context.clone();
            if !context.merge(&b.context) {
                continue;
            }
            // An ellipsis extends its side's token length to whatever the
            // combination turns out to be, so the width of a conjunction is
            // the larger of the two sides whether or not one is elided. The
            // SLEIGH manual, "The '...' Operator".
            let length = a.length.max(b.length);
            let max = a.max.max(b.max);
            let exact = a.exact && b.exact;
            let end = later_of(a, b, length);
            let mut residual = a.residual.clone();
            residual.extend(b.residual.iter().cloned());
            let mut offsets = a.offsets.clone();
            offsets.extend(b.offsets.iter().copied());
            out.push(Alt {
                instr,
                context,
                length,
                max,
                exact,
                end,
                residual,
                offsets,
            });
        }
    }
    out
}

/// Which of two ends a conjunction finishes at.
///
/// Two offsets measured from the same base compare directly. Measured from
/// different ones they do not, so the one anchored to a subtable wins, unless
/// the fixed one is already at or past everything that subtable could reach:
/// x86 has helper subtables of nought or one byte sitting in a conjunction
/// that has already consumed that byte, and anchoring to those would make a
/// following immediate look unplaceable when it is not.
fn later_of(a: &Alt, b: &Alt, length: usize) -> Offset {
    match (a.end.base, b.end.base) {
        _ if a.end.base == b.end.base => Offset {
            base: a.end.base,
            delta: a.end.delta.max(b.end.delta),
        },
        (Some(_), None) if b.end.delta >= a.max => b.end,
        (None, Some(_)) if a.end.delta >= b.max => a.end,
        (Some(_), None) => a.end,
        (None, Some(_)) => b.end,
        _ => Offset::absolute(length),
    }
}

fn concat(left: &[Alt], right: &[Alt], cap: usize) -> Vec<Alt> {
    let mut out = Vec::with_capacity(left.len().saturating_mul(right.len()).min(1 << 16));
    for a in left {
        for b in right {
            let mut instr = a.instr.clone();
            // Placing the right side's bits at `a.end.delta` is only sound
            // when the left side really ends there. When it does not, the bits
            // are dropped rather than guessed at: the masks stay a filter that
            // everything the constructor matches still passes, and the caller
            // has been told the pattern is approximate.
            if a.placeable() && a.end.delta <= cap {
                if !instr.merge(&b.instr.shifted(a.end.delta)) {
                    continue;
                }
            } else if !b.instr.is_empty() {
                out.push(Alt {
                    instr,
                    context: {
                        let mut context = a.context.clone();
                        if !context.merge(&b.context) {
                            continue;
                        }
                        context
                    },
                    length: a.length.saturating_add(b.length).min(cap),
                    max: a.max.saturating_add(b.max).min(cap),
                    exact: false,
                    end: shift_end(a.end, b.end),
                    residual: join(&a.residual, &b.residual),
                    offsets: shift_offsets(a, b),
                });
                continue;
            }
            let mut context = a.context.clone();
            if !context.merge(&b.context) {
                continue;
            }
            out.push(Alt {
                instr,
                context,
                length: a.length.saturating_add(b.length).min(cap),
                max: a.max.saturating_add(b.max).min(cap),
                exact: a.exact && b.exact,
                end: shift_end(a.end, b.end),
                residual: join(&a.residual, &b.residual),
                offsets: shift_offsets(a, b),
            });
        }
    }
    out
}

fn join(a: &[PatternExpr], b: &[PatternExpr]) -> Vec<PatternExpr> {
    let mut out = a.to_vec();
    out.extend(b.iter().cloned());
    out
}

/// Where the right side's operands land once the left side is in front of
/// them. An offset already anchored to a subtable stays where it is.
fn shift_offsets(a: &Alt, b: &Alt) -> Vec<(u16, Offset)> {
    let mut offsets = a.offsets.clone();
    offsets.extend(b.offsets.iter().map(|&(i, at)| (i, rebase(a.end, at))));
    offsets
}

fn shift_end(a: Offset, b: Offset) -> Offset {
    rebase(a, b)
}

fn rebase(base: Offset, at: Offset) -> Offset {
    match at.base {
        None => Offset {
            base: base.base,
            delta: base.delta.saturating_add(at.delta),
        },
        Some(_) => at,
    }
}

/// Set a field's bits in an instruction mask. False when they contradict what
/// is already there.
fn place_field(mv: &mut MaskValue, field: &Field, token: &TokenDef, value: u64) -> bool {
    let mut bytes: Vec<(usize, u8, u8)> = Vec::new();
    for (i, bit) in (field.low..=field.high).enumerate() {
        let Some((byte, offset)) = Field::bit_position(token, bit) else {
            return false;
        };
        let set = (value >> i) & 1 == 1;
        bytes.push((byte, 1 << offset, if set { 1 << offset } else { 0 }));
    }
    for (byte, mask, value) in bytes {
        if !mv.constrain(byte, mask, value) {
            return false;
        }
    }
    true
}

/// The same for a context field, whose bits are numbered from the register's
/// most significant end.
fn place_context(mv: &mut MaskValue, field: &ContextField, value: u64, bytes: usize) -> bool {
    for (i, bit) in (field.low..=field.high).rev().enumerate() {
        let (byte, offset) = ContextField::bit_position(bit);
        if bytes != 0 && byte >= bytes {
            return false;
        }
        let set = (value >> i) & 1 == 1;
        if !mv.constrain(byte, 1 << offset, if set { 1 << offset } else { 0 }) {
            return false;
        }
    }
    true
}

/// The bit pattern a constraint value takes in a field, or `None` when it does
/// not fit and the constraint therefore is not a plain mask test.
fn encode(field: &Field, value: i64) -> Option<u64> {
    if !fits(value, field.bits(), field.signed) {
        return None;
    }
    Some(value as u64 & mask_of(field.bits()))
}

fn fits(value: i64, bits: u32, signed: bool) -> bool {
    if bits >= 64 {
        return true;
    }
    if value < 0 || signed {
        let limit = 1i64 << (bits - 1);
        return value >= -limit && value < limit;
    }
    (value as u64) <= mask_of(bits)
}

fn mask_of(bits: u32) -> u64 {
    if bits >= 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    }
}

/// The order a decoder has to resolve a constructor's operands in.
///
/// Stream order, which is the pattern's own left to right order: the left of
/// a `;` is matched before the right, and an operand placed relative to a
/// variable width subtable is placed relative to one that was matched
/// earlier. Operands the pattern never mentions, which the disassembly action
/// section computes, come last in index order; nothing is measured from them.
///
/// The walk is iterative because the tree leans one level per term of a flat
/// `&` or `|` chain.
pub(crate) fn operand_order(expr: &PatternExpr, count: usize) -> Vec<u16> {
    let mut seen = vec![false; count];
    let mut order: Vec<u16> = Vec::with_capacity(count);
    let mut stack: Vec<&PatternExpr> = vec![expr];
    // Bounded by the nodes actually in the tree, which the parser's nesting
    // and chain limits already cap.
    while let Some(node) = stack.pop() {
        match node {
            PatternExpr::And(a, b) | PatternExpr::Or(a, b) | PatternExpr::Cat(a, b) => {
                stack.push(b);
                stack.push(a);
            }
            PatternExpr::EllipsisLeft(a) | PatternExpr::EllipsisRight(a) => stack.push(a),
            PatternExpr::Symbol(SymbolRef::Operand(i))
            | PatternExpr::Constraint {
                lhs: SymbolRef::Operand(i),
                ..
            } => {
                let at = *i as usize;
                if seen.get(at) == Some(&false) {
                    seen[at] = true;
                    order.push(*i);
                }
            }
            _ => {}
        }
    }
    for (i, done) in seen.iter().enumerate() {
        if !done {
            order.push(i as u16);
        }
    }
    order
}

/// The instruction bytes a pattern consumes, as a range, without reducing it
/// to masks.
///
/// This is the cheap half of the length fixpoint: table lengths depend on
/// their constructors' lengths, which depend on the lengths of the tables they
/// use, so the caller iterates this until nothing moves. An ellipsis does not
/// appear here, because it only extends its side to the length of what it is
/// combined with, and a conjunction already takes the larger of the two.
pub(crate) fn length_of(
    expr: &PatternExpr,
    operands: &[OperandSource],
    tokens: &[TokenDef],
    fields: &[Field],
    table_len: &[(usize, usize)],
    cap: usize,
) -> (usize, usize) {
    let clamp = |(a, b): (usize, usize)| (a.min(cap), b.min(cap));
    let leaf = |sym: &SymbolRef| -> (usize, usize) {
        let source = match sym {
            SymbolRef::Field(id) => Some(OperandSource::Field(*id)),
            SymbolRef::Table(id) => Some(OperandSource::Table(*id)),
            SymbolRef::Operand(i) => operands.get(*i as usize).copied(),
            _ => None,
        };
        match source {
            Some(OperandSource::Field(id)) => {
                let size = tokens[fields[id.index()].token.index()].size as usize;
                (size, size)
            }
            Some(OperandSource::Table(id)) => table_len.get(id.index()).copied().unwrap_or((0, 0)),
            _ => (0, 0),
        }
    };
    match expr {
        PatternExpr::Epsilon => (0, 0),
        PatternExpr::Symbol(sym) => clamp(leaf(sym)),
        PatternExpr::Constraint { lhs, .. } => clamp(leaf(lhs)),
        PatternExpr::EllipsisLeft(inner) | PatternExpr::EllipsisRight(inner) => {
            length_of(inner, operands, tokens, fields, table_len, cap)
        }
        PatternExpr::And(a, b) => {
            let left = length_of(a, operands, tokens, fields, table_len, cap);
            let right = length_of(b, operands, tokens, fields, table_len, cap);
            (left.0.max(right.0), left.1.max(right.1))
        }
        PatternExpr::Or(a, b) => {
            let left = length_of(a, operands, tokens, fields, table_len, cap);
            let right = length_of(b, operands, tokens, fields, table_len, cap);
            (left.0.min(right.0), left.1.max(right.1))
        }
        PatternExpr::Cat(a, b) => {
            let left = length_of(a, operands, tokens, fields, table_len, cap);
            let right = length_of(b, operands, tokens, fields, table_len, cap);
            clamp((
                left.0.saturating_add(right.0),
                left.1.saturating_add(right.1),
            ))
        }
    }
}
