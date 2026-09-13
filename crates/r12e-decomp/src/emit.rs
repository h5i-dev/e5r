//! Rendering a structured function as pseudo-C.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use r12e_core::Addr;
use r12e_ir::op::{Op, Space};
use r12e_ir::ssa::{Operand, SsaFunction, SsaKind, SsaOp, Value};

use crate::expr::{Expr, Rebuilder, c_type, input_name};
use crate::structure::{Graph, Region, Taken, structure};

/// A decompiled function.
#[derive(Debug, Clone)]
pub struct Output {
    /// The C text.
    pub text: String,
    /// Declarations the text needs to compile: the functions it calls and the
    /// helpers for operations C has no operator for.
    pub declarations: Vec<String>,
    /// Gotos the structuring needed; lower is better.
    pub gotos: usize,
    /// Named locals declared.
    pub locals: usize,
    /// Operations no expression covered.
    pub unmodelled: usize,
}

/// Decompile an SSA function to pseudo-C.
pub fn decompile(name: &str, f: &SsaFunction) -> Output {
    let graph: Graph = f
        .blocks
        .iter()
        .map(|(a, b)| (*a, b.successors.clone()))
        .collect();
    // Where each conditional branch goes when it is taken, read off the
    // branch rather than guessed from the order of the successors.
    let taken: Taken = f
        .blocks
        .iter()
        .filter_map(|(a, b)| {
            let op = b
                .ops
                .iter()
                .rev()
                .find(|op| op.kind == SsaKind::Op(Op::CBranch))?;
            let target = op.inputs.first()?.as_const()?;
            Some((*a, Addr(target)))
        })
        .collect();
    let s = structure(f.entry, &graph, &taken);
    let rebuilder = Rebuilder::new(f);

    let result = result_register(f, &rebuilder);
    let mut e = Emitter {
        f,
        r: &rebuilder,
        labels: &s.labels,
        result,
        unmodelled: 0,
    };

    let body = {
        let mut out = String::new();
        e.region(&mut out, &s.root, 1);
        out
    };

    // Values that arrive from outside and are not arguments: registers the
    // function inherited. Declaring them says where they came from without
    // pretending they are parameters.
    // Keyed by name: the same location read at two widths must be declared
    // once, not twice with different types.
    let mut inherited: BTreeMap<String, String> = BTreeMap::new();
    let mut called: BTreeSet<u64> = BTreeSet::new();
    let mut helpers: BTreeSet<&'static str> = BTreeSet::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            for i in &op.inputs {
                if let r12e_ir::ssa::Operand::Undefined(l) = i {
                    let name = crate::expr::input_name(*l, &rebuilder.abi);
                    if !name.starts_with("arg") && !name.starts_with("farg") {
                        let ty = if rebuilder.floats.contains(l) {
                            crate::expr::float_type(l.size)
                        } else {
                            c_type(l.size)
                        };
                        inherited.entry(name).or_insert_with(|| ty.to_string());
                    }
                }
            }
            if op.kind == SsaKind::Op(Op::Call) {
                if let Some(target) = op.inputs.first().and_then(|i| i.as_const()) {
                    called.insert(target);
                }
            }
            if let SsaKind::Op(o) = op.kind {
                if let Some(h) = helper_for(o) {
                    helpers.insert(h);
                }
            }
        }
    }

    let mut declarations: Vec<String> = helpers.iter().map(|h| h.to_string()).collect();
    declarations.extend(
        called
            .iter()
            // No parameter list: what a called function takes is what
            // prototype recovery is for, and guessing four would be a claim.
            .map(|a| format!("uint64_t sub_{a:x}();")),
    );

    let mut text = String::new();
    let _ = writeln!(
        text,
        "{} {}({})",
        return_type(result, &rebuilder),
        name,
        parameters(f, &rebuilder)
    );
    text.push_str("{\n");
    // Only the ones the body actually mentions: an inherited flag that every
    // pass removed should not be declared.
    let inherited: Vec<(&String, &String)> = inherited
        .iter()
        .filter(|(name, _)| mentions(&body, name))
        .collect();
    for (name, ty) in &inherited {
        let _ = writeln!(text, "    {ty} {name};  // inherited");
    }
    for (value, local) in &rebuilder.locals {
        let ty = if rebuilder.floats.contains(&value.location) {
            crate::expr::float_type(value.location.size)
        } else {
            c_type(value.location.size)
        };
        let _ = writeln!(text, "    {ty} {local};");
    }
    if !rebuilder.locals.is_empty() || !inherited.is_empty() {
        text.push('\n');
    }
    text.push_str(&body);
    text.push_str("}\n");

    Output {
        text,
        declarations,
        gotos: s.gotos,
        locals: rebuilder.locals.len(),
        unmodelled: e.unmodelled,
    }
}

/// Declarations every unit needs: the reinterpretations between a value's bits
/// and the number they stand for, which the machine does for free and C does
/// not.
const REINTERPRET: &str = "\
static inline uint64_t __bits(double v){union{double d;uint64_t u;}x;x.d=v;return x.u;}
static inline double __dbl(uint64_t v){union{double d;uint64_t u;}x;x.u=v;return x.d;}";

/// True when a name appears in the text as a whole word.
fn mentions(text: &str, name: &str) -> bool {
    let mut at = 0;
    while let Some(found) = text[at..].find(name) {
        let start = at + found;
        let end = start + name.len();
        let before = text[..start].chars().next_back();
        let after = text[end..].chars().next();
        let word = |c: Option<char>| c.is_some_and(|c| c.is_alphanumeric() || c == '_');
        if !word(before) && !word(after) {
            return true;
        }
        at = end;
    }
    false
}

/// The declaration an operation's helper needs, when it has one.
fn helper_for(o: Op) -> Option<&'static str> {
    Some(match o {
        Op::FloatAdd
        | Op::FloatSub
        | Op::FloatMul
        | Op::FloatDiv
        | Op::FloatNeg
        | Op::FloatEqual
        | Op::FloatNotEqual
        | Op::FloatLess
        | Op::FloatLessEqual => REINTERPRET,
        Op::FloatAbs => "double __fabs(double);",
        Op::FloatSqrt => "double __sqrt(double);",
        Op::FloatMax => "double __fmax(double, double);",
        Op::FloatMin => "double __fmin(double, double);",
        Op::FloatNan => "int __isnan(double);",
        Op::FloatTrunc => "double __trunc(double);",
        Op::FloatRound => "double __rint(double);",
        Op::FloatCeil => "double __ceil(double);",
        Op::FloatFloor => "double __floor(double);",
        Op::FloatMulAdd => "double __fma(double, double, double);",
        Op::FloatConvert | Op::IntToFloat | Op::UIntToFloat | Op::FloatToInt | Op::FloatToUInt => {
            REINTERPRET
        }
        Op::CallInd => "uint64_t __callind(uint64_t);",
        Op::IntDiv128 => "uint64_t __udiv128(uint64_t, uint64_t, uint64_t);",
        Op::IntSDiv128 => "uint64_t __sdiv128(uint64_t, uint64_t, uint64_t);",
        Op::IntRem128 => "uint64_t __urem128(uint64_t, uint64_t, uint64_t);",
        Op::IntSRem128 => "uint64_t __srem128(uint64_t, uint64_t, uint64_t);",
        Op::IntMulHigh => "uint64_t __mulhi(uint64_t, uint64_t);",
        Op::IntSMulHigh => "uint64_t __smulhi(uint64_t, uint64_t);",
        Op::PopCount => "uint64_t __popcount(uint64_t);",
        Op::LzCount => "uint64_t __clz(uint64_t);",
        Op::IntCarry => "uint64_t __carry(uint64_t, uint64_t);",
        Op::IntSCarry => "uint64_t __overflow(uint64_t, uint64_t);",
        Op::IntSBorrow => "uint64_t __borrow(uint64_t, uint64_t);",
        Op::Unimplemented => "void __unmodelled(uint64_t);",
        _ => return None,
    })
}

/// Which register the function leaves its result in, if any.
///
/// The convention lists the candidates; which one this function writes says
/// whether it returns an integer, a floating point value, or nothing.
fn result_register(f: &SsaFunction, r: &Rebuilder) -> Option<u64> {
    // The one written latest before the return. A function that computes into
    // a general register and then converts into a vector one writes both, and
    // only the order says which the caller reads.
    let mut best: Option<(usize, u64)> = None;
    for b in f.blocks.values() {
        let returns = b
            .ops
            .iter()
            .any(|op| op.kind == SsaKind::Op(Op::Return));
        if !returns {
            continue;
        }
        for (n, op) in b.ops.iter().enumerate() {
            let Some(v) = op.out else { continue };
            if v.location.space != Space::Register || !r.abi.results.contains(&v.location.offset)
            {
                continue;
            }
            if best.map(|(at, _)| n > at).unwrap_or(true) {
                best = Some((n, v.location.offset));
            }
        }
    }
    if let Some((_, offset)) = best {
        return Some(offset);
    }
    // Nothing was written in the returning block, so whichever the function
    // writes at all is the answer.
    r.abi.results.iter().copied().find(|offset| {
        f.blocks.values().any(|b| {
            b.ops
                .iter()
                .any(|op| op.out.is_some_and(|v| v.location.offset == *offset))
        })
    })
}

/// The declared return type, from where the result was left.
fn return_type(result: Option<u64>, r: &Rebuilder) -> &'static str {
    match result {
        None => "void",
        Some(offset) if offset >= r.abi.vector_base => "double",
        Some(_) => "uint64_t",
    }
}

/// The parameters, taken from the argument registers read before being written.
fn parameters(f: &SsaFunction, r: &Rebuilder) -> String {
    // Ordered by where the convention puts them, not by name, so `arg10` does
    // not sort before `arg2`.
    let mut seen: BTreeMap<usize, String> = BTreeMap::new();
    let order: Vec<u64> = r
        .abi
        .integer_arguments
        .iter()
        .chain(r.abi.float_arguments.iter())
        .copied()
        .collect();
    for b in f.blocks.values() {
        for op in &b.ops {
            for i in &op.inputs {
                let Operand::Undefined(l) = i else { continue };
                let name = input_name(*l, &r.abi);
                let ty = if r.floats.contains(l) {
                    crate::expr::float_type(l.size)
                } else {
                    c_type(l.size)
                };
                // Register arguments come first, in the order the convention
                // uses them; then the ones the caller left on the stack, in
                // address order.
                if l.space == Space::Register {
                    if let Some(n) = order.iter().position(|o| *o == l.offset) {
                        seen.insert(n, format!("{ty} {name}"));
                    }
                } else if crate::expr::is_stack_argument(*l) {
                    seen.insert(order.len() + l.offset as usize, format!("{ty} {name}"));
                }
            }
        }
    }
    if seen.is_empty() {
        "void".to_string()
    } else {
        seen.into_values().collect::<Vec<_>>().join(", ")
    }
}

struct Emitter<'a> {
    f: &'a SsaFunction,
    r: &'a Rebuilder<'a>,
    labels: &'a BTreeSet<Addr>,
    /// Where the function leaves its result.
    result: Option<u64>,
    unmodelled: usize,
}

impl Emitter<'_> {
    fn region(&mut self, out: &mut String, region: &Region, depth: usize) {
        let pad = "    ".repeat(depth);
        match region {
            Region::Empty => {}
            Region::Seq(parts) => {
                for p in parts {
                    self.region(out, p, depth);
                }
            }
            Region::Block(at) => {
                if self.labels.contains(at) {
                    let _ = writeln!(out, "{}L{:x}:", "    ".repeat(depth.saturating_sub(1)), at.0);
                }
                self.statements(out, *at, depth);
            }
            Region::Goto(at) => {
                let _ = writeln!(out, "{pad}goto L{:x};", at.0);
            }
            Region::Break => {
                let _ = writeln!(out, "{pad}break;");
            }
            Region::Continue => {
                let _ = writeln!(out, "{pad}continue;");
            }
            Region::If {
                head,
                invert,
                then,
                otherwise,
            } => {
                let cond = self.condition(*head, *invert);
                let _ = writeln!(out, "{pad}if ({cond}) {{");
                self.region(out, then, depth + 1);
                match otherwise {
                    Some(o) if **o != Region::Empty => {
                        let _ = writeln!(out, "{pad}}} else {{");
                        self.region(out, o, depth + 1);
                        let _ = writeln!(out, "{pad}}}");
                    }
                    _ => {
                        let _ = writeln!(out, "{pad}}}");
                    }
                }
            }
            Region::While {
                head,
                invert,
                body,
            } => {
                if self.labels.contains(head) {
                    let _ = writeln!(out, "{}L{:x}:", "    ".repeat(depth.saturating_sub(1)), head.0);
                }
                // The head's own statements compute the condition, so they run
                // on every iteration: a `for (; cond; )` with them hoisted
                // would be wrong. Write the loop as `while (1)` with the test
                // at the top when the head does more than test.
                let cond = self.condition(*head, *invert);
                if self.head_is_only_a_test(*head) {
                    let _ = writeln!(out, "{pad}while ({cond}) {{");
                    self.region(out, body, depth + 1);
                    let _ = writeln!(out, "{pad}}}");
                } else {
                    let _ = writeln!(out, "{pad}while (1) {{");
                    self.statements(out, *head, depth + 1);
                    let _ = writeln!(out, "{pad}    if ({}) break;", negate(cond.clone()));
                    self.region(out, body, depth + 1);
                    let _ = writeln!(out, "{pad}}}");
                }
            }
            Region::Infinite { head, body } => {
                if self.labels.contains(head) {
                    let _ = writeln!(out, "{}L{:x}:", "    ".repeat(depth.saturating_sub(1)), head.0);
                }
                let _ = writeln!(out, "{pad}while (1) {{");
                self.statements(out, *head, depth + 1);
                self.region(out, body, depth + 1);
                let _ = writeln!(out, "{pad}}}");
            }
        }
    }

    /// True when a block's only job is to compute the branch condition, so the
    /// condition can move into a `while` header.
    fn head_is_only_a_test(&self, at: Addr) -> bool {
        let Some(b) = self.f.blocks.get(&at) else {
            return true;
        };
        !b.ops.iter().any(|op| self.is_statement(op))
    }

    /// The branch condition of a block, inverted if asked.
    fn condition(&mut self, at: Addr, invert: bool) -> Expr {
        let cond = self
            .f
            .blocks
            .get(&at)
            .and_then(|b| {
                b.ops
                    .iter()
                    .rev()
                    .find(|op| op.kind == SsaKind::Op(Op::CBranch))
            })
            .and_then(|op| op.inputs.get(1))
            .map(|i| self.r.operand(i));
        match cond {
            Some(e) if invert => negate(e),
            Some(e) => e,
            None => {
                self.unmodelled += 1;
                Expr::Unknown("condition")
            }
        }
    }

    /// The statements of one block, branches excluded.
    fn statements(&mut self, out: &mut String, at: Addr, depth: usize) {
        self.block_ops(out, at, depth);
        self.phi_copies(out, at, depth);
    }

    /// The assignments a block's successors' phis stand for.
    ///
    /// A phi is not an instruction; it says that a value came from one path or
    /// another. Leaving SSA means writing that down as an assignment at the end
    /// of each path, which is the only place it can be said in C.
    fn phi_copies(&mut self, out: &mut String, at: Addr, depth: usize) {
        let pad = "    ".repeat(depth);
        let Some(b) = self.f.blocks.get(&at) else {
            return;
        };
        for successor in &b.successors {
            let Some(s) = self.f.blocks.get(successor) else {
                continue;
            };
            let Some(slot) = s.predecessors.iter().position(|p| *p == at) else {
                continue;
            };
            for op in &s.ops {
                if op.kind != SsaKind::Phi {
                    continue;
                }
                let (Some(v), Some(input)) = (op.out, op.inputs.get(slot)) else {
                    continue;
                };
                let Some(name) = self.r.locals.get(&v) else {
                    continue;
                };
                // An assignment from itself says nothing.
                let value = self.r.operand(input);
                let text = format!("{value}");
                if text == *name {
                    continue;
                }
                let _ = writeln!(out, "{pad}{name} = {text};");
            }
        }
    }

    fn block_ops(&mut self, out: &mut String, at: Addr, depth: usize) {
        let pad = "    ".repeat(depth);
        let Some(b) = self.f.blocks.get(&at) else {
            return;
        };
        for op in &b.ops {
            if !self.is_statement(op) {
                continue;
            }
            let SsaKind::Op(o) = op.kind else { continue };
            match o {
                Op::Store => {
                    let addr = op.inputs.first().map(|i| self.r.operand(i));
                    let val = op.inputs.get(1).map(|i| self.r.operand(i));
                    if let (Some(a), Some(v)) = (addr, val) {
                        let _ = writeln!(
                            out,
                            "{pad}*({}*){} = {};",
                            c_type(op.size),
                            parenthesize(&a),
                            v
                        );
                    }
                }
                Op::Return => {
                    let value = self.result(at);
                    if value.is_empty() {
                        let _ = writeln!(out, "{pad}return;");
                    } else {
                        let _ = writeln!(out, "{pad}return {value};");
                    }
                }
                Op::Call | Op::CallInd => {
                    let e = self.r.expr(op);
                    match op.out.and_then(|v| self.r.locals.get(&v)) {
                        Some(name) => {
                            let _ = writeln!(out, "{pad}{name} = {e};");
                        }
                        None => {
                            let _ = writeln!(out, "{pad}{e};");
                        }
                    }
                }
                Op::Unimplemented => {
                    self.unmodelled += 1;
                    let _ = writeln!(out, "{pad}__unmodelled(0x{:x});", op.addr.0);
                }
                Op::BranchInd => {
                    if let Some(t) = op.inputs.first().map(|i| self.r.operand(i)) {
                        let _ = writeln!(out, "{pad}goto *{};", parenthesize(&t));
                    }
                }
                _ => {
                    // Anything else that reaches here has a named output.
                    if let Some(name) = op.out.and_then(|v| self.r.locals.get(&v)) {
                        let _ = writeln!(out, "{pad}{name} = {};", self.r.expr(op));
                    }
                }
            }
        }
    }

    /// True when an operation has to appear as a statement rather than being
    /// inlined into whatever reads it.
    fn is_statement(&self, op: &SsaOp) -> bool {
        let SsaKind::Op(o) = op.kind else {
            // A phi is a merge, written where the paths join, not here.
            return false;
        };
        match o {
            Op::Store | Op::Return | Op::Call | Op::CallInd | Op::Unimplemented | Op::BranchInd => {
                true
            }
            Op::Branch | Op::CBranch => false,
            // Everything else is an expression, needed as a statement only when
            // its result got a name.
            _ => op.out.is_some_and(|v| self.r.locals.contains_key(&v)),
        }
    }

    /// What a function returns: whatever last reached the result register.
    fn result(&self, at: Addr) -> String {
        let Some(offset) = self.result else {
            return String::new();
        };
        let in_block = self
            .f
            .blocks
            .get(&at)
            .and_then(|b| {
                b.ops
                    .iter()
                    .rev()
                    .filter_map(|op| op.out)
                    .find(|v| v.location.space == Space::Register && v.location.offset == offset)
            });
        // Nothing in this block wrote it, so the value came from wherever it
        // was last written: the newest version is the one that reaches here.
        let value = in_block.or_else(|| {
            self.f
                .blocks
                .values()
                .flat_map(|b| b.ops.iter())
                .filter_map(|op| op.out)
                .filter(|v| v.location.space == Space::Register && v.location.offset == offset)
                .max_by_key(|v| v.version)
        });
        match value {
            Some(v) => match self.r.locals.get(&v) {
                Some(name) => name.clone(),
                None => format!("{}", self.r.operand(&Operand::Value(v))),
            },
            None => "0".to_string(),
        }
    }
}

/// Negate a condition without stacking `!` on something already negated.
fn negate(e: Expr) -> Expr {
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

/// Wrap in parentheses unless it is already atomic.
fn parenthesize(e: &Expr) -> String {
    match e {
        Expr::Const(..) | Expr::Local(_) | Expr::Input(..) => format!("{e}"),
        _ => format!("({e})"),
    }
}

/// Values each block defines, for callers that want the mapping.
pub fn block_definitions(f: &SsaFunction) -> BTreeMap<Addr, Vec<Value>> {
    f.blocks
        .iter()
        .map(|(a, b)| (*a, b.ops.iter().filter_map(|op| op.out).collect()))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn negation_flips_comparisons_rather_than_wrapping_them() {
        let a = Box::new(Expr::Local("a".into()));
        let b = Box::new(Expr::Local("b".into()));
        assert_eq!(
            format!("{}", negate(Expr::Binary("<", a.clone(), b.clone()))),
            "a >= b"
        );
        assert_eq!(
            format!("{}", negate(Expr::Unary("!", Box::new(Expr::Local("c".into()))))),
            "c"
        );
    }
}
