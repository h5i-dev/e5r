//! Rendering a structured function as pseudo-C.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use r12e_core::Addr;
use r12e_ir::op::Op;
use r12e_ir::ssa::{Operand, SsaFunction, SsaKind, SsaOp, Value};

use crate::expr::{Expr, Rebuilder, c_type, input_name};
use crate::structure::{Graph, Region, structure};

/// A decompiled function.
#[derive(Debug, Clone)]
pub struct Output {
    /// The C text.
    pub text: String,
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
    let s = structure(f.entry, &graph);
    let rebuilder = Rebuilder::new(f);

    let mut e = Emitter {
        f,
        r: &rebuilder,
        labels: &s.labels,
        unmodelled: 0,
    };

    let body = {
        let mut out = String::new();
        e.region(&mut out, &s.root, 1);
        out
    };

    let mut text = String::new();
    let _ = writeln!(text, "{} {}({})", return_type(f), name, parameters(f, &rebuilder));
    text.push_str("{\n");
    for (value, local) in &rebuilder.locals {
        let _ = writeln!(text, "    {} {};", c_type(value.location.size), local);
    }
    if !rebuilder.locals.is_empty() {
        text.push('\n');
    }
    text.push_str(&body);
    text.push_str("}\n");

    Output {
        text,
        gotos: s.gotos,
        locals: rebuilder.locals.len(),
        unmodelled: e.unmodelled,
    }
}

/// The declared return type, guessed from whether the return register is set.
fn return_type(f: &SsaFunction) -> &'static str {
    let writes_x0 = f.blocks.values().any(|b| {
        b.ops
            .iter()
            .any(|op| op.out.is_some_and(|v| v.location.offset == 0))
    });
    if writes_x0 { "uint64_t" } else { "void" }
}

/// The parameters, taken from the argument registers read before being written.
fn parameters(f: &SsaFunction, r: &Rebuilder) -> String {
    let mut seen: BTreeSet<String> = BTreeSet::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            for i in &op.inputs {
                if let Operand::Undefined(l) = i {
                    let name = input_name(*l);
                    if name.starts_with("arg") {
                        seen.insert(format!("{} {}", c_type(l.size), name));
                    }
                }
            }
        }
    }
    let _ = r;
    if seen.is_empty() {
        "void".to_string()
    } else {
        seen.into_iter().collect::<Vec<_>>().join(", ")
    }
}

struct Emitter<'a> {
    f: &'a SsaFunction,
    r: &'a Rebuilder<'a>,
    labels: &'a BTreeSet<Addr>,
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
                    let _ = writeln!(out, "{pad}    if (!({cond})) break;");
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
                    let _ = writeln!(out, "{pad}return {};", self.result(at));
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
        let Some(b) = self.f.blocks.get(&at) else {
            return String::new();
        };
        let last = b
            .ops
            .iter()
            .rev()
            .find(|op| op.out.is_some_and(|v| v.location.offset == 0 && v.location.size == 8));
        match last.and_then(|op| op.out) {
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
        Expr::Const(..) | Expr::Local(_) | Expr::Input(_) => format!("{e}"),
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
