//! Rendering a structured function as pseudo-C.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use r12e_core::Addr;
use r12e_ir::op::{Op, Space};
use r12e_ir::ssa::{Operand, SsaFunction, SsaKind, SsaOp, Value};

use crate::expr::{Expr, Rebuilder, c_type, input_name, negate};
use crate::structure::{Graph, Region, Switches, Taken, structure_with};

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
    /// Reachable blocks the structuring never placed, whose code is therefore
    /// missing from the text. Zero in a correct decompilation.
    pub lost: usize,
    /// Named locals declared.
    pub locals: usize,
    /// Operations no expression covered.
    pub unmodelled: usize,
    /// The declaration this definition would need, without the body, so a
    /// unit can be assembled with every function declared before it is called.
    pub signature: String,
    /// How many parameters it declares, so a call to it passes that many.
    pub arity: usize,
    /// Which of them are pointers.
    pub pointer_parameters: Vec<bool>,
    /// How wide each one is declared, in bytes, so a caller passing a constant
    /// can write it at the width the callee reads.
    pub parameter_widths: Vec<u8>,
}

/// What the debug information said about a function, when it said anything.
///
/// Names and types the compiler recorded beat anything inferred, so when this
/// is present the parameters are declared as written rather than as the
/// convention's registers.
#[derive(Debug, Clone, Default)]
pub struct Prototype {
    /// The parameters, in order.
    pub parameters: Vec<Param>,
    /// The return type as C spells it.
    pub returns: Option<String>,
    /// Local variables by their offset from the frame base.
    pub locals: BTreeMap<i64, (String, String)>,
    /// Definitions the declarations need, in an order C accepts.
    pub definitions: Vec<String>,
}

/// A function this unit also defines.
#[derive(Debug, Clone)]
pub struct Callee {
    /// What it is called, as C spells it.
    pub name: String,
    /// How many parameters it declares.
    pub arity: usize,
    /// Which of them are pointers, so a call passes something C will take.
    pub pointer_parameters: Vec<bool>,
    /// How wide each one is declared, in bytes.
    pub parameter_widths: Vec<u8>,
    /// False when it was declared to return nothing, so its result is not
    /// assigned to anything.
    pub returns_value: bool,
    /// Its declaration, without a body. Every name the emitter can write has
    /// to be declared somewhere, including a callee nobody asked to see: a
    /// call to an undeclared function is not C a compiler will accept.
    pub signature: String,
}

/// One declared parameter.
#[derive(Debug, Clone)]
pub struct Param {
    /// The name the source gave it.
    pub name: String,
    /// The whole declaration, as C spells it: the type wraps around the name,
    /// so it cannot be rebuilt from the two halves.
    pub decl: String,
    /// True when the convention passes it in a floating point register.
    pub floating: bool,
    /// True when its declared type is a pointer.
    pub pointer: bool,
    /// Its declared width in bytes, zero when unknown.
    pub size: u8,
    /// Fields seen through it, when it is a pointer whose shape was
    /// recovered rather than declared.
    pub fields: Vec<(i64, u8)>,
    /// The element size, when it walks an array of them.
    pub stride: Option<u64>,
    /// Its offset above the entry stack pointer, when the convention ran out
    /// of registers and the caller left it on the stack. `None` for the ones
    /// that arrive in registers.
    pub stack: Option<i64>,
}

/// Decompile an SSA function to pseudo-C.
pub fn decompile(name: &str, f: &SsaFunction) -> Output {
    decompile_with(name, f, None)
}

/// Decompile, using what the debug information said where it said anything.
pub fn decompile_with(name: &str, f: &SsaFunction, prototype: Option<&Prototype>) -> Output {
    decompile_in(name, f, prototype, &BTreeMap::new())
}

/// Decompile as part of a unit, knowing how many arguments its callees take.
///
/// A call whose callee is defined alongside it has to pass the number of
/// arguments that definition declares, or the two do not agree. Where the
/// callee is not in the unit, the declaration leaves the parameters
/// unspecified and the call passes what it can find.
pub fn decompile_in(
    name: &str,
    f: &SsaFunction,
    prototype: Option<&Prototype>,
    callees: &BTreeMap<u64, Callee>,
) -> Output {
    decompile_full(name, f, prototype, callees, &Switches::new())
}

/// Decompile knowing what the program's jump tables mean, so a multi-way
/// branch comes out as a switch rather than as a page of labels.
pub fn decompile_full(
    name: &str,
    f: &SsaFunction,
    prototype: Option<&Prototype>,
    callees: &BTreeMap<u64, Callee>,
    switches: &Switches,
) -> Output {
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
    let s = structure_with(f.entry, &graph, &taken, switches);
    let mut rebuilder = Rebuilder::new(f);
    // A declared parameter arrives in a register the convention chooses, so
    // the body can use the name the source gave it rather than `arg0`.
    if let Some(p) = prototype {
        let (mut ints, mut floats) = (0usize, 0usize);
        for param in &p.parameters {
            let offset = if param.floating {
                let o = rebuilder.abi.float_arguments.get(floats).copied();
                floats += 1;
                o
            } else {
                let o = rebuilder.abi.integer_arguments.get(ints).copied();
                ints += 1;
                o
            };
            if let Some(o) = offset {
                rebuilder.names.insert(o, param.name.clone());
                if param.pointer {
                    rebuilder.pointers.insert(o);
                }
                if param.size > 0 {
                    rebuilder.sizes.insert(o, param.size);
                }
                if !param.fields.is_empty() {
                    rebuilder.fields.insert(o, param.fields.clone());
                    if let Some(stride) = param.stride {
                        rebuilder.strides.insert(o, stride);
                    }
                }
                // A parameter declared floating is floating even when nothing
                // in the body does arithmetic on it: at O0 it is stored to the
                // stack before anything touches it.
                if param.floating {
                    rebuilder.floats.insert(r12e_ir::ssa::Location {
                        space: Space::Register,
                        offset: o,
                        size: 8,
                    });
                }
            }
        }
    }
    let rebuilder = rebuilder;

    let result = result_register(f, &rebuilder);
    let returns = prototype.and_then(|p| p.returns.clone());
    let structured_switches = switch_heads(&s.root);
    let mut e = Emitter {
        f,
        r: &rebuilder,
        labels: &s.labels,
        switches: &structured_switches,
        result,
        callees,
        returns,
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
    // Which names are parameters: the declared ones when there is a prototype,
    // and otherwise the convention's argument registers.
    let declared: BTreeSet<String> = match prototype {
        Some(p) => p
            .parameters
            .iter()
            .map(|param| param.name.clone())
            .collect(),
        None => BTreeSet::new(),
    };
    let mut called: BTreeSet<u64> = BTreeSet::new();
    let mut helpers: BTreeSet<&'static str> = BTreeSet::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            for i in &op.inputs {
                if let r12e_ir::ssa::Operand::Undefined(l) = i {
                    let name = rebuilder.name_of(*l);
                    let is_parameter = if prototype.is_some() {
                        declared.contains(&name)
                    } else {
                        name.starts_with("arg") || name.starts_with("farg")
                    };
                    if !is_parameter {
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
            if let Some(target) = tail_call(f, op) {
                called.insert(target);
            }
            if let SsaKind::Op(o) = op.kind {
                if let Some(h) = helper_for(o) {
                    helpers.insert(h);
                }
            }
        }
    }

    let mut declarations: Vec<String> =
        prototype.map(|p| p.definitions.clone()).unwrap_or_default();
    declarations.extend(helpers.iter().map(|h| h.to_string()));
    declarations.extend(
        called
            .iter()
            .filter(|a| !callees.contains_key(a))
            // No parameter list: what a called function takes is what
            // prototype recovery is for, and guessing four would be a claim.
            .map(|a| format!("uint64_t sub_{a:x}();")),
    );

    // The unknown-result return is written during emission, after the helpers
    // the operations need have been collected, so it declares its own.
    if body.contains("__clobbered(") && !declarations.iter().any(|d| d.contains("__clobbered")) {
        declarations.push("uint64_t __clobbered(void);".to_string());
    }

    let mut text = String::new();
    let declared_return = prototype
        .and_then(|p| p.returns.clone())
        .unwrap_or_else(|| return_type(result, &rebuilder).to_string());
    let declared: Vec<String> = match prototype {
        Some(p) if !p.parameters.is_empty() => p
            .parameters
            .iter()
            // A parameter whose type did not resolve is still a parameter; C
            // has no `void` argument, so it is declared as what it occupies.
            .map(|param| {
                if param.decl.starts_with("void ") {
                    format!("uint64_t {}", param.name)
                } else {
                    param.decl.clone()
                }
            })
            .collect(),
        Some(p) if p.returns.is_some() => Vec::new(),
        _ => parameter_list(f, &rebuilder),
    };
    let arity = declared.len();
    let pointer_parameters: Vec<bool> = match prototype {
        Some(p) => p.parameters.iter().map(|param| param.pointer).collect(),
        None => vec![false; arity],
    };
    let parameter_widths: Vec<u8> = match prototype {
        Some(p) => p.parameters.iter().map(|param| param.size).collect(),
        None => vec![8; arity],
    };
    let declared_parameters = if declared.is_empty() {
        "void".to_string()
    } else {
        declared.join(", ")
    };
    let signature = format!(
        "{declared_return} {}({declared_parameters})",
        identifier(name)
    );
    let _ = writeln!(text, "{signature}");
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
        signature,
        arity,
        pointer_parameters,
        parameter_widths,
        declarations,
        gotos: s.gotos,
        lost: s.lost.len(),
        locals: rebuilder.locals.len(),
        unmodelled: e.unmodelled,
    }
}

/// Declarations every unit needs: the reinterpretations between a value's bits
/// and the number they stand for, which the machine does for free and C does
/// not.
const REINTERPRET: &str = "\
static inline uint64_t __bits(double v){union{double d;uint64_t u;}x;x.d=v;return x.u;}
static inline double __dbl(uint64_t v){union{double d;uint64_t u;}x;x.u=v;return x.d;}
static inline uint32_t __bits32(float v){union{float f;uint32_t u;}x;x.f=v;return x.u;}
static inline float __flt(uint64_t v){union{float f;uint32_t u;}x;x.u=(uint32_t)v;return x.f;}";

/// The function a branch tails into, when it leaves this function entirely.
///
/// A tail call is a plain branch to something that is no block of this
/// function: the callee returns on the caller's behalf. Nothing else in the IR
/// marks it, and a branch is not otherwise a statement, so without this both
/// the call and the return it stands for vanish and the body comes out empty.
fn tail_call(f: &SsaFunction, op: &SsaOp) -> Option<u64> {
    if op.kind != SsaKind::Op(Op::Branch) {
        return None;
    }
    let target = op.inputs.first()?.as_const()?;
    (!f.blocks.contains_key(&Addr(target))).then_some(target)
}

/// True when a region always leaves by itself, so no `break` is needed after.
fn ends_control(r: &Region) -> bool {
    match r {
        Region::Break | Region::Continue | Region::Goto(_) => true,
        Region::Seq(parts) => parts.last().is_some_and(ends_control),
        _ => false,
    }
}

/// A name C will accept: anything else becomes an underscore.
pub fn identifier(name: &str) -> String {
    let mut out: String = name
        .chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect();
    if out.chars().next().is_some_and(|c| c.is_ascii_digit()) {
        out.insert(0, '_');
    }
    if out.is_empty() {
        out.push('_');
    }
    out
}

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
        Op::BranchInd => "void __indirect_branch(uint64_t);",
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
        Op::Undefine => "uint64_t __clobbered(void);",
        Op::CBranch => "int __condition(void);",
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
        let returns = b.ops.iter().any(|op| op.kind == SsaKind::Op(Op::Return));
        if !returns {
            continue;
        }
        for (n, op) in b.ops.iter().enumerate() {
            let Some(v) = op.out else { continue };
            if v.location.space != Space::Register || !r.abi.results.contains(&v.location.offset) {
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
fn parameter_list(f: &SsaFunction, r: &Rebuilder) -> Vec<String> {
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
    seen.into_values().collect()
}

/// The blocks a region tree turned into a `switch`.
///
/// Their indirect branch is the switch itself, so writing it out as well would
/// say the control transfer twice.
fn switch_heads(r: &Region) -> BTreeSet<Addr> {
    let mut out = BTreeSet::new();
    collect_switch_heads(r, &mut out);
    out
}

fn collect_switch_heads(r: &Region, out: &mut BTreeSet<Addr>) {
    match r {
        Region::Seq(parts) => {
            for p in parts {
                collect_switch_heads(p, out);
            }
        }
        Region::If {
            then, otherwise, ..
        } => {
            collect_switch_heads(then, out);
            if let Some(o) = otherwise {
                collect_switch_heads(o, out);
            }
        }
        Region::While { body, .. } | Region::Infinite { body, .. } => {
            collect_switch_heads(body, out);
        }
        Region::Switch {
            head,
            cases,
            default,
        } => {
            out.insert(*head);
            for c in cases {
                collect_switch_heads(&c.body, out);
            }
            if let Some(d) = default {
                collect_switch_heads(d, out);
            }
        }
        _ => {}
    }
}

struct Emitter<'a> {
    f: &'a SsaFunction,
    r: &'a Rebuilder<'a>,
    labels: &'a BTreeSet<Addr>,
    /// Blocks whose indirect branch the region tree already says as a `switch`.
    switches: &'a BTreeSet<Addr>,
    /// Where the function leaves its result.
    result: Option<u64>,
    /// How many arguments each callee defined in this unit takes.
    callees: &'a BTreeMap<u64, Callee>,
    /// The declared return type, which the returned expression is converted
    /// to: the machine leaves bits in a register and the declaration says what
    /// they mean.
    returns: Option<String>,
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
                    let _ = writeln!(
                        out,
                        "{}L{:x}:",
                        "    ".repeat(depth.saturating_sub(1)),
                        at.0
                    );
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
            Region::While { head, invert, body } => {
                if self.labels.contains(head) {
                    let _ = writeln!(
                        out,
                        "{}L{:x}:",
                        "    ".repeat(depth.saturating_sub(1)),
                        head.0
                    );
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
            Region::Switch {
                head,
                cases,
                default,
            } => {
                let index = self.switch_index(*head);
                let _ = writeln!(out, "{pad}switch ({index}) {{");
                for case in cases {
                    for value in &case.values {
                        let _ = writeln!(out, "{pad}case {value}:");
                    }
                    self.region(out, &case.body, depth + 1);
                    if !ends_control(&case.body) {
                        let _ = writeln!(out, "{pad}    break;");
                    }
                }
                if let Some(d) = default {
                    let _ = writeln!(out, "{pad}default:");
                    self.region(out, d, depth + 1);
                    if !ends_control(d) {
                        let _ = writeln!(out, "{pad}    break;");
                    }
                }
                let _ = writeln!(out, "{pad}}}");
            }
            Region::Infinite { head, body } => {
                if self.labels.contains(head) {
                    let _ = writeln!(
                        out,
                        "{}L{:x}:",
                        "    ".repeat(depth.saturating_sub(1)),
                        head.0
                    );
                }
                let _ = writeln!(out, "{pad}while (1) {{");
                self.statements(out, *head, depth + 1);
                self.region(out, body, depth + 1);
                let _ = writeln!(out, "{pad}}}");
            }
        }
    }

    /// What a switch switches on.
    ///
    /// The branch computes an address; the index is what was used to look it
    /// up. Recovering it means finding the table read in the address's own
    /// expression, which is the shape the jump table analysis already proved
    /// is there. Where that fails the address itself is switched on, which is
    /// correct and reads worse.
    fn switch_index(&self, at: Addr) -> Expr {
        let branch = self
            .f
            .blocks
            .get(&at)
            .and_then(|b| {
                b.ops
                    .iter()
                    .rev()
                    .find(|op| op.kind == SsaKind::Op(Op::BranchInd))
            })
            .and_then(|op| op.inputs.first().copied());
        let Some(operand) = branch else {
            return Expr::Unknown("switch");
        };
        if let Some(index) = self.table_index(&operand, 0) {
            return index;
        }
        self.r.operand(&operand)
    }

    /// The index an expression looks up, found by walking to the table read.
    fn table_index(&self, operand: &Operand, depth: u32) -> Option<Expr> {
        if depth > 8 {
            return None;
        }
        let Operand::Value(v) = operand else {
            return None;
        };
        let (block, index) = self.r.definition_site(*v)?;
        let op = self.f.blocks.get(&block)?.ops.get(index)?;
        let SsaKind::Op(o) = op.kind else { return None };
        match o {
            // The read itself: the address is a constant table plus the index
            // scaled by the entry size.
            Op::Load => {
                let address = op.inputs.first()?;
                self.scaled_index(address, 0)
            }
            // Anything on the way there: the sign extension, the addition of
            // the base, the shift.
            _ => op
                .inputs
                .iter()
                .find_map(|i| self.table_index(i, depth + 1)),
        }
    }

    /// The index inside an address of the form `table + index * size`.
    fn scaled_index(&self, operand: &Operand, depth: u32) -> Option<Expr> {
        if depth > 8 {
            return None;
        }
        let Operand::Value(v) = operand else {
            return None;
        };
        let (block, index) = self.r.definition_site(*v)?;
        let op = self.f.blocks.get(&block)?.ops.get(index)?;
        let SsaKind::Op(o) = op.kind else { return None };
        match o {
            Op::IntAdd => {
                // One side is the table's address, the other the scaled index.
                let (a, b) = (op.inputs.first()?, op.inputs.get(1)?);
                if a.as_const().is_some() {
                    self.scaled_index(b, depth + 1)
                        .or_else(|| Some(self.r.operand(b)))
                } else if b.as_const().is_some() {
                    self.scaled_index(a, depth + 1)
                        .or_else(|| Some(self.r.operand(a)))
                } else {
                    self.scaled_index(a, depth + 1)
                        .or_else(|| self.scaled_index(b, depth + 1))
                }
            }
            Op::IntLeft | Op::IntMul => {
                let a = op.inputs.first()?;
                self.scaled_index(a, depth + 1)
                    .or_else(|| Some(self.r.operand(a)))
            }
            Op::IntZExt | Op::IntSExt | Op::Copy => {
                let a = op.inputs.first()?;
                self.scaled_index(a, depth + 1)
                    .or_else(|| Some(self.r.operand(a)))
            }
            // A truncation is where the index starts: the table was indexed by
            // the narrow value, so walking past it switches on the wide one
            // and every argument whose low half is in range falls off the end
            // of the switch instead of into its arm.
            Op::SubPiece => Some(self.r.operand(operand)),
            _ => None,
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
                // A branch whose condition the lifter did not model. Saying so
                // is the point; the helper exists so the output still
                // compiles.
                self.unmodelled += 1;
                Expr::Named("__condition", Vec::new())
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
                let value = self.r.integer(self.r.operand(input), input);
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
        for (index, op) in b.ops.iter().enumerate() {
            if !self.is_statement(op) {
                continue;
            }
            let SsaKind::Op(o) = op.kind else { continue };
            match o {
                Op::Store => {
                    // A store to a known field says so, the same as a load.
                    if let Some(field) = self
                        .r
                        .field_access(op.inputs.first(), op.size)
                        .filter(|_| op.size > 0)
                    {
                        if let Some(value) = op
                            .inputs
                            .get(1)
                            .map(|i| self.r.integer(self.r.operand(i), i))
                        {
                            let _ = writeln!(out, "{pad}{field} = {value};");
                            continue;
                        }
                    }
                    let addr = op
                        .inputs
                        .first()
                        .map(|i| self.r.integer(self.r.operand(i), i));
                    let val = op
                        .inputs
                        .get(1)
                        .map(|i| self.r.integer(self.r.operand(i), i));
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
                    let _ = writeln!(out, "{pad}{}", self.return_statement(at));
                }
                Op::Call | Op::CallInd => {
                    let void = match op.inputs.first().and_then(|i| i.as_const()) {
                        Some(target) => self.callees.get(&target).is_some_and(|c| !c.returns_value),
                        None => false,
                    };
                    let e = match (o, op.inputs.first().and_then(|i| i.as_const())) {
                        (Op::Call, Some(target)) => {
                            let callee = self.callees.get(&target);
                            let name = callee
                                .map(|c| c.name.clone())
                                .unwrap_or_else(|| crate::expr::default_call_name(target));
                            Expr::Call(name, self.arguments(at, index, callee))
                        }
                        _ => self.r.expr(op),
                    };
                    match op.out.and_then(|v| self.r.locals.get(&v)).filter(|_| !void) {
                        // The local is an integer and the callee may be
                        // declared to return a pointer, which C will not
                        // assign without being told.
                        Some(name) => {
                            let _ = writeln!(out, "{pad}{name} = (uint64_t)({e});");
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
                Op::Branch => {
                    let Some(target) = tail_call(self.f, op) else {
                        continue;
                    };
                    let callee = self.callees.get(&target);
                    let name = callee
                        .map(|c| c.name.clone())
                        .unwrap_or_else(|| crate::expr::default_call_name(target));
                    let e = Expr::Call(name, self.arguments(at, index, callee));
                    let _ = writeln!(out, "{pad}{e};");
                    let _ = writeln!(out, "{pad}{}", self.return_statement(at));
                }
                Op::BranchInd => {
                    // A computed branch that structuring did not turn into a
                    // switch. C's own computed goto needs a label table this
                    // does not have, so the target is named and the control
                    // transfer is said rather than spelled.
                    if self.switches.contains(&at) {
                        continue;
                    }
                    if let Some(t) = op.inputs.first().map(|i| self.r.operand(i)) {
                        let target = self.r.integer(t, &op.inputs[0]);
                        let _ = writeln!(out, "{pad}__indirect_branch({target});");
                        let _ = writeln!(out, "{pad}{}", self.return_statement(at));
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
            // A branch out of the function is a tail call and has to be said.
            // Any other branch is control flow the region tree already carries.
            Op::Branch => tail_call(self.f, op).is_some(),
            Op::CBranch => false,
            // Everything else is an expression, needed as a statement only when
            // its result got a name.
            _ => op.out.is_some_and(|v| self.r.locals.contains_key(&v)),
        }
    }

    /// The `return` a block ends with, converted to the declared type.
    fn return_statement(&self, at: Addr) -> String {
        let value = self.result(at);
        match (&self.returns, value.is_empty()) {
            (Some(ty), _) if ty == "void" => "return;".to_string(),
            // The value is already rendered, so the cast needs its own
            // parentheses: a cast binds tighter than anything in an
            // expression and would otherwise apply to the first term.
            (Some(ty), false) => format!("return ({ty})({value});"),
            // Declared to return something, with nothing found that it
            // returns: an import thunk, or a result the rebuilder could not
            // name. Zero would be a claim about the value; the helper says
            // only that it is not known, which is what was established.
            (Some(ty), true) => format!("return ({ty})__clobbered();"),
            (None, false) => format!("return {value};"),
            (None, true) => "return;".to_string(),
        }
    }

    /// The arguments a call passes, read out of the convention's registers.
    ///
    /// The value each one holds is whatever last wrote it before the call. A
    /// register nothing wrote is passed as zero rather than left out, because
    /// the count has to match what the callee declares.
    fn arguments(&self, at: Addr, index: usize, callee: Option<&Callee>) -> Vec<Expr> {
        let Some(callee) = callee else {
            return Vec::new();
        };
        let n = callee.arity;
        let pointers = &callee.pointer_parameters;
        let mut out = Vec::new();
        for (slot, offset) in self.r.abi.integer_arguments.iter().enumerate().take(n) {
            let value = match self.value_before(at, index, *offset) {
                Some(v) => self.r.operand(&Operand::Value(v)),
                None => Expr::Const(0, 8),
            };
            // A constant written into a 64-bit register by a 32-bit move is
            // held as the whole register, so `-512` arrives as `0xfffffe00`.
            // The callee reads four bytes of it, so four bytes is what the
            // call passes, and the reader gets the number back.
            let value = match (value, callee.parameter_widths.get(slot)) {
                (Expr::Const(v, size), Some(&w)) if w > 0 && w < size => {
                    Expr::Const(v & (u64::MAX >> (64 - w as u32 * 8)), w)
                }
                (v, _) => v,
            };
            // A parameter declared as a pointer needs the argument cast to it:
            // the machine passes bits and C wants to be told what they are.
            match pointers.get(slot) {
                Some(true) => out.push(Expr::Cast("void *", Box::new(value))),
                _ => out.push(value),
            }
        }
        // A callee with more parameters than there are argument registers
        // takes the rest on the stack, which this does not recover; the count
        // still has to match what it declares.
        while out.len() < n {
            out.push(Expr::Const(0, 8));
        }
        out
    }

    /// The value a register held just before an operation.
    fn value_before(&self, at: Addr, index: usize, offset: u64) -> Option<Value> {
        let b = self.f.blocks.get(&at)?;
        if let Some(v) = b.ops[..index]
            .iter()
            .rev()
            .filter_map(|op| op.out)
            .find(|v| v.location.space == Space::Register && v.location.offset == offset)
        {
            return Some(v);
        }
        // Nothing in this block wrote it, so whatever reached the block did.
        // Without liveness this takes the newest version, which is right
        // whenever the register is written once.
        self.f
            .blocks
            .values()
            .flat_map(|other| other.ops.iter())
            .filter_map(|op| op.out)
            .filter(|v| v.location.space == Space::Register && v.location.offset == offset)
            .max_by_key(|v| v.version)
    }

    /// What a function returns: whatever last reached the result register.
    fn result(&self, at: Addr) -> String {
        let Some(offset) = self.result else {
            return String::new();
        };
        let in_block = self.f.blocks.get(&at).and_then(|b| {
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
            format!(
                "{}",
                negate(Expr::Unary("!", Box::new(Expr::Local("c".into()))))
            ),
            "c"
        );
    }
}
