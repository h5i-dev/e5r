//! What a call hands to what it calls, and how well each argument is known.
//!
//! "Find every call to `memcpy` whose third argument is not bounded by a
//! constant" is the question this exists to answer, and the whole value of the
//! answer is in the difference between two ways of failing to find a bound.
//! Either the code constrains the value nowhere between reading it and passing
//! it, which is a claim about the program, or the analysis could not follow it,
//! which is a claim about the analysis. Printing the first when the second is
//! what happened would make every row untrustworthy, so they are separate
//! verdicts and the row always says which one it is.
//!
//! Nothing here re-derives dataflow. SSA, the interval domain, stack promotion
//! and the ABI model already exist; this walks the reaching definition of each
//! argument register at each call site and reports what those passes already
//! know, plus one thing they do not do: the bound a comparison that guards the
//! call site puts on the value.
//!
//! Three limits are deliberate and are visible in the output rather than
//! hidden.
//!
//! * A bound that comes only from the width the value was read at is not a
//!   bound the code established. It is reported as `width only` with the width
//!   in the bound column, and the verdict stays `unknown`.
//! * A signed comparison bounds a signed value. A length compared as signed
//!   and used as unsigned is the classic bug, so a guard that leaves the low
//!   end at the signed minimum bounds nothing here.
//! * `unconstrained` is a claim about the code, under the assumption that
//!   memory can hold anything the code did not put there. It is only made when
//!   the value arrives from a memory read at the full width of the argument
//!   with nothing but copies and merges in between.

use std::collections::{BTreeMap, BTreeSet};

use e5r_analysis::{Function, Program};
use e5r_core::{Addr, Strength};
use e5r_ir::abi::Abi;
use e5r_ir::op::{Op, Space};
use e5r_ir::range::Range;
use e5r_ir::ssa::{Location, Operand, SsaFunction, SsaKind, SsaOp, Value};

/// How well an argument is bounded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// A constant upper bound the code establishes, with the bound to show.
    Bounded,
    /// The code constrains the value nowhere: on some path it exceeds any
    /// bound. A claim about the program.
    Unconstrained,
    /// No bound was established. A claim about the analysis, and never to be
    /// read as the one above.
    Unknown,
}

impl Verdict {
    /// The word it prints as.
    pub fn as_str(self) -> &'static str {
        match self {
            Verdict::Bounded => "bounded",
            Verdict::Unconstrained => "unconstrained",
            Verdict::Unknown => "unknown",
        }
    }
}

/// Why the verdict is what it is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Basis {
    /// The value is one number, which the code computes and nothing can
    /// change: a literal, or something folded to one.
    Literal,
    /// A comparison that guards the call site bounds it.
    Guard,
    /// Something in the code narrowed it: a mask, a division, a shift.
    Narrowed,
    /// Only the width it was read at says anything, which the code did not
    /// establish and which is not treated as a bound.
    Width,
    /// Read from memory with nothing in between.
    NoConstraint,
    /// It arrives as an argument of the function the call is in.
    Caller,
    /// It is what another call left behind.
    Result,
    /// Nothing was found to say either way.
    Nothing,
}

impl Basis {
    /// The phrase it prints as.
    pub fn as_str(self) -> &'static str {
        match self {
            Basis::Literal => "literal",
            Basis::Guard => "guard",
            Basis::Narrowed => "narrowed",
            Basis::Width => "width only",
            Basis::NoConstraint => "no constraint",
            Basis::Caller => "from the caller",
            Basis::Result => "from a call",
            Basis::Nothing => "no evidence",
        }
    }
}

/// Where a value came from, at the end of the walk.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Source {
    /// A literal the instruction stream carries, with what it points at when
    /// it points at something.
    Constant {
        /// The literal.
        value: u64,
        /// The string it addresses, when it addresses one.
        text: Option<String>,
        /// The symbol it addresses, when it addresses one.
        symbol: Option<String>,
    },
    /// An argument of the function the call site is in.
    Caller {
        /// Which argument, counting from zero.
        index: usize,
    },
    /// A stack slot nothing in this function wrote.
    Frame {
        /// Offset from the entry stack pointer.
        offset: i64,
    },
    /// Read from memory.
    Memory {
        /// The address, when it is a constant.
        at: Option<Addr>,
        /// The symbol at that address, when there is one.
        symbol: Option<String>,
        /// How many bytes were read.
        size: u8,
        /// True when the address is this function's own frame, which is the
        /// shape a spilled local has when promotion refused it.
        frame: bool,
    },
    /// What another call left in the result register.
    Result {
        /// The callee, when the call is direct.
        target: Option<Addr>,
        /// Its name, when it has one.
        name: Option<String>,
    },
    /// A register a call was free to leave holding anything.
    Clobbered,
    /// Computed by an operation the walk does not see through.
    Computed {
        /// The operation.
        op: String,
    },
    /// No reaching definition at all.
    Nothing,
}

impl Source {
    /// One line naming it, for a row of an answer.
    pub fn describe(&self) -> String {
        match self {
            Source::Constant {
                value,
                text,
                symbol,
            } => match (text, symbol) {
                (Some(t), _) => format!("string {t:?}"),
                (None, Some(s)) => format!("address of {s}"),
                (None, None) => format!("literal {value:#x}"),
            },
            Source::Caller { index } => format!("arg{} of this function", index + 1),
            Source::Frame { offset } => format!("stack slot {offset}"),
            Source::Memory {
                at,
                symbol,
                size,
                frame,
            } => match (symbol, at, frame) {
                (Some(s), _, _) => format!("{size}-byte read of {s}"),
                (None, _, true) => format!("{size}-byte read of the frame"),
                (None, Some(a), _) => format!("{size}-byte read of {a}"),
                (None, None, _) => format!("{size}-byte read of memory"),
            },
            Source::Result { name, target } => match (name, target) {
                (Some(n), _) => format!("result of {n}"),
                (None, Some(t)) => format!("result of the call to {t}"),
                (None, None) => "result of an indirect call".to_string(),
            },
            Source::Clobbered => "left by a call".to_string(),
            Source::Computed { op } => format!("computed by {op}"),
            Source::Nothing => "nothing".to_string(),
        }
    }

    /// True when the value was read from somewhere rather than built here.
    ///
    /// A literal is built, whatever it addresses: the pointer to a string is
    /// as fixed as the string. Everything else arrived from outside the
    /// instruction that passes it.
    pub fn is_read(&self) -> bool {
        !matches!(self, Source::Constant { .. } | Source::Nothing)
    }

    /// How well the source itself is known.
    pub fn strength(&self) -> Strength {
        match self {
            // The value is in the encoding.
            Source::Constant { .. } => Strength::Proven,
            // The convention says which register is which argument, and that
            // this register was never written is what the SSA form says.
            Source::Caller { .. }
            | Source::Frame { .. }
            | Source::Memory { .. }
            | Source::Result { .. }
            | Source::Clobbered
            | Source::Computed { .. } => Strength::Inferred,
            Source::Nothing => Strength::Heuristic,
        }
    }
}

/// What is known about one argument at one call site.
#[derive(Debug, Clone)]
pub struct ArgumentFact {
    /// Which argument, counting from zero. `arg1` in a query is index zero.
    pub index: usize,
    /// Bounded, unconstrained, or not established.
    pub verdict: Verdict,
    /// The interval, when anything is known about it.
    pub bound: Option<Range>,
    /// Why.
    pub basis: Basis,
    /// How strongly the verdict is held.
    pub strength: Strength,
    /// Where the value comes from.
    pub sources: Vec<Source>,
}

impl ArgumentFact {
    /// The name it is written as in a query: `arg1` is the first.
    pub fn name(&self) -> String {
        format!("arg{}", self.index + 1)
    }

    /// The bound as a person reads it.
    pub fn bound_text(&self) -> Option<String> {
        let b = self.bound?;
        Some(if b.low == b.high {
            format!("{}", b.low)
        } else {
            format!("{}..={}", b.low, b.high)
        })
    }

    /// The sources as one line.
    pub fn source_text(&self) -> String {
        if self.sources.is_empty() {
            return Source::Nothing.describe();
        }
        self.sources
            .iter()
            .map(|s| s.describe())
            .collect::<Vec<_>>()
            .join(" or ")
    }
}

/// One call, and what it hands over.
#[derive(Debug, Clone)]
pub struct CallSite {
    /// The address of the call itself.
    pub at: Addr,
    /// The function it is in.
    pub caller: Addr,
    /// That function's name.
    pub caller_name: String,
    /// The callee, when the call is direct.
    pub target: Option<Addr>,
    /// The callee's name, when it has one.
    pub target_name: Option<String>,
    /// True when the machine computes the target.
    pub indirect: bool,
    /// How well the target is known.
    pub target_strength: Strength,
    /// One per argument the callee appears to take.
    pub arguments: Vec<ArgumentFact>,
}

impl CallSite {
    /// The target as a person reads it.
    pub fn target_text(&self) -> String {
        match (&self.target_name, self.target) {
            (Some(n), _) => n.clone(),
            (None, Some(t)) => format!("{t}"),
            (None, None) => "indirect".to_string(),
        }
    }

    /// One argument by its zero-based index.
    pub fn argument(&self, index: usize) -> Option<&ArgumentFact> {
        self.arguments.iter().find(|a| a.index == index)
    }

    /// True when the callee's name is this one, with a PLT thunk standing in
    /// for what it reaches.
    pub fn calls(&self, name: &str) -> bool {
        match &self.target_name {
            Some(n) => n == name || plain(n) == name,
            None => false,
        }
    }
}

/// A name with the import thunk's decoration taken off.
fn plain(name: &str) -> &str {
    let name = name.strip_suffix("@plt").unwrap_or(name);
    name.strip_suffix("@got").unwrap_or(name)
}

/// Every call in the program, with what is known about its arguments.
pub fn call_sites(p: &Program) -> Vec<CallSite> {
    let mut state = Analysis::new(p);
    let mut out = Vec::new();
    for f in p.functions_by_address() {
        out.extend(state.function(f));
    }
    out
}

/// Every call in one function.
pub fn call_sites_in(p: &Program, f: &Function) -> Vec<CallSite> {
    Analysis::new(p).function(f)
}

/// Every call to one named callee, anywhere in the program.
///
/// Two shortcuts, and together they are the difference between a question
/// that costs what its callee's callers cost and one that costs what the
/// image costs. Only the functions the cross references say reach the callee
/// are lifted, and inside those only the calls to it are described.
pub fn call_sites_to(p: &Program, name: &str) -> Vec<CallSite> {
    let mut state = Analysis::new(p);
    state.only = Some(name.to_string());
    let mut out = Vec::new();
    for f in callers_of_name(p, name) {
        out.extend(state.function(f));
    }
    out
}

/// The functions that contain a direct call to a function of this name.
///
/// Cross references already record every direct call, so the set of functions
/// worth lifting for a question about one callee is a lookup rather than a
/// scan.
pub fn callers_of_name<'a>(p: &'a Program, name: &str) -> Vec<&'a Function> {
    let mut out: BTreeMap<Addr, &Function> = BTreeMap::new();
    for target in p.functions_by_address() {
        let display = target.display_name();
        if display != name && plain(&display) != name {
            continue;
        }
        for x in p.xrefs.to(target.entry) {
            if x.kind != e5r_analysis::XrefKind::Call {
                continue;
            }
            if let Some(f) = p.function_at(x.from) {
                out.insert(f.entry, f);
            }
        }
    }
    out.into_values().collect()
}

/// How many blocks a function may have before the guard search is skipped.
///
/// The dominator sets are quadratic in the block count, and a query is not
/// allowed to become the slowest thing in the tool on one pathological
/// function. Past this the other evidence still applies and the guard does
/// not, which loses bounds rather than inventing them.
const MAX_BLOCKS_FOR_GUARDS: usize = 512;

/// How far the walk follows a value back before giving up.
const MAX_DEPTH: usize = 64;

/// One program's worth of state, so prototypes are recovered once.
struct Analysis<'a> {
    p: &'a Program,
    abi: Abi,
    arity: BTreeMap<Addr, usize>,
    /// The only callee worth describing, when a query named one. A function
    /// that calls it usually calls several other things as well, and working
    /// out what those are handed is work nobody asked for.
    only: Option<String>,
}

impl<'a> Analysis<'a> {
    fn new(p: &'a Program) -> Analysis<'a> {
        Analysis {
            p,
            abi: e5r_ir::abi::of(&p.object.arch),
            arity: BTreeMap::new(),
            only: None,
        }
    }

    /// Every call in one function.
    fn function(&mut self, f: &Function) -> Vec<CallSite> {
        let Some(ssa) = build(self.p, f) else {
            return Vec::new();
        };
        let ranges = e5r_ir::range::ranges(&ssa);
        let mut defs: BTreeMap<Value, SsaOp> = BTreeMap::new();
        for b in ssa.blocks.values() {
            for op in &b.ops {
                if let Some(out) = op.out {
                    defs.insert(out, op.clone());
                }
            }
        }
        let doms = dominators(&ssa);

        let mut out = Vec::new();
        for (at, b) in &ssa.blocks {
            for (index, op) in b.ops.iter().enumerate() {
                let indirect = match op.kind {
                    SsaKind::Op(Op::Call) => false,
                    SsaKind::Op(Op::CallInd) => true,
                    _ => continue,
                };
                let target = op
                    .inputs
                    .first()
                    .and_then(|i| i.as_const())
                    .filter(|_| !indirect)
                    .map(Addr);
                let target_name = target.and_then(|t| self.p.name_of(t));
                if let Some(only) = &self.only {
                    let hit = target_name
                        .as_deref()
                        .is_some_and(|n| n == only || plain(n) == only);
                    if !hit {
                        continue;
                    }
                }
                let ctx = Site {
                    ssa: &ssa,
                    ranges: &ranges,
                    defs: &defs,
                    doms: &doms,
                    block: *at,
                    index,
                };
                out.push(CallSite {
                    at: op.addr,
                    caller: f.entry,
                    caller_name: f.display_name(),
                    target,
                    target_name,
                    indirect,
                    target_strength: self.target_strength(target, indirect),
                    arguments: self.arguments(&ctx, target),
                });
            }
        }
        out
    }

    /// How sure we are about who is being called.
    fn target_strength(&self, target: Option<Addr>, indirect: bool) -> Strength {
        // That the machine computes its target is what the encoding says: an
        // indirect call is indirect however little is known about where it
        // goes.
        if indirect {
            return Strength::Proven;
        }
        match target.and_then(|t| self.p.function(t)) {
            Some(f) => f.provenance.strength(),
            // A direct call whose target is not a recovered function: the
            // decode gives the address and the rest is a step past it.
            None => Strength::Inferred,
        }
    }

    /// What each argument of a call is.
    fn arguments(&mut self, site: &Site<'_>, target: Option<Addr>) -> Vec<ArgumentFact> {
        let count = self.arity_of(target, site);
        (0..count)
            .map(|index| {
                let offset = self.abi.integer_arguments[index];
                let location = Location {
                    space: Space::Register,
                    offset,
                    size: 8,
                };
                let reaching = site.reaching(location);
                self.fact(site, index, &reaching)
            })
            .collect()
    }

    /// How many arguments to describe.
    ///
    /// Whichever of two counts is larger. The callee's own recovered prototype
    /// is the better evidence where there is one, since a register holding a
    /// leftover from earlier code is not an argument. But an import thunk has
    /// a prototype of nothing — it reads no argument register, it jumps — and
    /// a query about the third argument of a call through one has to be
    /// answered rather than silently dropped, so the argument registers this
    /// call site sets up, counted from the first until one is not set, are the
    /// other half of the answer.
    fn arity_of(&mut self, target: Option<Addr>, site: &Site<'_>) -> usize {
        let most = self.abi.integer_arguments.len();
        let declared = target
            .map(|t| self.declared_arity(t))
            .unwrap_or(0)
            .min(most);
        if declared >= most {
            return most;
        }
        let mut set_up = 0;
        for offset in &self.abi.integer_arguments {
            let location = Location {
                space: Space::Register,
                offset: *offset,
                size: 8,
            };
            // A register nothing in this function wrote is not an argument
            // this call passes: it is whatever arrived, which the reaching
            // walk reports as an undefined location. Neither is one an earlier
            // call was free to leave holding anything, which the IR says in as
            // many words.
            let written = site.reaching(location).iter().any(|o| {
                matches!(o, Operand::Value(_))
                    && !matches!(
                        site.def(*o).map(|d| &d.kind),
                        Some(SsaKind::Op(Op::Undefine))
                    )
            });
            if !written {
                break;
            }
            set_up += 1;
        }
        declared.max(set_up).min(most)
    }

    /// How many integer arguments a callee's own code says it takes.
    fn declared_arity(&mut self, target: Addr) -> usize {
        if let Some(known) = self.arity.get(&target) {
            return *known;
        }
        let n = self
            .p
            .function(target)
            .and_then(|f| build(self.p, f))
            .map(|ssa| e5r_ir::proto::recover(&ssa, &self.abi).integer_arguments)
            .unwrap_or(0);
        self.arity.insert(target, n);
        n
    }

    /// What is known about one argument.
    fn fact(&self, site: &Site<'_>, index: usize, reaching: &[Operand]) -> ArgumentFact {
        if reaching.is_empty() {
            return ArgumentFact {
                index,
                verdict: Verdict::Unknown,
                bound: None,
                basis: Basis::Nothing,
                strength: Strength::Heuristic,
                sources: vec![Source::Nothing],
            };
        }

        let mut sources = Vec::new();
        let mut judgements = Vec::new();
        for operand in reaching {
            let mut seen = BTreeSet::new();
            site.sources(self.p, &self.abi, *operand, &mut seen, &mut sources, 0);
            judgements.push(self.judge(site, *operand));
        }
        sources.dedup();

        // The join over every definition that reaches the call. Bounded only
        // when every path is bounded; unconstrained when any path is, because
        // the claim is about some path and not about all of them.
        let bounded = judgements
            .iter()
            .all(|j| j.verdict == Verdict::Bounded)
            .then(|| {
                judgements
                    .iter()
                    .filter_map(|j| j.bound)
                    .reduce(Range::join)
            })
            .flatten();
        let verdict = match (
            bounded.is_some(),
            judgements
                .iter()
                .any(|j| j.verdict == Verdict::Unconstrained),
        ) {
            (true, _) => Verdict::Bounded,
            (false, true) => Verdict::Unconstrained,
            (false, false) => Verdict::Unknown,
        };
        let leader = judgements
            .iter()
            .find(|j| j.verdict == verdict)
            .unwrap_or(&judgements[0]);
        let bound = match verdict {
            Verdict::Bounded => bounded,
            // Nothing is claimed, but what the width admits is still worth
            // showing next to the reason the verdict is what it is.
            _ => leader.bound,
        };
        ArgumentFact {
            index,
            verdict,
            bound,
            basis: leader.basis,
            strength: strength_of(verdict, leader.basis),
            sources,
        }
    }

    /// What is known about one definition that reaches the call.
    fn judge(&self, site: &Site<'_>, operand: Operand) -> Judgement {
        if let Operand::Const(v, size) = operand {
            let value = signed(v, size);
            return Judgement {
                verdict: Verdict::Bounded,
                bound: Some(Range::exact(value)),
                basis: Basis::Literal,
            };
        }

        let interval = e5r_ir::range::of(&operand, site.ranges);
        // One number and nothing else, which is what the constant a call site
        // materializes in a register looks like once folding has run. As good
        // a bound as the literal it came from.
        if interval.low == interval.high {
            return Judgement {
                verdict: Verdict::Bounded,
                bound: Some(interval),
                basis: Basis::Literal,
            };
        }
        let guard = site.guard(operand);
        let narrowed = site.narrows(operand);

        // The tighter of what the intervals say and what the guard says, with
        // the guard preferred when it is what produced the upper end.
        let combined = match guard {
            Some(g) => Range {
                low: interval.low.max(g.low),
                high: interval.high.min(g.high),
            },
            None => interval,
        };
        let from_guard = guard.is_some_and(|g| g.high <= interval.high);
        // A negative low end means the value is huge read as the unsigned
        // count a size argument is, so it bounds nothing.
        let usable = combined.low >= 0 && combined.high >= combined.low && !combined.is_any();
        if usable && (from_guard || narrowed) {
            return Judgement {
                verdict: Verdict::Bounded,
                bound: Some(combined),
                basis: if from_guard {
                    Basis::Guard
                } else {
                    Basis::Narrowed
                },
            };
        }

        if site.unconstrained(&self.abi, operand) {
            return Judgement {
                verdict: Verdict::Unconstrained,
                bound: None,
                basis: Basis::NoConstraint,
            };
        }

        // Nothing established. The basis says why, which is what tells an
        // analyst whether to go and look.
        let basis = match site.root_kind(&self.abi, operand) {
            RootKind::Caller => Basis::Caller,
            RootKind::Result => Basis::Result,
            RootKind::Other if usable => Basis::Width,
            RootKind::Other => Basis::Nothing,
        };
        Judgement {
            verdict: Verdict::Unknown,
            bound: usable.then_some(combined),
            basis,
        }
    }
}

/// How strongly a verdict is held.
///
/// A literal is in the encoding and nothing can change it. Everything else is
/// derived from a decode that is itself proven, which is what `Inferred` means
/// here. An unknown verdict claims nothing, so it carries the weakest strength
/// there is rather than borrowing one.
fn strength_of(verdict: Verdict, basis: Basis) -> Strength {
    match (verdict, basis) {
        (Verdict::Bounded, Basis::Literal) => Strength::Proven,
        (Verdict::Bounded, _) | (Verdict::Unconstrained, _) => Strength::Inferred,
        (Verdict::Unknown, _) => Strength::Heuristic,
    }
}

/// What one reaching definition says on its own.
struct Judgement {
    verdict: Verdict,
    bound: Option<Range>,
    basis: Basis,
}

/// Which kind of thing a value ultimately comes from.
enum RootKind {
    Caller,
    Result,
    Other,
}

/// One call site, and the function around it.
struct Site<'a> {
    ssa: &'a SsaFunction,
    ranges: &'a BTreeMap<Value, Range>,
    defs: &'a BTreeMap<Value, SsaOp>,
    doms: &'a BTreeMap<Addr, BTreeSet<Addr>>,
    block: Addr,
    index: usize,
}

impl Site<'_> {
    /// The definitions of a location that reach this call site.
    ///
    /// The block first, then its predecessors, which is where a phi is found
    /// when the paths disagree. An empty result at the entry means the
    /// function never wrote the location, which the caller reports as an
    /// incoming value rather than as nothing.
    fn reaching(&self, location: Location) -> Vec<Operand> {
        let mut out: Vec<Operand> = Vec::new();
        let mut seen: BTreeSet<Addr> = BTreeSet::new();
        let mut work = vec![(self.block, self.index)];
        seen.insert(self.block);
        while let Some((at, before)) = work.pop() {
            let Some(b) = self.ssa.blocks.get(&at) else {
                continue;
            };
            let found = b.ops[..before.min(b.ops.len())]
                .iter()
                .rev()
                .filter_map(|op| op.out)
                .find(|v| v.location == location);
            if let Some(v) = found {
                let operand = Operand::Value(v);
                if !out.contains(&operand) {
                    out.push(operand);
                }
                continue;
            }
            if b.predecessors.is_empty() {
                let operand = Operand::Undefined(location);
                if !out.contains(&operand) {
                    out.push(operand);
                }
                continue;
            }
            for pred in &b.predecessors {
                if seen.insert(*pred) {
                    let len = self.ssa.blocks.get(pred).map(|p| p.ops.len()).unwrap_or(0);
                    work.push((*pred, len));
                }
            }
        }
        out
    }

    /// The operation that defined a value, when one did.
    fn def(&self, operand: Operand) -> Option<&SsaOp> {
        match operand {
            Operand::Value(v) => self.defs.get(&v),
            _ => None,
        }
    }

    /// The values a bound on which is a bound on this one.
    ///
    /// Only the steps that carry a bound forward: a copy keeps the value, a
    /// widening keeps a non-negative one, and a truncation cannot raise it. A
    /// phi is not one of these, because a bound on one of the paths into a
    /// merge says nothing about the other.
    fn carriers(&self, operand: Operand, out: &mut BTreeSet<Operand>, depth: usize) {
        if depth > MAX_DEPTH || !out.insert(operand) {
            return;
        }
        let Some(op) = self.def(operand) else { return };
        let SsaKind::Op(kind) = op.kind else { return };
        let carries = match kind {
            Op::Copy | Op::IntZExt | Op::IntSExt => true,
            Op::SubPiece => op.inputs.get(1).and_then(|i| i.as_const()) == Some(0),
            _ => false,
        };
        if !carries {
            return;
        }
        if let Some(input) = op.inputs.first() {
            self.carriers(*input, out, depth + 1);
        }
    }

    /// The bound the comparisons that guard this call site put on a value.
    fn guard(&self, operand: Operand) -> Option<Range> {
        if self.ssa.blocks.len() > MAX_BLOCKS_FOR_GUARDS {
            return None;
        }
        let mut atoms = BTreeSet::new();
        self.carriers(operand, &mut atoms, 0);
        let reached = self.doms.get(&self.block)?;

        let mut out: Option<Range> = None;
        for at in reached {
            if *at == self.block {
                continue;
            }
            let Some(b) = self.ssa.blocks.get(at) else {
                continue;
            };
            let Some(last) = b.ops.last() else { continue };
            if last.kind != SsaKind::Op(Op::CBranch) {
                continue;
            }
            let Some(taken) = self.edge(b, last) else {
                continue;
            };
            let Some(cond) = last.inputs.get(1) else {
                continue;
            };
            let facts = self.constraints(*cond, taken, 0);
            for (atom, range) in facts {
                if !atoms.contains(&atom) {
                    continue;
                }
                out = Some(match out {
                    Some(existing) => Range {
                        low: existing.low.max(range.low),
                        high: existing.high.min(range.high),
                    },
                    None => range,
                });
            }
        }
        out
    }

    /// Whether the call site is on the branch's taken edge or its other one.
    ///
    /// Only when one of the two successors dominates the call: if both do, or
    /// neither, the branch says nothing about how control got here.
    fn edge(&self, b: &e5r_ir::ssa::SsaBlock, cbranch: &SsaOp) -> Option<bool> {
        let target = Addr(cbranch.inputs.first()?.as_const()?);
        if !b.successors.contains(&target) {
            return None;
        }
        let other = *b.successors.iter().find(|s| **s != target)?;
        let by_target = self.dominates(target);
        let by_other = self.dominates(other);
        match (by_target, by_other) {
            (true, false) => Some(true),
            (false, true) => Some(false),
            _ => None,
        }
    }

    /// True when every path to this call site goes through a block.
    fn dominates(&self, block: Addr) -> bool {
        self.doms
            .get(&self.block)
            .is_some_and(|d| d.contains(&block))
    }

    /// What a condition says about the values in it, given which way it went.
    ///
    /// A disjunction keeps only what both sides agree on, because a value
    /// bounded on one side of an `or` and not the other is not bounded. That
    /// is what makes a negated `and` usable, which is the shape a compiler
    /// emits for `if (n > 64) return;`: the call is on the edge where the
    /// conjunction failed, and the two ways it can fail bound the value
    /// between them.
    fn constraints(&self, cond: Operand, taken: bool, depth: usize) -> BTreeMap<Operand, Range> {
        let mut out = BTreeMap::new();
        if depth > MAX_DEPTH {
            return out;
        }
        let Some(op) = self.def(cond) else { return out };
        let SsaKind::Op(kind) = op.kind else {
            return out;
        };
        let a = op.inputs.first().copied();
        let b = op.inputs.get(1).copied();
        match kind {
            Op::Copy => {
                if let Some(a) = a {
                    return self.constraints(a, taken, depth + 1);
                }
            }
            Op::BoolNot => {
                if let Some(a) = a {
                    return self.constraints(a, !taken, depth + 1);
                }
            }
            Op::BoolAnd | Op::BoolOr => {
                let (Some(a), Some(b)) = (a, b) else {
                    return out;
                };
                let both = (kind == Op::BoolAnd) == taken;
                let left = self.constraints(a, taken, depth + 1);
                let right = self.constraints(b, taken, depth + 1);
                if both {
                    // Both hold: every constraint applies, and one on the same
                    // value from both sides applies twice.
                    out = left;
                    for (atom, range) in right {
                        let merged = match out.get(&atom) {
                            Some(existing) => Range {
                                low: existing.low.max(range.low),
                                high: existing.high.min(range.high),
                            },
                            None => range,
                        };
                        out.insert(atom, merged);
                    }
                } else {
                    // One of them holds and nothing says which: only a value
                    // both sides bound is bounded, by the wider of the two.
                    for (atom, range) in left {
                        if let Some(other) = right.get(&atom) {
                            out.insert(atom, range.join(*other));
                        }
                    }
                }
            }
            Op::IntEqual | Op::IntNotEqual => {
                // Equality bounds a value only when it holds; that it is not
                // one particular number is not an interval.
                if taken == (kind == Op::IntEqual) {
                    if let Some((value, k)) = compared(a, b) {
                        out.insert(value, Range::exact(k));
                    }
                }
            }
            Op::IntLess | Op::IntLessEqual | Op::IntSLess | Op::IntSLessEqual => {
                let signed = matches!(kind, Op::IntSLess | Op::IntSLessEqual);
                let orequal = matches!(kind, Op::IntLessEqual | Op::IntSLessEqual);
                let floor = if signed { i64::MIN } else { 0 };
                let (Some(a), Some(b)) = (a, b) else {
                    return out;
                };
                // `x < k` holding, or `k < x` failing, are both upper bounds
                // on the side that is not the constant.
                if let (None, Some(k)) = (a.as_const(), b.as_const().map(|v| signed_of(b, v))) {
                    let high = if orequal { Some(k) } else { k.checked_sub(1) };
                    if let (true, Some(high)) = (taken, high) {
                        out.insert(a, Range { low: floor, high });
                    }
                } else if let (Some(k), None) =
                    (a.as_const().map(|v| signed_of(a, v)), b.as_const())
                {
                    let high = if orequal { k.checked_sub(1) } else { Some(k) };
                    if let (false, Some(high)) = (taken, high) {
                        out.insert(b, Range { low: floor, high });
                    }
                }
            }
            _ => {}
        }
        out
    }

    /// True when something in the code narrowed the value.
    ///
    /// A mask, a division, a remainder or a shift is the code saying how large
    /// the value can be. A widening or a copy is not: it says how large the
    /// storage is, which is not a bound the program established.
    fn narrows(&self, operand: Operand) -> bool {
        let mut seen = BTreeSet::new();
        self.narrows_inner(operand, &mut seen, 0)
    }

    fn narrows_inner(&self, operand: Operand, seen: &mut BTreeSet<Operand>, depth: usize) -> bool {
        if depth > MAX_DEPTH || !seen.insert(operand) {
            return false;
        }
        let Some(op) = self.def(operand) else {
            return false;
        };
        match op.kind {
            SsaKind::Phi => op.inputs.iter().all(|i| {
                matches!(i, Operand::Const(..)) || self.narrows_inner(*i, seen, depth + 1)
            }),
            SsaKind::Op(kind) => match kind {
                Op::IntAnd
                | Op::IntDiv
                | Op::IntRem
                | Op::IntRight
                | Op::IntSRight
                | Op::PopCount
                | Op::LzCount
                | Op::IntEqual
                | Op::IntNotEqual
                | Op::IntLess
                | Op::IntLessEqual
                | Op::IntSLess
                | Op::IntSLessEqual => true,
                Op::Copy | Op::IntZExt | Op::IntSExt | Op::SubPiece => op
                    .inputs
                    .first()
                    .is_some_and(|i| self.narrows_inner(*i, seen, depth + 1)),
                // Arithmetic on something narrowed stays narrowed: the
                // interval domain already carried the bound through it.
                Op::IntAdd | Op::IntSub | Op::IntMul | Op::IntLeft => op
                    .inputs
                    .iter()
                    .any(|i| self.narrows_inner(*i, seen, depth + 1)),
                _ => false,
            },
        }
    }

    /// True when the code constrains this value nowhere.
    ///
    /// Strict on purpose. The value has to arrive from a memory read at the
    /// full width of an argument register with nothing but copies and merges
    /// in between, and no guard on the way to the call. Anything narrower has
    /// its width as a bound, which is not "exceeds any bound", and anything
    /// else on the path is a constraint this refuses to look past.
    fn unconstrained(&self, abi: &Abi, operand: Operand) -> bool {
        let mut seen = BTreeSet::new();
        self.unconstrained_inner(abi, operand, &mut seen, 0)
    }

    fn unconstrained_inner(
        &self,
        abi: &Abi,
        operand: Operand,
        seen: &mut BTreeSet<Operand>,
        depth: usize,
    ) -> bool {
        if depth > MAX_DEPTH || !seen.insert(operand) {
            return false;
        }
        let Some(op) = self.def(operand) else {
            return false;
        };
        match op.kind {
            // A merge is unconstrained when any path into it is, because the
            // claim is that the value exceeds any bound on some path.
            SsaKind::Phi => op
                .inputs
                .iter()
                .any(|i| self.unconstrained_inner(abi, *i, seen, depth + 1)),
            SsaKind::Op(Op::Copy) => op
                .inputs
                .first()
                .is_some_and(|i| self.unconstrained_inner(abi, *i, seen, depth + 1)),
            // A read of this function's own frame is a spilled local, not
            // memory an attacker fills: what put it there is somewhere in this
            // function and the walk did not follow it. Claiming the code
            // constrains it nowhere would be claiming something about the
            // analysis and calling it a fact about the program.
            SsaKind::Op(Op::Load) => {
                op.size >= 8
                    && !op
                        .inputs
                        .first()
                        .is_some_and(|a| self.frame_relative(abi, *a, &mut BTreeSet::new(), 0))
            }
            _ => false,
        }
    }

    /// True when an address is worked out from this function's own frame.
    fn frame_relative(
        &self,
        abi: &Abi,
        operand: Operand,
        seen: &mut BTreeSet<Operand>,
        depth: usize,
    ) -> bool {
        if depth > MAX_DEPTH || !seen.insert(operand) {
            return false;
        }
        match operand {
            Operand::Undefined(l) => {
                l.space == Space::Stack
                    || (l.space == Space::Register && l.offset == abi.stack_pointer)
            }
            Operand::Const(..) => false,
            Operand::Value(v) => {
                if v.location.space == Space::Stack
                    || (v.location.space == Space::Register
                        && v.location.offset == abi.stack_pointer)
                {
                    return true;
                }
                match self.def(operand) {
                    Some(op) => op
                        .inputs
                        .iter()
                        .any(|i| self.frame_relative(abi, *i, seen, depth + 1)),
                    None => false,
                }
            }
        }
    }

    /// Which kind of thing a value comes from, for the reason an unknown
    /// verdict gives.
    fn root_kind(&self, abi: &Abi, operand: Operand) -> RootKind {
        let mut seen = BTreeSet::new();
        let mut sources = Vec::new();
        self.collect(abi, operand, &mut seen, &mut sources, 0);
        if sources.iter().any(|s| matches!(s, Root::Caller)) {
            return RootKind::Caller;
        }
        if sources.iter().any(|s| matches!(s, Root::Result)) {
            return RootKind::Result;
        }
        RootKind::Other
    }

    /// Where a value comes from, followed back to what produced it.
    fn sources(
        &self,
        p: &Program,
        abi: &Abi,
        operand: Operand,
        seen: &mut BTreeSet<Operand>,
        out: &mut Vec<Source>,
        depth: usize,
    ) {
        if depth > MAX_DEPTH || !seen.insert(operand) {
            return;
        }
        let Some(op) = self.def(operand) else {
            let source = match operand {
                // A narrow constant is a number rather than an address,
                // whatever happens to sit at that address.
                Operand::Const(v, size) if size < 8 => Source::Constant {
                    value: v,
                    text: None,
                    symbol: None,
                },
                Operand::Const(v, _) => Source::Constant {
                    value: v,
                    text: p.text_at(Addr(v), 96),
                    symbol: p
                        .object
                        .symbol_at(Addr(v))
                        .filter(|s| s.addr == Addr(v) && !s.name.is_empty())
                        .map(|s| s.name.clone()),
                },
                Operand::Undefined(l) if l.space == Space::Stack => Source::Frame {
                    offset: l.offset as i64,
                },
                Operand::Undefined(l) if l.space == Space::Register => {
                    match abi.integer_arguments.iter().position(|o| *o == l.offset) {
                        Some(index) => Source::Caller { index },
                        None => Source::Computed {
                            op: "a register this function never wrote".to_string(),
                        },
                    }
                }
                _ => Source::Nothing,
            };
            if !out.contains(&source) {
                out.push(source);
            }
            return;
        };

        match op.kind {
            SsaKind::Phi => {
                for i in &op.inputs {
                    self.sources(p, abi, *i, seen, out, depth + 1);
                }
            }
            SsaKind::Op(Op::Copy | Op::IntZExt | Op::IntSExt | Op::SubPiece | Op::Piece) => {
                for i in op.inputs.iter().take(1) {
                    self.sources(p, abi, *i, seen, out, depth + 1);
                }
            }
            SsaKind::Op(Op::Load) => {
                let at = op.inputs.first().and_then(|i| i.as_const()).map(Addr);
                let source = Source::Memory {
                    at,
                    symbol: at.and_then(|a| p.object.symbol_at(a)).and_then(|s| {
                        (!s.name.is_empty() && !s.name.starts_with('$')).then(|| s.name.clone())
                    }),
                    size: op.size,
                    frame: op
                        .inputs
                        .first()
                        .is_some_and(|a| self.frame_relative(abi, *a, &mut BTreeSet::new(), 0)),
                };
                if !out.contains(&source) {
                    out.push(source);
                }
            }
            SsaKind::Op(Op::Call | Op::CallInd) => {
                let target = op.inputs.first().and_then(|i| i.as_const()).map(Addr);
                let source = Source::Result {
                    target,
                    name: target.and_then(|t| p.name_of(t)),
                };
                if !out.contains(&source) {
                    out.push(source);
                }
            }
            SsaKind::Op(Op::Undefine) => {
                if !out.contains(&Source::Clobbered) {
                    out.push(Source::Clobbered);
                }
            }
            SsaKind::Op(other) => {
                let source = Source::Computed {
                    op: format!("{other:?}").to_lowercase(),
                };
                if !out.contains(&source) {
                    out.push(source);
                }
            }
        }
    }

    /// The same walk, kept to the kinds the unknown reason needs.
    fn collect(
        &self,
        abi: &Abi,
        operand: Operand,
        seen: &mut BTreeSet<Operand>,
        out: &mut Vec<Root>,
        depth: usize,
    ) {
        if depth > MAX_DEPTH || !seen.insert(operand) {
            return;
        }
        let Some(op) = self.def(operand) else {
            if let Operand::Undefined(l) = operand {
                if l.space == Space::Register && abi.integer_arguments.contains(&l.offset) {
                    out.push(Root::Caller);
                }
            }
            return;
        };
        match op.kind {
            SsaKind::Op(Op::Call | Op::CallInd | Op::Undefine) => out.push(Root::Result),
            SsaKind::Phi
            | SsaKind::Op(Op::Copy | Op::IntZExt | Op::IntSExt | Op::SubPiece | Op::Piece) => {
                for i in &op.inputs {
                    self.collect(abi, *i, seen, out, depth + 1);
                }
            }
            _ => {}
        }
    }
}

/// What a walk found, without the detail the reason does not need.
enum Root {
    Caller,
    Result,
}

/// The value and the constant of a comparison, when one side is a constant.
fn compared(a: Option<Operand>, b: Option<Operand>) -> Option<(Operand, i64)> {
    match (a?, b?) {
        (value, Operand::Const(k, size)) if value.as_const().is_none() => {
            Some((value, signed(k, size)))
        }
        (Operand::Const(k, size), value) if value.as_const().is_none() => {
            Some((value, signed(k, size)))
        }
        _ => None,
    }
}

/// A constant read at the width the operation reads it at.
fn signed_of(operand: Operand, value: u64) -> i64 {
    signed(value, operand.size())
}

/// A constant read as a signed number of its own width.
fn signed(value: u64, size: u8) -> i64 {
    let bits = (size as u32 * 8).min(64);
    if bits == 64 {
        value as i64
    } else {
        ((value << (64 - bits)) as i64) >> (64 - bits)
    }
}

/// Which blocks every path to a block goes through.
fn dominators(f: &SsaFunction) -> BTreeMap<Addr, BTreeSet<Addr>> {
    let all: BTreeSet<Addr> = f.blocks.keys().copied().collect();
    let mut out: BTreeMap<Addr, BTreeSet<Addr>> = BTreeMap::new();
    for at in &all {
        if *at == f.entry {
            out.insert(*at, BTreeSet::from([*at]));
        } else {
            out.insert(*at, all.clone());
        }
    }
    if all.len() > MAX_BLOCKS_FOR_GUARDS {
        return out;
    }
    // Iterate to a fixed point. The sets only shrink, so this settles in at
    // most one round per block on the longest path.
    let order: Vec<Addr> = f.blocks.keys().copied().collect();
    loop {
        let mut changed = false;
        for at in &order {
            if *at == f.entry {
                continue;
            }
            let Some(b) = f.blocks.get(at) else { continue };
            let mut merged: Option<BTreeSet<Addr>> = None;
            for pred in &b.predecessors {
                let Some(d) = out.get(pred) else { continue };
                merged = Some(match merged {
                    Some(existing) => existing.intersection(d).copied().collect(),
                    None => d.clone(),
                });
            }
            let mut next = merged.unwrap_or_default();
            next.insert(*at);
            if out.get(at) != Some(&next) {
                out.insert(*at, next);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    out
}

/// One function in SSA form, optimized, which is what every pass here reads.
fn build(p: &Program, f: &Function) -> Option<SsaFunction> {
    let blocks: BTreeMap<Addr, (Addr, Vec<Addr>)> = f
        .cfg
        .blocks
        .iter()
        .map(|(a, b)| (*a, (b.range.end(), b.successors.clone())))
        .collect();
    if blocks.is_empty() {
        return None;
    }
    let mut ir = e5r_ir::func::build(&p.object.memory, &p.object.arch, f.entry, &blocks);
    e5r_ir::stack::promote(&mut ir);
    let mut ssa = e5r_ir::ssa::build(&ir);
    e5r_ir::opt::optimize(&mut ssa);
    Some(ssa)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_constant_is_read_at_its_own_width() {
        assert_eq!(signed(0xff, 1), -1);
        assert_eq!(signed(0xff, 8), 255);
        assert_eq!(signed(0x40, 8), 64);
    }

    #[test]
    fn the_verdicts_print_as_different_words() {
        // The whole feature is that these two are never confused, so they are
        // never spelled the same way either.
        assert_ne!(
            Verdict::Unconstrained.as_str(),
            Verdict::Unknown.as_str(),
            "the two ways of not being bounded have to read differently"
        );
    }

    #[test]
    fn only_a_literal_is_proven() {
        assert_eq!(
            strength_of(Verdict::Bounded, Basis::Literal),
            Strength::Proven
        );
        assert_eq!(
            strength_of(Verdict::Bounded, Basis::Guard),
            Strength::Inferred
        );
        assert_eq!(
            strength_of(Verdict::Unconstrained, Basis::NoConstraint),
            Strength::Inferred
        );
        assert_eq!(
            strength_of(Verdict::Unknown, Basis::Caller),
            Strength::Heuristic
        );
    }

    #[test]
    fn an_import_thunk_stands_in_for_what_it_reaches() {
        assert_eq!(plain("memcpy@plt"), "memcpy");
        assert_eq!(plain("memcpy"), "memcpy");
    }
}
