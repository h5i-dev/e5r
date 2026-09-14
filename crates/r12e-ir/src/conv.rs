//! The convention a function actually uses, rather than the one it was
//! assumed to use.
//!
//! [`crate::abi`] says what the platform declares. That is the right default
//! and the wrong answer for a large class of real functions: a `static` a
//! compiler gave a convention of its own, passing in whatever registers were
//! free; a function that takes nothing where the fixed order hands it six
//! arguments; a `__stdcall` that pops the caller's arguments itself. Assuming
//! the default there does not leave a gap, it produces confident nonsense,
//! which is worse.
//!
//! So the convention is observed instead:
//!
//! * an argument is a register read before this function writes it, whether or
//!   not the default passes arguments there. A read of a register the default
//!   passes nothing in is evidence of a convention the compiler invented, not
//!   something to drop;
//! * a result is a register the callers read after the call. A function whose
//!   result nobody reads probably has none, and `void` beats a fabricated
//!   `uint64_t`;
//! * the callee popping the caller's arguments is visible in the stack pointer
//!   at the return, which is where `ret imm16` shows up.
//!
//! What comes out is classified against the default and, when it contradicts
//! it, said so: a [`Departure`] is never normalised away. Where the evidence is
//! thin the answer is [`Convention::Unknown`] rather than a guess.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use r12e_core::provenance::Strength;
use r12e_core::{Addr, Arch};

use crate::abi::{Abi, Named, Slot};
use crate::op::{Op, Space};
use crate::ssa::{Location, Operand, SsaFunction, SsaKind, SsaOp, Value};

/// Where a value was defined, which several of these walks need and none of
/// them should rebuild.
pub(crate) type Definitions = BTreeMap<Value, (Addr, usize)>;

/// How a function's convention compares with the platform default.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Convention {
    /// The evidence is too thin to say. A function the lifter did not model
    /// completely reads registers it would have written, so its entry reads
    /// are not arguments and calling them arguments would be an invention.
    #[default]
    Unknown,
    /// The platform default, using every argument the default passes: nothing
    /// is known to be missing.
    Standard,
    /// The platform default, with fewer arguments than the fixed order would
    /// give it.
    ///
    /// The registers it reads leave a gap: it reads the fourth integer
    /// argument register and not the first three, so the count taken from the
    /// highest slot used is three arguments too high. The gap is the evidence
    /// that the fixed order is not what the caller filled, and it is the case
    /// that puts phantom parameters in a decompilation.
    Fewer,
    /// Not the platform default. [`Detected::departures`] says how.
    NonStandard,
}

impl Convention {
    /// The word used in output and in JSON.
    pub fn as_str(self) -> &'static str {
        match self {
            Convention::Unknown => "unknown",
            Convention::Standard => "standard",
            Convention::Fewer => "standard-fewer-arguments",
            Convention::NonStandard => "non-standard",
        }
    }

    /// True when nothing about the function contradicts the default.
    pub fn is_standard(self) -> bool {
        matches!(self, Convention::Standard | Convention::Fewer)
    }
}

impl fmt::Display for Convention {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// What the default makes of one incoming value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Purpose {
    /// The nth integer argument register of the default.
    Integer(usize),
    /// The nth floating point one.
    Float(usize),
    /// A slot at this offset from the entry stack pointer.
    Stack(i64),
    /// The address the caller wants a memory-returned result written to,
    /// which AAPCS64 passes in `x8`.
    IndirectResult,
    /// How many vector registers a variadic call filled, which System V passes
    /// in `al`.
    VarargsCount,
    /// A register the default passes nothing in.
    Custom,
}

impl Purpose {
    /// True when this is an argument the caller passed, as opposed to a
    /// housekeeping register the convention reserves.
    pub fn is_argument(self) -> bool {
        !matches!(self, Purpose::IndirectResult | Purpose::VarargsCount)
    }

    /// Sort key: the default's own order first, then what it has no slot for.
    fn order(self) -> (u8, i64) {
        match self {
            Purpose::Integer(n) => (0, n as i64),
            Purpose::Float(n) => (1, n as i64),
            Purpose::Stack(o) => (2, o),
            Purpose::IndirectResult => (3, 0),
            Purpose::VarargsCount => (4, 0),
            Purpose::Custom => (5, 0),
        }
    }
}

/// One value that arrives with the function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Incoming {
    /// Where it arrives.
    pub location: Location,
    /// What the default makes of that place.
    pub purpose: Purpose,
}

/// One way a function contradicts the platform default.
///
/// The interesting case, and what this module exists for. Every one of these
/// is reported; none is silently normalised into the default.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Departure {
    /// An argument arrives in a register the default passes nothing in.
    Argument {
        /// Its register file offset.
        register: u64,
    },
    /// The callee removes the caller's arguments from the stack, which on x86
    /// is a `ret imm16`.
    CalleePops {
        /// How many bytes.
        bytes: u64,
    },
    /// A register the default promises to give back unchanged is left changed.
    Clobbers {
        /// Its register file offset.
        register: u64,
    },
    /// A caller reads a result out of a register the default does not return
    /// values in.
    Result {
        /// Its register file offset.
        register: u64,
    },
    /// Nothing in the function returns to its caller, so the default's result
    /// register says nothing about it. A function that never comes back, or
    /// one whose only exit is a tail call.
    NeverReturns,
}

impl fmt::Display for Departure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Departure::Argument { register } => write!(
                f,
                "an argument arrives in {register:#x}, which the convention passes nothing in"
            ),
            Departure::CalleePops { bytes } => {
                write!(f, "the callee pops {bytes} bytes of arguments")
            }
            Departure::Clobbers { register } => write!(
                f,
                "{register:#x} is callee-saved and this function does not put it back"
            ),
            Departure::Result { register } => write!(
                f,
                "a caller reads the result from {register:#x}, which is not a result register"
            ),
            Departure::NeverReturns => write!(f, "nothing returns to the caller"),
        }
    }
}

/// The convention one function was found to use.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Detected {
    /// How it compares with the platform default.
    pub convention: Convention,
    /// A convention with a name that this matches, when one does. A function
    /// that departs from the default but matches another platform's standard
    /// convention is a different finding from one with no name at all.
    pub named: Option<Named>,
    /// How strongly the classification is known.
    pub strength: Strength,
    /// How many call sites corroborated it.
    ///
    /// A convention confirmed at several call sites is better evidence than
    /// one read off a single function's entry reads, and [`Strength`] has no
    /// rung between them, so the corroboration is counted rather than folded
    /// into the rung.
    pub support: usize,
    /// Everything that arrives with a value, in the default's order and then
    /// the places it has no slot for.
    pub arguments: Vec<Incoming>,
    /// Where the result is left, when there is one.
    pub result: Option<u64>,
    /// True when the result register is a vector one.
    pub result_float: bool,
    /// Bytes of the caller's arguments the function removes before returning.
    pub callee_pops: u64,
    /// The register the object arrives in, when the function looks like a
    /// member function.
    ///
    /// Always [`Strength::Heuristic`]: under every convention modelled here
    /// but `__thiscall` the object is an ordinary first argument, so this
    /// names a shape rather than a departure from anything.
    pub this_register: Option<u64>,
    /// False when nothing in the function returns to its caller.
    pub returns_to_caller: bool,
    /// Every way this contradicts the default.
    pub departures: Vec<Departure>,
}

impl Default for Detected {
    fn default() -> Detected {
        Detected {
            convention: Convention::Unknown,
            named: None,
            // Nothing has been looked at, so nothing is known. `Strength` has
            // no `Default` on purpose and this is the honest floor.
            strength: Strength::Heuristic,
            support: 0,
            arguments: Vec::new(),
            result: None,
            result_float: false,
            callee_pops: 0,
            this_register: None,
            returns_to_caller: false,
            departures: Vec::new(),
        }
    }
}

impl Detected {
    /// How many arguments the caller passes, housekeeping registers aside.
    pub fn arity(&self) -> usize {
        self.arguments
            .iter()
            .filter(|a| a.purpose.is_argument())
            .count()
    }

    /// How many arguments the fixed order alone would give this function: one
    /// past the highest slot it touches, whether or not the slots below were
    /// ever read. The number [`Convention::Fewer`] says is too high.
    pub fn assumed_arity(&self) -> usize {
        let slot = |pick: fn(Purpose) -> Option<usize>| {
            self.arguments
                .iter()
                .filter_map(|a| pick(a.purpose))
                .map(|n| n + 1)
                .max()
                .unwrap_or(0)
        };
        slot(|p| match p {
            Purpose::Integer(n) => Some(n),
            _ => None,
        }) + slot(|p| match p {
            Purpose::Float(n) => Some(n),
            _ => None,
        }) + self
            .arguments
            .iter()
            .filter(|a| matches!(a.purpose, Purpose::Stack(_)))
            .count()
    }

    /// The registers the default passes nothing in and this function reads.
    pub fn custom_registers(&self) -> Vec<u64> {
        self.arguments
            .iter()
            .filter(|a| a.purpose == Purpose::Custom)
            .map(|a| a.location.offset)
            .collect()
    }

    /// Rank two detections: the stronger evidence first, then the better
    /// corroborated.
    pub fn rank(&self, other: &Detected) -> std::cmp::Ordering {
        other
            .strength
            .cmp(&self.strength)
            .then_with(|| other.support.cmp(&self.support))
    }

    /// A one-line description, for output that has to say why.
    pub fn describe(&self) -> String {
        let mut out = format!("{} ({}", self.convention, self.strength);
        if self.support > 0 {
            out.push_str(&format!(", {} call site(s)", self.support));
        }
        out.push(')');
        for d in &self.departures {
            out.push_str(&format!("; {d}"));
        }
        out
    }
}

/// What the callers of one function said about it.
///
/// Built by [`observe`] over each caller and merged per callee. Everything in
/// here is evidence the function itself cannot produce: whether anyone reads
/// the result, and which registers the callers actually fill.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Observed {
    /// How many calls were seen.
    pub sites: usize,
    /// How many of them read what the function left in a result register.
    pub result_read: usize,
    /// Register offsets a caller set before the call, and at how many sites.
    pub set: BTreeMap<u64, usize>,
    /// Register offsets a caller read back after the call, and at how many
    /// sites. A register a caller reads back is one the function returned
    /// something in.
    pub read_after: BTreeMap<u64, usize>,
    /// What the compiler recorded about the arguments, one entry per call site
    /// it described, as register file offsets.
    ///
    /// Ground truth: a producer emitting `DW_TAG_call_site_parameter` is
    /// saying where it put each argument. Translate the DWARF register numbers
    /// with [`crate::dwreg::offset`] and put them here, and the detection is
    /// [`Strength::Proven`] rather than inferred.
    pub recorded: Vec<Vec<u64>>,
}

impl Observed {
    /// Fold another observation of the same function into this one.
    pub fn merge(&mut self, other: &Observed) {
        self.sites += other.sites;
        self.result_read += other.result_read;
        for (k, v) in &other.set {
            *self.set.entry(*k).or_default() += v;
        }
        for (k, v) in &other.read_after {
            *self.read_after.entry(*k).or_default() += v;
        }
        self.recorded.extend(other.recorded.iter().cloned());
    }

    /// The registers the compiler said hold arguments, over every call site it
    /// described.
    pub fn recorded_registers(&self) -> BTreeSet<u64> {
        self.recorded.iter().flatten().copied().collect()
    }

    /// The most arguments the compiler recorded at any one call site, which is
    /// the arity it compiled against.
    pub fn recorded_arity(&self) -> Option<usize> {
        self.recorded.iter().map(|r| r.len()).max()
    }

    /// True when nothing was seen at all.
    pub fn is_empty(&self) -> bool {
        self.sites == 0 && self.recorded.is_empty()
    }
}

/// Detect one function's convention from the function alone.
pub fn detect(f: &SsaFunction, abi: &Abi) -> Detected {
    detect_with(f, abi, &Observed::default())
}

/// Detect one function's convention, with what its callers said.
pub fn detect_with(f: &SsaFunction, abi: &Abi, observed: &Observed) -> Detected {
    detect_from(f, abi, &facts(f), &f.definitions(), observed)
}

/// What one pass over a function establishes, so recovery and detection share
/// the walk rather than disagreeing about it.
pub(crate) struct Facts {
    /// Locations read before this function wrote them.
    pub live_in: BTreeSet<Location>,
    /// Register offsets this function writes.
    pub written: BTreeSet<u64>,
    /// True when every instruction was modelled.
    pub complete: bool,
    /// True when some block returns to the caller.
    pub returns_to_caller: bool,
}

/// Walk the function once.
pub(crate) fn facts(f: &SsaFunction) -> Facts {
    let mut live_in = BTreeSet::new();
    let mut written = BTreeSet::new();
    let mut complete = true;
    let mut returns_to_caller = false;
    for b in f.blocks.values() {
        for op in &b.ops {
            for i in &op.inputs {
                if let Operand::Undefined(l) = i {
                    live_in.insert(*l);
                }
            }
            match op.kind {
                SsaKind::Op(Op::Unimplemented) => complete = false,
                SsaKind::Op(Op::Return) => returns_to_caller = true,
                // An undefined value is not a write: it says the location
                // holds something this function did not compute.
                SsaKind::Op(Op::Undefine) => continue,
                _ => {}
            }
            if let Some(v) = op.out {
                if v.location.space == Space::Register {
                    written.insert(v.location.offset);
                }
            }
        }
    }
    Facts {
        live_in,
        written,
        complete,
        returns_to_caller,
    }
}

/// The detection proper, on facts already gathered.
pub(crate) fn detect_from(
    f: &SsaFunction,
    abi: &Abi,
    facts: &Facts,
    definitions: &Definitions,
    observed: &Observed,
) -> Detected {
    let arguments = incoming(f, abi, facts, definitions);
    let unsaved = clobbered(f, abi, &facts.written, definitions);
    let pops = callee_pops(f, abi, definitions);

    let mut departures: Vec<Departure> = Vec::new();
    for a in &arguments {
        if a.purpose == Purpose::Custom {
            departures.push(Departure::Argument {
                register: register_base(abi, a.location.offset),
            });
        }
    }
    for register in &unsaved {
        departures.push(Departure::Clobbers {
            register: *register,
        });
    }
    if pops > 0 {
        departures.push(Departure::CalleePops { bytes: pops });
    }
    if !facts.returns_to_caller && !f.blocks.is_empty() {
        departures.push(Departure::NeverReturns);
    }
    // A register a caller reads back that the default does not return values
    // in is a result the default cannot name. A register the default passes
    // arguments in is excluded: a value sitting in one after a call is the
    // caller setting up the next call far more often than it is a result, and
    // a convention that returns in its own first argument register is rarer
    // than that noise.
    for (register, sites) in &observed.read_after {
        if *sites > 0
            && !abi.results.contains(register)
            && !abi.passes_arguments_in(*register)
            && facts.written.contains(register)
        {
            departures.push(Departure::Result {
                register: *register,
            });
        }
    }
    departures.sort();
    departures.dedup();

    let custom = arguments.iter().any(|a| a.purpose == Purpose::Custom);
    let convention = if !facts.complete || f.blocks.is_empty() {
        // A function the lifter did not model reads registers it would have
        // written, so its entry reads are not evidence of anything.
        Convention::Unknown
    } else if departures.iter().any(|d| *d != Departure::NeverReturns) {
        Convention::NonStandard
    } else if contiguous(&arguments) {
        Convention::Standard
    } else {
        Convention::Fewer
    };

    let (strength, support) = confidence(convention, custom, &arguments, observed);
    let result = result(f, abi, facts, definitions, observed);

    Detected {
        convention,
        named: named(abi, convention, custom, pops),
        strength,
        support,
        result,
        result_float: result.is_some_and(|r| r >= abi.vector_base),
        callee_pops: pops,
        this_register: object_register(f, abi, facts),
        returns_to_caller: facts.returns_to_caller,
        arguments,
        departures,
    }
}

/// True when the argument slots used are the ones the fixed order predicts:
/// the first n integer registers and the first m floating point ones, with no
/// gaps.
///
/// A gap means the function takes fewer arguments than its highest slot says,
/// which is the difference between a prototype and a prototype with phantom
/// parameters in it.
fn contiguous(arguments: &[Incoming]) -> bool {
    let mut integers = 0usize;
    let mut floats = 0usize;
    for a in arguments {
        match a.purpose {
            Purpose::Integer(n) if n == integers => integers += 1,
            Purpose::Integer(_) => return false,
            Purpose::Float(n) if n == floats => floats += 1,
            Purpose::Float(_) => return false,
            _ => {}
        }
    }
    true
}

/// Everything that arrives with a value, classified against the default.
fn incoming(f: &SsaFunction, abi: &Abi, facts: &Facts, definitions: &Definitions) -> Vec<Incoming> {
    let mut out: Vec<Incoming> = Vec::new();
    for l in &facts.live_in {
        let purpose = match l.space {
            // A slot at or above where the convention starts passing arguments
            // was filled by the caller. Below that is the return address on
            // x86 and the shadow space on the Microsoft convention, neither of
            // which is an argument.
            Space::Stack => {
                let offset = l.offset as i64;
                if offset < abi.stack_argument_base {
                    continue;
                }
                Purpose::Stack(offset)
            }
            Space::Register => {
                // The flags are a byte each and arrive holding nothing anyone
                // passed.
                if l.size == 1 || housekeeping(&f.arch, abi, l.offset) {
                    continue;
                }
                let base = register_base(abi, l.offset);
                if Some(base) == abi.indirect_result {
                    Purpose::IndirectResult
                } else if Some(base) == abi.varargs_count {
                    Purpose::VarargsCount
                } else {
                    match abi.slot(base) {
                        Some(Slot::Integer(n)) => Purpose::Integer(n),
                        Some(Slot::Float(n)) => Purpose::Float(n),
                        // A callee-saved register read at entry is the
                        // prologue saving it, not an argument: either the
                        // value goes straight to the frame and nowhere else,
                        // or it is back in place at the return. A register the
                        // function reads and then computes with, and never
                        // puts back, is one the compiler took for itself,
                        // which is the custom convention this looks for.
                        None if abi.callee_saved.contains(&base)
                            && (only_spilled(f, *l) || restored(f, definitions, l.offset)) =>
                        {
                            continue;
                        }
                        None => Purpose::Custom,
                    }
                }
            }
            // A temporary read before it was written is a lifting artifact,
            // and memory is not somewhere the convention passes anything.
            Space::Unique | Space::Ram | Space::Const => continue,
        };
        out.push(Incoming {
            location: *l,
            purpose,
        });
    }
    out.sort_by_key(|i| (i.purpose.order(), i.location.offset));
    out
}

/// The register an offset is part of.
///
/// A vector register is sixteen bytes and SSA versions eight-byte locations,
/// so the upper half of `xmm6` is an offset of its own. Left alone it looks
/// like a register no convention names, and a Windows prologue saving
/// `xmm6` through `xmm15` would read as ten arguments the compiler invented.
fn register_base(abi: &Abi, offset: u64) -> u64 {
    if offset < abi.vector_base {
        return offset;
    }
    abi.vector_base + (offset - abi.vector_base) / 16 * 16
}

/// Registers that are the machine's business rather than the caller's: the
/// stack pointer, the program counter, and the link register that arrives
/// holding the return address.
fn housekeeping(arch: &Arch, abi: &Abi, offset: u64) -> bool {
    if offset == abi.stack_pointer {
        return true;
    }
    match arch {
        Arch::X86_64 | Arch::X86 => offset == crate::lift::x86::pc_offset(),
        // x30 arrives with the return address under every AArch64 convention.
        Arch::AArch64 => offset == crate::lift::aarch64::gpr_offset(30),
        _ => false,
    }
}

/// Callee-saved registers this function writes and does not put back.
pub(crate) fn clobbered(
    f: &SsaFunction,
    abi: &Abi,
    written: &BTreeSet<u64>,
    definitions: &Definitions,
) -> Vec<u64> {
    abi.callee_saved
        .iter()
        .copied()
        .filter(|offset| written.contains(offset) && !restored(f, definitions, *offset))
        .collect()
}

/// Where the result is left, once the callers have had their say.
fn result(
    f: &SsaFunction,
    abi: &Abi,
    facts: &Facts,
    definitions: &Definitions,
    observed: &Observed,
) -> Option<u64> {
    // A register a caller reads back is a result whatever else is true, and it
    // is the only direct evidence there is.
    for register in abi.results.iter() {
        if observed.read_after.get(register).copied().unwrap_or(0) > 0 {
            return Some(*register);
        }
    }
    // Every caller ignored what it left, so it left nothing: `void` beats a
    // fabricated result. A function nothing calls keeps its own answer,
    // because absence of evidence is not evidence.
    if observed.sites > 0 && observed.result_read == 0 {
        return None;
    }
    crate::proto::returned(f, abi, &facts.written, definitions)
}

/// How many bytes of the caller's arguments the function pops on its way out.
///
/// The stack pointer at the return, minus what it started at, minus whatever
/// the call itself pushed. On x86 that is `ret imm16`; on AArch64 the stack
/// pointer comes back where it started and this is zero.
fn callee_pops(f: &SsaFunction, abi: &Abi, definitions: &Definitions) -> u64 {
    let location = Location {
        space: Space::Register,
        offset: abi.stack_pointer,
        size: 8,
    };
    let mut delta: Option<i64> = None;
    for b in f.blocks.values() {
        let Some(at) = b
            .ops
            .iter()
            .position(|op| op.kind == SsaKind::Op(Op::Return))
        else {
            continue;
        };
        // What the stack pointer holds when the return runs: the last thing in
        // this block that wrote it. A block that writes it nowhere leaves the
        // question to a predecessor, and an unproven pop is not claimed.
        let Some(value) = b.ops[..at]
            .iter()
            .rev()
            .filter_map(|op| op.out)
            .find(|v| v.location == location)
        else {
            return 0;
        };
        let Some(found) = entry_offset(f, definitions, value, location, 0) else {
            return 0;
        };
        match delta {
            // Returns that disagree describe two conventions, which is not a
            // thing to average.
            Some(seen) if seen != found => return 0,
            _ => delta = Some(found),
        }
    }
    let popped = delta.unwrap_or(0) - abi.return_address_bytes as i64;
    popped.max(0) as u64
}

/// A value's offset from what a location held at entry, when it is a chain of
/// constant adjustments away from it.
fn entry_offset(
    f: &SsaFunction,
    definitions: &Definitions,
    value: Value,
    location: Location,
    depth: u32,
) -> Option<i64> {
    if depth > 16 {
        return None;
    }
    let (block, index) = definitions.get(&value)?;
    let op = f.blocks.get(block)?.ops.get(*index)?;
    let step = |operand: &Operand| -> Option<i64> {
        match operand {
            Operand::Undefined(l) if *l == location => Some(0),
            Operand::Value(v) => entry_offset(f, definitions, *v, location, depth + 1),
            _ => None,
        }
    };
    match op.kind {
        SsaKind::Op(Op::Copy) => step(op.inputs.first()?),
        SsaKind::Op(Op::IntAdd) | SsaKind::Op(Op::IntSub) => {
            let (a, b) = (op.inputs.first()?, op.inputs.get(1)?);
            let subtract = op.kind == SsaKind::Op(Op::IntSub);
            match (a.as_const(), b.as_const()) {
                (None, Some(n)) if subtract => Some(step(a)? - sign_extend(n, op.size)),
                (None, Some(n)) => Some(step(a)? + sign_extend(n, op.size)),
                // Only the left operand can be the pointer in a subtraction.
                (Some(n), None) if !subtract => Some(step(b)? + sign_extend(n, op.size)),
                _ => None,
            }
        }
        SsaKind::Phi => {
            let mut found: Option<i64> = None;
            for i in &op.inputs {
                let n = step(i)?;
                if found.is_some_and(|seen| seen != n) {
                    return None;
                }
                found = Some(n);
            }
            found
        }
        _ => None,
    }
}

fn sign_extend(value: u64, size: u8) -> i64 {
    match size {
        0 | 8.. => value as i64,
        n => {
            let bits = n as u32 * 8;
            ((value << (64 - bits)) as i64) >> (64 - bits)
        }
    }
}

/// The register the object arrives in, when the function looks like a member
/// function: a pointer only ever dereferenced and never used as a number.
fn object_register(f: &SsaFunction, abi: &Abi, facts: &Facts) -> Option<u64> {
    let candidate = abi
        .this_register
        .or_else(|| abi.integer_arguments.first().copied())?;
    let location = Location {
        space: Space::Register,
        offset: candidate,
        size: 8,
    };
    if !facts.live_in.contains(&location) {
        return None;
    }
    only_dereferenced(f, location).then_some(candidate)
}

/// True when the value a location arrives with goes to the frame and nowhere
/// else, which is a prologue saving a register rather than an argument being
/// used.
fn only_spilled(f: &SsaFunction, location: Location) -> bool {
    let mut spills = 0usize;
    for b in f.blocks.values() {
        for op in &b.ops {
            for (n, i) in op.inputs.iter().enumerate() {
                if !matches!(i, Operand::Undefined(l) if *l == location) {
                    continue;
                }
                match op.kind {
                    // `*sp = reg`, or the same after stack promotion turned the
                    // slot into a location of its own.
                    SsaKind::Op(Op::Store) if n == 1 => spills += 1,
                    SsaKind::Op(Op::Copy)
                        if op.out.is_some_and(|v| v.location.space == Space::Stack) =>
                    {
                        spills += 1
                    }
                    _ => return false,
                }
            }
        }
    }
    spills > 0
}

/// True when an operation only moves a pointer a constant distance, so what it
/// produces is still the same object.
fn derivation(op: &SsaOp) -> bool {
    match op.kind {
        SsaKind::Op(Op::Copy) => true,
        SsaKind::Op(Op::IntAdd) | SsaKind::Op(Op::IntSub) => {
            op.inputs.iter().any(|i| i.as_const().is_some())
        }
        _ => false,
    }
}

/// True when the value arriving in a location is used only as the address of a
/// memory access, directly or a constant away from one.
fn only_dereferenced(f: &SsaFunction, location: Location) -> bool {
    let ours = |operand: &Operand, derived: &BTreeSet<Value>| match operand {
        Operand::Undefined(l) => *l == location,
        Operand::Value(v) => derived.contains(v),
        Operand::Const(..) => false,
    };

    // Grow the set of values that are the object, or a constant away from it.
    // Three sweeps: an address computed in one block and used in another needs
    // the set complete before the uses are judged, and a compiler's field
    // access is one or two steps deep.
    let mut derived: BTreeSet<Value> = BTreeSet::new();
    for _ in 0..3 {
        for b in f.blocks.values() {
            for op in &b.ops {
                if !derivation(op) {
                    continue;
                }
                if op.inputs.iter().any(|i| ours(i, &derived)) {
                    if let Some(v) = op.out {
                        derived.insert(v);
                    }
                }
            }
        }
    }

    let mut loads = 0usize;
    for b in f.blocks.values() {
        for op in &b.ops {
            for (n, i) in op.inputs.iter().enumerate() {
                if !ours(i, &derived) {
                    continue;
                }
                match op.kind {
                    SsaKind::Op(Op::Load) if n == 0 => loads += 1,
                    SsaKind::Op(Op::Store) if n == 0 => {}
                    // Anything else treats the object as a value, which a
                    // `this` pointer is not.
                    _ if derivation(op) => {}
                    _ => return false,
                }
            }
        }
    }
    loads > 0
}

/// True when a register's value at every return is the one it arrived with.
pub(crate) fn restored(f: &SsaFunction, definitions: &Definitions, offset: u64) -> bool {
    let location = Location {
        space: Space::Register,
        offset,
        size: 8,
    };
    for b in f.blocks.values() {
        if !b.ops.iter().any(|op| op.kind == SsaKind::Op(Op::Return)) {
            continue;
        }
        // What the register holds at the return: the last definition in this
        // block, or whatever reached it.
        let last = b
            .ops
            .iter()
            .rev()
            .filter_map(|op| op.out)
            .find(|v| v.location == location);
        match last {
            // Nothing in the returning block wrote it, so it still holds
            // whatever the entry left there.
            None => continue,
            Some(v) => {
                if !crate::proto::is_entry_value(f, definitions, v, location, 0) {
                    return false;
                }
            }
        }
    }
    true
}

/// Which named convention the evidence matches, when one does.
fn named(abi: &Abi, convention: Convention, custom: bool, pops: u64) -> Option<Named> {
    match convention {
        Convention::Unknown => None,
        Convention::Standard | Convention::Fewer => Some(abi.name),
        // A departure that is only the callee popping is another platform's
        // standard convention rather than an invention, and on 32-bit x86 the
        // pop is exactly what tells `__stdcall` from `cdecl`.
        Convention::NonStandard if !custom && pops > 0 => match abi.name {
            Named::Cdecl => Some(Named::Stdcall),
            _ => None,
        },
        Convention::NonStandard => None,
    }
}

/// How well the classification is known, and how much corroborated.
///
/// The ladder: a function the lifter did not model, or one with nothing to go
/// on, is a guess. A function's own entry reads are a step past a proven
/// decode, which is what `Inferred` means. What the compiler recorded about
/// its own call sites is stated by the file in a structure the format defines,
/// which is `Proven`, and it is the strongest gate there is.
fn confidence(
    convention: Convention,
    custom: bool,
    arguments: &[Incoming],
    observed: &Observed,
) -> (Strength, usize) {
    if convention == Convention::Unknown {
        return (Strength::Heuristic, 0);
    }
    if !observed.recorded.is_empty() {
        let recorded = observed.recorded_registers();
        let found: BTreeSet<u64> = arguments
            .iter()
            .filter(|a| a.location.space == Space::Register && a.purpose.is_argument())
            .map(|a| a.location.offset)
            .collect();
        // The compiler named the registers it passed arguments in. Agreeing
        // with it is as good as this gets; disagreeing means the reads are
        // measuring something else and the claim drops back to a guess.
        if recorded.is_subset(&found) {
            return (Strength::Proven, observed.recorded.len());
        }
        return (Strength::Heuristic, observed.recorded.len());
    }
    // Call sites that fill every register this function reads corroborate what
    // its own entry says.
    let support = arguments
        .iter()
        .filter(|a| a.location.space == Space::Register && a.purpose.is_argument())
        .filter_map(|a| observed.set.get(&a.location.offset))
        .copied()
        .min()
        .unwrap_or(0);
    // Callers that fill none of the registers a custom convention needs are
    // evidence against it, not for it.
    if custom && support == 0 && observed.sites > 0 {
        return (Strength::Heuristic, 0);
    }
    (Strength::Inferred, support)
}

/// What one caller's code says about the functions it calls.
///
/// One observation per direct call target. A caller of a function in another
/// compilation unit says nothing about it here, which is correct: the evidence
/// is the code that is present.
pub fn observe(caller: &SsaFunction, abi: &Abi) -> BTreeMap<Addr, Observed> {
    let mut out: BTreeMap<Addr, Observed> = BTreeMap::new();
    let used = consumed(caller, abi);
    // A register a call clobbered counts as read back only when something
    // actually reads it. The convention's own rule -- a value sitting in an
    // argument register when the next call runs is passed to it -- would make
    // every clobbered argument register look like a result, which is how a
    // destructor ends up returning `rcx`.
    let operands = operands(caller);

    for b in caller.blocks.values() {
        // What each register was last given in this block, so the value a call
        // finds there is the one the caller put there.
        let mut latest: BTreeMap<u64, Value> = BTreeMap::new();
        // The call whose clobbers are being walked, if the last thing seen was
        // a call or one of the undefined values it leaves behind.
        let mut after: Option<Addr> = None;
        for op in &b.ops {
            if op.kind == SsaKind::Op(Op::Call) {
                after = None;
                if let Some(target) = op.inputs.first().and_then(|i| i.as_const()) {
                    let at = Addr(target);
                    let entry = out.entry(at).or_default();
                    entry.sites += 1;
                    for offset in latest.keys() {
                        if *offset != abi.stack_pointer {
                            *entry.set.entry(*offset).or_default() += 1;
                        }
                    }
                    if let Some(v) = op.out {
                        if used.contains(&v) {
                            entry.result_read += 1;
                            *entry.read_after.entry(v.location.offset).or_default() += 1;
                        }
                    }
                    after = Some(at);
                }
                // Everything a call clobbers is the callee's answer from here
                // on, not the caller's.
                latest.clear();
                continue;
            }
            if op.kind == SsaKind::Op(Op::Undefine) {
                // A register the call left holding something nobody promised.
                // A caller that goes on to read it is reading a result the
                // convention does not name.
                if let (Some(at), Some(v)) = (after, op.out) {
                    if v.location.space == Space::Register
                        && v.location.size > 1
                        && v.location.offset != abi.stack_pointer
                        && operands.contains(&v)
                    {
                        if let Some(entry) = out.get_mut(&at) {
                            *entry.read_after.entry(v.location.offset).or_default() += 1;
                        }
                    }
                }
                continue;
            }
            after = None;
            if let Some(v) = op.out {
                if v.location.space == Space::Register {
                    latest.insert(v.location.offset, v);
                }
            }
        }
    }
    out
}

/// Every value something in this function reads as an operand.
///
/// A phi input does not count. A phi is a merge the SSA builder inserted, not
/// something the code does, and a register a call clobbered flows into one
/// whenever the call is inside a branch. Counting that as a read would make
/// every clobbered register look like a result the callee returned.
fn operands(f: &SsaFunction) -> BTreeSet<Value> {
    let mut out = BTreeSet::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            if op.kind == SsaKind::Phi {
                continue;
            }
            for i in &op.inputs {
                if let Some(v) = i.as_value() {
                    out.insert(v);
                }
            }
        }
    }
    out
}

/// Every value this function does something with.
///
/// Reading it as an operand is the obvious way and not the only one: a value
/// left in an argument register before a call is passed to that call, and one
/// left in a result register at a return is handed back. Neither appears as an
/// operand, because the registers are the convention rather than the
/// instruction.
fn consumed(f: &SsaFunction, abi: &Abi) -> BTreeSet<Value> {
    let mut out = BTreeSet::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            for i in &op.inputs {
                if let Some(v) = i.as_value() {
                    out.insert(v);
                }
            }
        }
    }

    let argument: BTreeSet<u64> = abi
        .integer_arguments
        .iter()
        .chain(abi.float_arguments.iter())
        .copied()
        .collect();
    let result: BTreeSet<u64> = abi.results.iter().copied().collect();

    for b in f.blocks.values() {
        let mut latest: BTreeMap<u64, Value> = BTreeMap::new();
        for op in &b.ops {
            match op.kind {
                SsaKind::Op(Op::Call) | SsaKind::Op(Op::CallInd) => {
                    for offset in &argument {
                        if let Some(v) = latest.get(offset) {
                            out.insert(*v);
                        }
                    }
                }
                SsaKind::Op(Op::Return) => {
                    for offset in &result {
                        if let Some(v) = latest.get(offset) {
                            out.insert(*v);
                        }
                    }
                }
                _ => {}
            }
            if let Some(v) = op.out {
                if v.location.space == Space::Register {
                    latest.insert(v.location.offset, v);
                }
            }
        }
    }
    out
}
