//! What a function takes and gives back, worked out from what it does.
//!
//! A prototype is not written down in a stripped binary, but it is visible: a
//! register read before anything wrote it arrived with a value, and a register
//! written on the way to a return is left for the caller. That is enough to
//! recover the shape of most functions, and where it is not, saying so is
//! better than inventing a parameter.
//!
//! The convention gives the candidates and the code decides which of them are
//! used. A function that reads the third argument register and not the first
//! two still takes three arguments: the first two are unused, not absent.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use r12e_core::Arch;
use r12e_core::provenance::Strength;
use r12e_types::cdecl;
use r12e_types::ctype::{Model, Signature, Type, TypeId, Types};

use crate::abi::Abi;
use crate::op::{Op, Space};
use crate::ssa::{Location, Operand, SsaFunction, SsaKind};

/// What a function appears to take and return.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Prototype {
    /// How many integer argument registers it takes, counting the unused ones
    /// before the last one it reads.
    pub integer_arguments: usize,
    /// How many floating point ones.
    pub float_arguments: usize,
    /// Offsets from the entry stack pointer of the arguments passed there.
    pub stack_arguments: Vec<i64>,
    /// Where it leaves a value the caller could read, when it leaves one.
    ///
    /// A possibility, not a promise. A function that computes an address into
    /// the first argument register on its way out has left something there,
    /// and nothing inside the function says whether anyone reads it: only its
    /// callers do. What this does guarantee is the other direction — a
    /// function that leaves nothing has `None` — so a caller is never denied a
    /// result that exists.
    pub returns: Option<u64>,
    /// True when the result is a floating point register.
    pub returns_float: bool,
    /// Callee-saved registers it writes without putting back, which is a
    /// convention the compiler invented rather than the standard one.
    pub unsaved: Vec<u64>,
    /// True when nothing about the function contradicts the standard
    /// convention.
    pub standard: bool,
    /// The name a declaration gave the function, when one did.
    pub name: Option<String>,
    /// The parameters, with the types a declaration gave them.
    ///
    /// Empty when nothing was asserted: recovery on its own knows how many
    /// registers arrive with values and nothing about what is in them.
    pub parameters: Vec<Parameter>,
    /// The declared return type, when a declaration gave one. `None` here and
    /// a `returns` register together mean the code leaves something behind
    /// that nobody has named.
    pub return_type: Option<TypeId>,
    /// True when a declaration said the function is variadic.
    pub varargs: bool,
    /// True when the declared result is too large for the result registers and
    /// the caller passes its address as a hidden first argument.
    ///
    /// The emitter needs this: with it set, the first integer argument
    /// register is not parameter zero.
    pub returns_via_memory: bool,
    /// Which of these fields the code decided and which a person did.
    pub origin: Origin,
    /// Where the declaration and the code disagree. The declaration wins; this
    /// is the record of what it overrode.
    pub conflicts: Vec<Conflict>,
    /// What the code alone said, kept when a declaration overrode it.
    ///
    /// An analyst who declares three parameters where the code reads four
    /// registers is entitled to be believed, and the fourth read still
    /// happened. Nothing the machine saw is thrown away by an assertion.
    pub recovered: Option<Box<Prototype>>,
}

/// Where each part of a prototype came from.
///
/// `ROADMAP.md` bet 4: every fact says how strongly it is known. A parameter
/// count worked out from the registers a function reads is
/// [`Strength::Inferred`]; one a person wrote down is [`Strength::Asserted`]
/// and outranks it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Origin {
    /// The parameters: how many, where and what.
    pub arguments: Strength,
    /// The result and its register.
    pub returns: Strength,
    /// Whether it is variadic.
    pub varargs: Strength,
}

impl Default for Origin {
    fn default() -> Origin {
        // Recovery reads a proven decode and takes a step past it, which is
        // exactly what `Inferred` means.
        Origin {
            arguments: Strength::Inferred,
            returns: Strength::Inferred,
            varargs: Strength::Inferred,
        }
    }
}

/// Where the convention passes one argument.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Storage {
    /// The nth integer argument register the convention names.
    Integer(usize),
    /// The nth floating point one.
    Float(usize),
    /// A slot at this offset from the entry stack pointer.
    Stack(i64),
}

/// One parameter of a declared prototype.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parameter {
    /// Its name, when the declaration gave one.
    pub name: Option<String>,
    /// Its declared type.
    pub ty: TypeId,
    /// Its width in bytes, zero when the type has no size.
    pub size: u64,
    /// Where it is passed. More than one slot for an aggregate that spans
    /// registers.
    pub storage: Vec<Storage>,
    /// Whether the code or a person decided this.
    pub strength: Strength,
}

/// A disagreement between an asserted declaration and the code.
///
/// Every one of these is reported and none of them changes the answer: the
/// declaration is the analyst's to make. The point is that an output which
/// differs from what the machine found can say why.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Conflict {
    /// The code reads an argument register the declaration does not account
    /// for. The declaration still wins; this says what was set aside.
    ExtraArgument {
        /// The register file offset the code read.
        register: u64,
        /// Which argument slot of the convention that is.
        slot: usize,
    },
    /// The declaration names an argument the code never reads.
    UnreadArgument {
        /// Its index in the declaration.
        index: usize,
    },
    /// The declaration needs a register the convention does not pass arguments
    /// or results in.
    OffConvention {
        /// The parameter it applies to, or `None` for the result.
        index: Option<usize>,
        /// What the convention cannot do.
        detail: String,
    },
    /// The declaration returns nothing and the code leaves a value behind.
    ResultDiscarded {
        /// Where the code left it.
        register: u64,
    },
    /// The declaration returns a value the code never computes.
    ResultMissing,
    /// The declaration's result register is not the one the code writes.
    ResultElsewhere {
        /// Where the convention says the declared result goes.
        declared: u64,
        /// Where the code actually writes.
        written: u64,
    },
}

impl fmt::Display for Conflict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Conflict::ExtraArgument { register, slot } => write!(
                f,
                "the code reads argument register {slot} (offset {register:#x}), which the declaration does not name"
            ),
            Conflict::UnreadArgument { index } => {
                write!(f, "parameter {index} is declared and never read")
            }
            Conflict::OffConvention { index, detail } => match index {
                Some(n) => write!(f, "parameter {n}: {detail}"),
                None => write!(f, "the result: {detail}"),
            },
            Conflict::ResultDiscarded { register } => write!(
                f,
                "the declaration returns nothing and the code leaves a value in {register:#x}"
            ),
            Conflict::ResultMissing => {
                write!(f, "the declaration returns a value the code never computes")
            }
            Conflict::ResultElsewhere { declared, written } => write!(
                f,
                "the declaration's result belongs in {declared:#x} and the code writes {written:#x}"
            ),
        }
    }
}

/// A C declaration a person asserted about a function.
///
/// It owns its types because a declaration mentions types nothing else in the
/// program has heard of: an analyst who writes `int f(struct sockaddr *)` has
/// just introduced `struct sockaddr`.
#[derive(Debug, Clone)]
pub struct Asserted {
    /// The types the declaration mentions.
    pub types: Types,
    /// The function's own signature.
    pub signature: Signature,
    /// The name the declaration gave, when it gave one.
    pub name: Option<String>,
    /// The text it was written as. The annotation log stores the source and
    /// parses on read, so this is what came out of the log.
    pub text: String,
}

impl Asserted {
    /// Parse a C function declaration, laid out the way `arch` lays types out.
    pub fn parse(text: &str, arch: &Arch) -> Result<Asserted, cdecl::ParseError> {
        Asserted::parse_into(Types::for_model(model_of(arch)), text)
    }

    /// The same, starting from a store that already holds the program's types,
    /// so a declaration can refer to a structure recovered from debug
    /// information by name.
    pub fn parse_into(mut types: Types, text: &str) -> Result<Asserted, cdecl::ParseError> {
        let (name, signature) = cdecl::prototype(&mut types, text)?;
        Ok(Asserted {
            types,
            signature,
            name,
            text: text.to_string(),
        })
    }
}

/// The widths and alignments an architecture's C compiler uses.
///
/// The container decides this as much as the machine does: the same x86-64
/// code is LP64 under ELF and LLP64 under PE. Only the architecture is known
/// here, so this is the ELF and Mach-O answer and a PE loader that wants the
/// other one passes [`Model::llp64`] itself.
pub fn model_of(arch: &Arch) -> Model {
    match arch {
        Arch::X86_64 => Model::lp64(),
        // A plain `char` is unsigned on ARM, which changes what a comparison
        // against a byte means.
        Arch::AArch64 => Model::lp64().with_unsigned_char(),
        Arch::X86 => Model::ilp32(),
        Arch::Arm => Model::ilp32().with_unsigned_char(),
        _ => Model::lp64(),
    }
}

impl Prototype {
    /// How many arguments in total, for a caller that has to pass them.
    pub fn arity(&self) -> usize {
        if !self.parameters.is_empty() {
            return self.parameters.len();
        }
        self.integer_arguments + self.float_arguments + self.stack_arguments.len()
    }

    /// True when any part of this was written down by a person.
    pub fn is_asserted(&self) -> bool {
        self.origin.arguments == Strength::Asserted
            || self.origin.returns == Strength::Asserted
            || self.origin.varargs == Strength::Asserted
    }
}

/// Recover what a function takes and returns, letting a declaration override
/// what the code says.
///
/// Recovery runs either way, and fills in everything the declaration did not
/// say: an assertion about the parameters leaves the callee-saved analysis
/// alone, because a person writing a prototype has said nothing about that.
/// What the machine found is kept in [`Prototype::recovered`] whenever a
/// declaration displaced it.
pub fn recover_with(f: &SsaFunction, abi: &Abi, asserted: Option<&Asserted>) -> Prototype {
    let machine = recover(f, abi);
    match asserted {
        Some(a) => apply(machine, a, abi),
        None => machine,
    }
}

/// Lay an asserted signature over a recovered prototype.
fn apply(machine: Prototype, asserted: &Asserted, abi: &Abi) -> Prototype {
    let (parameters, mut conflicts, reserved) = classify(&asserted.types, &asserted.signature, abi);

    // The hidden result pointer occupies a register no declared parameter
    // names, so the count is not just what the parameters landed on.
    let integer_arguments = slots_used(&parameters, |s| match s {
        Storage::Integer(n) => Some(*n),
        _ => None,
    })
    .max(reserved);
    let float_arguments = slots_used(&parameters, |s| match s {
        Storage::Float(n) => Some(*n),
        _ => None,
    });
    let mut stack_arguments: Vec<i64> = parameters
        .iter()
        .flat_map(|p| p.storage.iter())
        .filter_map(|s| match s {
            Storage::Stack(o) => Some(*o),
            _ => None,
        })
        .collect();
    stack_arguments.sort();
    stack_arguments.dedup();

    // A register the code reads that the declaration does not account for is
    // not dropped: honour the declaration and say what was set aside.
    for slot in integer_arguments..machine.integer_arguments {
        if let Some(register) = abi.integer_arguments.get(slot) {
            conflicts.push(Conflict::ExtraArgument {
                register: *register,
                slot,
            });
        }
    }
    for slot in float_arguments..machine.float_arguments {
        if let Some(register) = abi.float_arguments.get(slot) {
            conflicts.push(Conflict::ExtraArgument {
                register: *register,
                slot,
            });
        }
    }
    for (index, p) in parameters.iter().enumerate() {
        let read = p.storage.iter().any(|s| match s {
            Storage::Integer(n) => *n < machine.integer_arguments,
            Storage::Float(n) => *n < machine.float_arguments,
            Storage::Stack(o) => machine.stack_arguments.contains(o),
        });
        if !read {
            conflicts.push(Conflict::UnreadArgument { index });
        }
    }

    let (returns, returns_float, mut return_conflicts) =
        classify_return(&asserted.types, &asserted.signature, abi, &machine);
    conflicts.append(&mut return_conflicts);

    Prototype {
        integer_arguments,
        float_arguments,
        stack_arguments,
        returns,
        returns_float,
        // A person writing a prototype has said nothing about which
        // callee-saved registers the body clobbers, so the code keeps these.
        unsaved: machine.unsaved.clone(),
        standard: machine.standard,
        name: asserted.name.clone(),
        return_type: asserted.signature.returns,
        varargs: asserted.signature.varargs,
        returns_via_memory: returns_in_memory(&asserted.types, &asserted.signature),
        origin: Origin {
            arguments: Strength::Asserted,
            returns: Strength::Asserted,
            varargs: Strength::Asserted,
        },
        parameters,
        conflicts,
        recovered: Some(Box::new(machine)),
    }
}

fn slots_used(parameters: &[Parameter], pick: impl Fn(&Storage) -> Option<usize>) -> usize {
    parameters
        .iter()
        .flat_map(|p| p.storage.iter())
        .filter_map(pick)
        .map(|n| n + 1)
        .max()
        .unwrap_or(0)
}

/// Place a declared signature's parameters on the convention's registers.
///
/// This is the common path of the System V and AAPCS rules and not the whole
/// of either: an integer or a pointer takes one integer register, a `float` or
/// `double` takes one vector register, a small aggregate takes as many integer
/// registers as it needs, and anything that does not fit goes on the stack in
/// declaration order. The classification of an aggregate holding floats
/// differs between the two conventions and is not modelled; where this is
/// wrong it is wrong about where a value is, which is reported as a conflict
/// when the code disagrees rather than silently believed.
#[allow(clippy::type_complexity)]
fn classify(types: &Types, sig: &Signature, abi: &Abi) -> (Vec<Parameter>, Vec<Conflict>, usize) {
    let mut out = Vec::new();
    let mut conflicts = Vec::new();
    let mut integers = 0usize;
    let mut floats = 0usize;
    let mut stack = abi.stack_argument_base;

    // A result too large for the registers is returned in memory the caller
    // provides, and the pointer to it arrives as a hidden first argument. It
    // shifts every declared parameter by one register, which is the kind of
    // thing that makes a decompilation wrong everywhere if it is missed.
    let mut reserved = 0usize;
    if returns_in_memory(types, sig) {
        if abi.integer_arguments.is_empty() {
            conflicts.push(Conflict::OffConvention {
                index: None,
                detail: "the result is returned in memory and the convention has no register to pass the address in"
                    .into(),
            });
        } else {
            integers += 1;
            reserved = 1;
        }
    }

    for (index, (name, ty)) in sig.parameters.iter().enumerate() {
        let size = types.size_of(*ty).unwrap_or(0);
        let resolved = types.resolve(*ty);
        let mut storage = Vec::new();

        let wants_float = matches!(types.get(resolved), Some(Type::Float { size: 4 | 8 }));
        if wants_float {
            if abi.float_arguments.is_empty() {
                conflicts.push(Conflict::OffConvention {
                    index: Some(index),
                    detail: "is floating point and the convention passes no arguments in floating point registers"
                        .into(),
                });
            } else if floats < abi.float_arguments.len() {
                storage.push(Storage::Float(floats));
                floats += 1;
            }
        } else {
            let registers = register_count(types, resolved, size, abi);
            if registers > 0 && integers + registers <= abi.integer_arguments.len() {
                for _ in 0..registers {
                    storage.push(Storage::Integer(integers));
                    integers += 1;
                }
            }
        }

        if storage.is_empty() {
            // Everything that did not land in a register lands on the stack,
            // aligned to a slot, in declaration order.
            let slot = abi.stack_argument_base.max(8);
            let width = size.max(1).div_ceil(slot as u64) * slot as u64;
            storage.push(Storage::Stack(stack));
            stack += width as i64;
        }

        out.push(Parameter {
            name: name.clone(),
            ty: *ty,
            size,
            storage,
            strength: Strength::Asserted,
        });
    }
    (out, conflicts, reserved)
}

/// How many integer registers a value of this type occupies, or zero when it
/// does not go in registers at all.
fn register_count(types: &Types, resolved: TypeId, size: u64, abi: &Abi) -> usize {
    let slot = abi.stack_argument_base.max(8) as u64;
    match types.get(resolved) {
        // An aggregate up to two registers wide is passed in them; anything
        // larger is passed in memory by every convention this models.
        Some(Type::Composite(_)) | Some(Type::Array(..)) => {
            if size == 0 || size > 2 * slot {
                0
            } else {
                size.div_ceil(slot) as usize
            }
        }
        // An x87 `long double` is passed in memory on x86-64 and this is the
        // only float wider than a register.
        Some(Type::Float { size }) if *size as u64 > slot => 0,
        Some(Type::Void) | None => 0,
        _ => 1,
    }
}

/// True when the declared result is too large for the result registers.
fn returns_in_memory(types: &Types, sig: &Signature) -> bool {
    let Some(ty) = sig.returns else { return false };
    let resolved = types.resolve(ty);
    if !matches!(
        types.get(resolved),
        Some(Type::Composite(_)) | Some(Type::Array(..))
    ) {
        return false;
    }
    types.size_of(ty).is_none_or(|s| s > 16)
}

/// Where the declared result goes, and how that compares with the code.
fn classify_return(
    types: &Types,
    sig: &Signature,
    abi: &Abi,
    machine: &Prototype,
) -> (Option<u64>, bool, Vec<Conflict>) {
    let mut conflicts = Vec::new();
    let Some(ty) = sig.returns else {
        if let Some(register) = machine.returns {
            conflicts.push(Conflict::ResultDiscarded { register });
        }
        return (None, false, conflicts);
    };

    let resolved = types.resolve(ty);
    let wants_float = matches!(types.get(resolved), Some(Type::Float { size: 4 | 8 }));
    let declared = if wants_float {
        match abi.results.iter().find(|r| **r >= abi.vector_base) {
            Some(r) => Some(*r),
            None => {
                conflicts.push(Conflict::OffConvention {
                    index: None,
                    detail:
                        "is floating point and the convention has no floating point result register"
                            .into(),
                });
                abi.results.first().copied()
            }
        }
    } else {
        match abi.results.iter().find(|r| **r < abi.vector_base) {
            Some(r) => Some(*r),
            None => {
                conflicts.push(Conflict::OffConvention {
                    index: None,
                    detail: "the convention has no integer result register".into(),
                });
                None
            }
        }
    };

    match (declared, machine.returns) {
        (Some(d), Some(w)) if d != w => {
            conflicts.push(Conflict::ResultElsewhere {
                declared: d,
                written: w,
            });
        }
        (Some(_), None) => conflicts.push(Conflict::ResultMissing),
        _ => {}
    }
    (declared, wants_float, conflicts)
}

/// Recover what a function takes and returns.
pub fn recover(f: &SsaFunction, abi: &Abi) -> Prototype {
    let live_in = live_in(f);
    let written = written(f);

    // The highest argument register read, plus one: a function that reads the
    // third and not the first two still takes three.
    let integer_arguments = last_used(&live_in, &abi.integer_arguments);
    let float_arguments = last_used(&live_in, &abi.float_arguments);

    // Arguments the caller left on the stack, which promotion turned into
    // locations above the entry stack pointer.
    let mut stack_arguments: Vec<i64> = live_in
        .iter()
        .filter(|l| l.space == Space::Stack && (l.offset as i64) > 0)
        .map(|l| l.offset as i64)
        .collect();
    stack_arguments.sort();
    stack_arguments.dedup();

    // The result: a register the convention names, written somewhere that
    // reaches a return.
    let returns = returned(f, abi, &written);
    let returns_float = returns.is_some_and(|r| r >= abi.vector_base);

    // A callee-saved register this function writes and does not put back.
    let unsaved: Vec<u64> = abi
        .callee_saved
        .iter()
        .copied()
        .filter(|offset| written.contains(offset) && !restored(f, *offset))
        .collect();

    Prototype {
        integer_arguments,
        float_arguments,
        stack_arguments,
        returns,
        returns_float,
        standard: unsaved.is_empty(),
        unsaved,
        ..Prototype::default()
    }
}

/// Locations read before this function wrote them.
fn live_in(f: &SsaFunction) -> BTreeSet<Location> {
    let mut out = BTreeSet::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            for i in &op.inputs {
                if let Operand::Undefined(l) = i {
                    out.insert(*l);
                }
            }
        }
    }
    out
}

/// Register offsets this function writes.
fn written(f: &SsaFunction) -> BTreeSet<u64> {
    let mut out = BTreeSet::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            // An undefined value is not a write: it says the location holds
            // something this function did not compute.
            if op.kind == SsaKind::Op(Op::Undefine) {
                continue;
            }
            if let Some(v) = op.out {
                if v.location.space == Space::Register {
                    out.insert(v.location.offset);
                }
            }
        }
    }
    out
}

/// One past the last of `candidates` that appears among the live-in set.
fn last_used(live_in: &BTreeSet<Location>, candidates: &[u64]) -> usize {
    candidates
        .iter()
        .enumerate()
        .filter(|(_, offset)| {
            live_in
                .iter()
                .any(|l| l.space == Space::Register && l.offset == **offset)
        })
        .map(|(n, _)| n + 1)
        .next_back()
        .unwrap_or(0)
}

/// Which result register the function leaves a value in, if any.
///
/// The value that reaches a return, when the function computed it. A register
/// still holding what it arrived with was not a result: the caller put it
/// there. The one written latest wins, because a function that computes into a
/// general register and then converts into a vector one writes both.
fn returned(f: &SsaFunction, abi: &Abi, written: &BTreeSet<u64>) -> Option<u64> {
    let definitions = f.definitions();
    let mut best: Option<(usize, u64)> = None;
    for b in f.blocks.values() {
        if !b.ops.iter().any(|op| op.kind == SsaKind::Op(Op::Return)) {
            continue;
        }
        for offset in &abi.results {
            if !written.contains(offset) {
                continue;
            }
            let location = Location {
                space: Space::Register,
                offset: *offset,
                size: 8,
            };
            // What reaches the return: the last definition in this block, or
            // the newest one anywhere when the block itself did not write it.
            let (rank, value) = match b
                .ops
                .iter()
                .enumerate()
                .rev()
                .find(|(_, op)| op.out.is_some_and(|v| v.location == location))
            {
                Some((n, op)) => (n, op.out?),
                None => {
                    let newest = f
                        .blocks
                        .values()
                        .flat_map(|other| other.ops.iter())
                        .filter_map(|op| op.out)
                        .filter(|v| v.location == location)
                        .max_by_key(|v| v.version)?;
                    (0, newest)
                }
            };
            if is_entry_value(f, &definitions, value, location, 0) {
                continue;
            }
            if best.is_none_or(|(at, _)| rank > at) {
                best = Some((rank, *offset));
            }
        }
    }
    best.map(|(_, offset)| offset)
}

/// True when a register's value at every return is the one it arrived with.
fn restored(f: &SsaFunction, offset: u64) -> bool {
    let location = Location {
        space: Space::Register,
        offset,
        size: 8,
    };
    let definitions = f.definitions();
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
                if !is_entry_value(f, &definitions, v, location, 0) {
                    return false;
                }
            }
        }
    }
    true
}

/// True when a value is the one the function was entered with, however many
/// copies and merges it came through.
fn is_entry_value(
    f: &SsaFunction,
    definitions: &BTreeMap<crate::ssa::Value, (r12e_core::Addr, usize)>,
    value: crate::ssa::Value,
    location: Location,
    depth: u32,
) -> bool {
    if depth > 16 {
        return false;
    }
    let Some((block, index)) = definitions.get(&value) else {
        return false;
    };
    let Some(op) = f.blocks.get(block).and_then(|b| b.ops.get(*index)) else {
        return false;
    };
    let inputs: Vec<&Operand> = match op.kind {
        SsaKind::Phi => op.inputs.iter().collect(),
        SsaKind::Op(Op::Copy) | SsaKind::Op(Op::Load) => op.inputs.iter().take(1).collect(),
        _ => return false,
    };
    // A load restores a spilled register: what it reads is not tracked, so a
    // reload of the same location counts as a restore only when the function
    // spilled it first. Treating a load as a restore is the assumption a
    // prologue and epilogue actually satisfy.
    if op.kind == SsaKind::Op(Op::Load) {
        return true;
    }
    inputs.iter().all(|i| match i {
        Operand::Undefined(l) => *l == location,
        Operand::Value(v) => is_entry_value(f, definitions, *v, location, depth + 1),
        Operand::Const(..) => false,
    })
}
