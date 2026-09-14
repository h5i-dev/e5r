//! Running a function, and what that settles.
//!
//! The interpreter the lifters are tested against, offered as a tool. Set the
//! arguments, place whatever memory the code expects, run, and report what came
//! back, where every indirect branch went, and which system calls were taken.
//! It is the same machine the semantics gate uses, so what it says a function
//! computes is what that gate has been checking against real hardware.
//!
//! Three things this is for, and each one is a question static analysis cannot
//! answer on its own:
//!
//! * **A string that only exists at run time.** A decryptor is a small
//!   self-contained routine, and running it and reading the buffer back is the
//!   only way to see what it produces. [`Setup::inputs`] places the buffer,
//!   [`Setup::watch`] reads it back.
//! * **A control flow that is computed.** [`Run::branches`] says where each
//!   indirect branch actually went, and [`resolve`] turns a set of runs into
//!   edges that carry the inputs they were observed under, which is the whole
//!   of the evidence for them.
//! * **A jump table that was inferred.** [`confirm`] runs the switch once per
//!   index and reports which of the recovered targets execution actually
//!   reached, which turns a pattern match into a checked answer.
//!
//! Nothing here escapes the process. Memory is a map that starts as the image's
//! own bytes; a system call is answered by a stub that performs no action at
//! all, or refused by number; and the budget bounds the whole thing. See
//! [`crate::kernel`] for exactly what a stub is allowed to do.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use r12e_analysis::{Function, JumpTable, Program};
use r12e_core::{Addr, Arch, MemoryMap};
use r12e_ir::{Machine, Op, Stop};

use crate::kernel::{self, Answer, Call, Kernel, Output, Session};

/// The most bytes one [`Span`] captures. A span longer than this is truncated
/// rather than allowed to turn a typo into an allocation.
pub const MAX_WATCH: u64 = 1 << 22;

/// Why a run ended.
///
/// A superset of the interpreter's own [`Stop`]: emulation here can also end
/// because the program asked to exit, because a system call had no stub, or
/// because the caller asked to stop at an indirect branch, and none of those
/// has an interpreter word for it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ending {
    /// The function returned to its caller.
    Returned,
    /// The program called `exit`, with this status.
    Exited(u64),
    /// The operation budget ran out, which is how a loop that does not
    /// terminate is reported rather than hung on.
    Budget,
    /// An instruction the lifter does not model was reached.
    Unimplemented(Addr),
    /// Control went somewhere with no code.
    NoCode(Addr),
    /// A call was reached and calls were not being followed that deep.
    Call(Addr),
    /// Division by zero.
    DivideByZero(Addr),
    /// A system call with no stub. Reported by number, never answered with a
    /// plausible value.
    Syscall {
        /// The instruction that made it.
        at: Addr,
        /// The number in the architecture's system call register.
        number: u64,
        /// What that number is called, where the table knows a name.
        name: Option<&'static str>,
    },
    /// The indirect transfer [`Setup::stop_at_indirect`] named resolved, and
    /// the run stopped there rather than going on into the target.
    Indirect {
        /// The branching instruction.
        at: Addr,
        /// Where it went.
        to: Addr,
    },
}

impl Ending {
    /// True when the run ended of its own accord rather than being cut off.
    pub fn finished(&self) -> bool {
        matches!(self, Ending::Returned | Ending::Exited(_))
    }

    /// The nearest thing the interpreter has a word for.
    ///
    /// This exists so [`Run::stop`] can go on meaning what it meant. It loses
    /// information on purpose and [`Run::ending`] is the answer to trust: an
    /// exit reads as a return, a refused system call reads as an instruction
    /// the model does not have, and a deliberate stop at an indirect branch
    /// reads as a transfer that was not followed.
    pub fn as_stop(&self) -> Stop {
        match self {
            Ending::Returned | Ending::Exited(_) => Stop::Returned,
            Ending::Budget => Stop::Budget,
            Ending::Unimplemented(a) => Stop::Unimplemented(*a),
            Ending::NoCode(a) => Stop::NoCode(*a),
            Ending::Call(a) => Stop::Call(*a),
            Ending::DivideByZero(a) => Stop::DivideByZero(*a),
            Ending::Syscall { at, .. } => Stop::Unimplemented(*at),
            Ending::Indirect { to, .. } => Stop::Call(*to),
        }
    }
}

impl fmt::Display for Ending {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ending::Returned => write!(f, "returned"),
            Ending::Exited(s) => write!(f, "exited with status {s}"),
            Ending::Budget => write!(f, "ran out of budget"),
            Ending::Unimplemented(a) => write!(f, "unmodelled instruction at {a}"),
            Ending::NoCode(a) => write!(f, "no code at {a}"),
            Ending::Call(a) => write!(f, "call to {a}, not followed"),
            Ending::DivideByZero(a) => write!(f, "divide by zero at {a}"),
            Ending::Syscall { at, number, name } => match name {
                Some(n) => write!(f, "system call {n} ({number}) at {at} has no stub"),
                None => write!(f, "system call {number} at {at} has no stub"),
            },
            Ending::Indirect { at, to } => write!(f, "indirect branch at {at} went to {to}"),
        }
    }
}

/// Where an indirect transfer actually went.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Indirect {
    /// The branching instruction.
    pub at: Addr,
    /// Where control went.
    pub to: Addr,
    /// True when it was a call rather than a branch.
    pub call: bool,
}

/// Bytes to put in the machine's memory before the run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Place {
    /// Where they go.
    pub at: u64,
    /// The bytes.
    pub bytes: Vec<u8>,
}

/// A span of memory to capture when the run stops.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    /// Where it starts.
    pub at: u64,
    /// How long it is, capped at [`MAX_WATCH`].
    pub len: u64,
}

/// A captured span, as it stood when the run stopped.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Region {
    /// Where it starts.
    pub at: u64,
    /// The bytes.
    pub bytes: Vec<u8>,
}

/// What a run did.
#[derive(Debug, Clone)]
pub struct Run {
    /// Why it stopped, as the interpreter would put it.
    ///
    /// [`Ending::as_stop`] explains what this loses; [`Run::ending`] is the
    /// field to read when the difference matters.
    pub stop: Stop,
    /// Why it stopped.
    pub ending: Ending,
    /// What the result register held when it did.
    pub result: u64,
    /// Machine instructions executed.
    pub insns: u64,
    /// IR operations executed.
    pub ops: u64,
    /// Instructions the lifter did not model, in the order they were reached.
    pub unlifted: Vec<Addr>,
    /// Memory the run wrote, by address.
    pub written: BTreeMap<u64, u8>,
    /// The spans [`Setup::watch`] asked for, in that order.
    pub regions: Vec<Region>,
    /// Every system call reached, stubbed or refused, in order.
    ///
    /// This is how a run that took a stub is told apart from one that did not.
    /// A `read` that returned zero bytes because no file exists is a different
    /// answer from a `read` that was never made, and both leave the same
    /// registers behind.
    pub syscalls: Vec<Call>,
    /// Bytes a stubbed `write` was handed. Nothing was written anywhere.
    pub output: Vec<Output>,
    /// Where each indirect branch and indirect call went, in order.
    pub branches: Vec<Indirect>,
}

impl Run {
    /// True when the function returned with nothing unmodelled and no system
    /// call stubbed.
    ///
    /// A stub is a decision about what the kernel would have done, so a run
    /// that took one is not a clean reading of the code alone even when it
    /// returned. [`Run::ending`] and [`Run::syscalls`] say which of the three
    /// it was.
    pub fn clean(&self) -> bool {
        self.ending == Ending::Returned && self.unlifted.is_empty() && self.syscalls.is_empty()
    }

    /// True when any system call was answered by a stub.
    pub fn stubbed(&self) -> bool {
        self.syscalls.iter().any(|c| c.stubbed)
    }

    /// A watched span's bytes.
    pub fn region(&self, at: u64) -> Option<&[u8]> {
        self.regions
            .iter()
            .find(|r| r.at == at)
            .map(|r| r.bytes.as_slice())
    }

    /// The NUL-terminated text at `at`, when a watched span covers it.
    ///
    /// `None` rather than replacement characters when the bytes are not UTF-8:
    /// a decryption that came out wrong must not be laundered into something
    /// that looks like a string.
    pub fn text(&self, at: u64) -> Option<String> {
        let r = self
            .regions
            .iter()
            .find(|r| r.at <= at && at < r.at + r.bytes.len() as u64)?;
        let from = &r.bytes[(at - r.at) as usize..];
        let end = from.iter().position(|b| *b == 0).unwrap_or(from.len());
        String::from_utf8(from[..end].to_vec()).ok()
    }

    /// Everything a stubbed `write` was handed, concatenated.
    pub fn written_out(&self) -> Vec<u8> {
        self.output.iter().flat_map(|o| o.bytes.clone()).collect()
    }
}

/// How to set a run up.
#[derive(Debug, Clone)]
pub struct Setup {
    /// Integer arguments, in the convention's order.
    pub arguments: Vec<u64>,
    /// How deep to follow calls.
    pub depth: u32,
    /// How many IR operations to allow.
    pub budget: u64,
    /// Where the stack goes.
    pub stack: u64,
    /// Bytes to place before the run: a buffer to decrypt into, a structure the
    /// code expects to find, a ciphertext that lives somewhere else.
    pub inputs: Vec<Place>,
    /// Spans to capture when the run stops.
    pub watch: Vec<Span>,
    /// What the system call stubs answer with.
    pub kernel: Kernel,
    /// Stop when the indirect transfer at this address resolves, rather than
    /// going on into the target.
    ///
    /// This is what makes confirming a jump table cheap: the target is the
    /// answer, and running the case body afterwards can only add ways to fail.
    pub stop_at_indirect: Option<Addr>,
}

impl Default for Setup {
    fn default() -> Self {
        Setup {
            arguments: Vec::new(),
            depth: 64,
            budget: 1 << 22,
            // Away from the image, so a stray read is visibly unmapped rather
            // than quietly reading code.
            stack: 0x7fff_0000,
            inputs: Vec::new(),
            watch: Vec::new(),
            kernel: Kernel::default(),
            stop_at_indirect: None,
        }
    }
}

/// Run one function.
pub fn run(p: &Program, f: &Function, setup: &Setup) -> Run {
    let arch = &p.object.arch;
    let abi = r12e_ir::abi::of(arch);
    let mut m = Machine::over(&p.object.memory);
    m.budget = setup.budget;
    // Real storage under the stack pointer, so a spill and its reload agree.
    m.write_mem(setup.stack - 0x8000, &[0u8; 0x10000]);

    let registers = abi.integer_arguments.len();
    for (i, a) in setup.arguments.iter().enumerate().take(registers) {
        m.set_reg(abi.integer_arguments[i], 8, *a);
    }
    m.set_reg(abi.stack_pointer, 8, setup.stack);
    // Arguments past the registers go on the stack, above the return address
    // on the architectures that push one.
    let reserved = match arch {
        Arch::X86_64 => 8,
        _ => 0,
    };
    for (n, a) in setup.arguments.iter().skip(registers).enumerate() {
        m.write_mem(setup.stack + reserved + n as u64 * 8, &a.to_le_bytes());
    }
    // Somewhere that is not code, so the outermost return stops the run.
    const SENTINEL: u64 = 0xdead_0000;
    match arch {
        Arch::X86_64 => m.write_mem(setup.stack, &SENTINEL.to_le_bytes()),
        _ => m.set_reg(r12e_ir::lift::aarch64::gpr_offset(30), 8, SENTINEL),
    }
    // The caller's own bytes go in last, so they win over the stack fill if a
    // caller deliberately places something inside the frame.
    for place in &setup.inputs {
        m.write_mem(place.at, &place.bytes);
    }

    let before = m.written().clone();
    let mut session = Session::new(setup.kernel.clone());
    let walk = walk(&mut m, &mut session, &p.object.memory, arch, setup, f.entry);

    let result = m.reg(abi.results.first().copied().unwrap_or(0), 8);
    let regions = setup
        .watch
        .iter()
        .map(|s| {
            let len = s.len.min(MAX_WATCH);
            let bytes = (0..len).map(|i| m.read_mem(s.at + i, 1) as u8).collect();
            Region { at: s.at, bytes }
        })
        .collect();
    let written = m
        .written()
        .iter()
        .filter(|(a, v)| before.get(a) != Some(v))
        .map(|(a, v)| (*a, *v))
        .collect();

    Run {
        stop: walk.ending.as_stop(),
        ending: walk.ending,
        result,
        insns: walk.insns,
        ops: walk.ops,
        unlifted: walk.unlifted,
        written,
        regions,
        syscalls: walk.syscalls,
        output: session.output,
        branches: walk.branches,
    }
}

/// What one walk of the code produced.
struct Walk {
    ending: Ending,
    insns: u64,
    ops: u64,
    unlifted: Vec<Addr>,
    syscalls: Vec<Call>,
    branches: Vec<Indirect>,
}

/// Decode, lift, interpret, one instruction at a time.
///
/// This is the interpreter's own loop with two things added: a system call goes
/// to the stubs instead of falling through with an undefined result, and an
/// indirect transfer records where it went. Neither belongs in the IR crate,
/// which has no business knowing what Linux is.
fn walk(
    m: &mut Machine<'_>,
    session: &mut Session,
    image: &MemoryMap,
    arch: &Arch,
    setup: &Setup,
    entry: Addr,
) -> Walk {
    let mut w = Walk {
        ending: Ending::Budget,
        insns: 0,
        ops: 0,
        unlifted: Vec::new(),
        syscalls: Vec::new(),
        branches: Vec::new(),
    };
    let mut pc = entry;
    let mut budget = setup.budget;
    let mut frames = 0u32;

    loop {
        if budget == 0 {
            w.ending = Ending::Budget;
            return w;
        }
        let Some(insn) = r12e_ir::func::decode_at(image, arch, pc) else {
            w.ending = Ending::NoCode(pc);
            return w;
        };
        let lifted = r12e_ir::lift::lift(arch, &insn);
        if !lifted.complete {
            w.unlifted.push(pc);
        }

        m.end_instruction();
        let mut next = insn.next();
        let gate = gate(arch, insn.mnemonic);

        for ir in &lifted.ops {
            budget = budget.saturating_sub(1);
            w.ops += 1;
            let indirect = matches!(ir.op, Op::BranchInd | Op::CallInd);
            match r12e_ir::step(m, ir) {
                r12e_ir::Step::Next => {}
                r12e_ir::Step::Jump(t) => {
                    if indirect {
                        w.branches.push(Indirect {
                            at: ir.addr,
                            to: t,
                            call: false,
                        });
                        if setup.stop_at_indirect == Some(ir.addr) {
                            w.insns += 1;
                            w.ending = Ending::Indirect { at: ir.addr, to: t };
                            return w;
                        }
                    }
                    next = t;
                    break;
                }
                r12e_ir::Step::Call(target) => {
                    if indirect {
                        w.branches.push(Indirect {
                            at: ir.addr,
                            to: target,
                            call: true,
                        });
                        if setup.stop_at_indirect == Some(ir.addr) {
                            w.insns += 1;
                            w.ending = Ending::Indirect {
                                at: ir.addr,
                                to: target,
                            };
                            return w;
                        }
                    }
                    if frames >= setup.depth {
                        w.insns += 1;
                        w.ending = Ending::Call(target);
                        return w;
                    }
                    frames += 1;
                    next = target;
                    break;
                }
                r12e_ir::Step::Leave(target) => {
                    if frames == 0 {
                        w.insns += 1;
                        w.ending = Ending::Returned;
                        return w;
                    }
                    frames -= 1;
                    next = target;
                    break;
                }
                r12e_ir::Step::Halt(s) => {
                    w.insns += 1;
                    w.ending = from_stop(s);
                    return w;
                }
            }
        }
        w.insns += 1;

        // The lifting of a system call says what the instruction did to the
        // register file and stops there, because what the kernel does is not
        // knowable from the instruction. That is the hole the stubs fill, and
        // it has to be filled here rather than in the lifter: the lifter is a
        // statement about the architecture and this is a statement about an
        // operating system.
        match gate {
            None => {}
            Some(Gate::Other) => {
                // A hypervisor call or a 32-bit gate. It is a system call by
                // flow and nothing here models it, so the run stops rather
                // than walking on into the next instruction as if it had run.
                w.ending = Ending::Unimplemented(pc);
                return w;
            }
            Some(Gate::Linux) => {
                let mut call = Session::observe(m, arch, pc);
                match session.serve(m, arch, &call) {
                    Answer::Returned(v) => {
                        call.stubbed = true;
                        call.returned = Some(v);
                        m.set_reg(kernel::result_register(arch), 8, v);
                        w.syscalls.push(call);
                    }
                    Answer::Exited(status) => {
                        call.stubbed = true;
                        w.syscalls.push(call);
                        w.ending = Ending::Exited(status);
                        return w;
                    }
                    Answer::Refused => {
                        let ending = Ending::Syscall {
                            at: pc,
                            number: call.number,
                            name: call.name,
                        };
                        w.syscalls.push(call);
                        w.ending = ending;
                        return w;
                    }
                }
            }
        }

        pc = next;
    }
}

/// What the interpreter's own stop reasons become.
fn from_stop(s: Stop) -> Ending {
    match s {
        Stop::Returned => Ending::Returned,
        Stop::Budget => Ending::Budget,
        Stop::Unimplemented(a) => Ending::Unimplemented(a),
        Stop::NoCode(a) => Ending::NoCode(a),
        Stop::Call(a) => Ending::Call(a),
        Stop::DivideByZero(a) => Ending::DivideByZero(a),
    }
}

/// Which kind of gate into the kernel an instruction is, if any.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Gate {
    /// The Linux system call instruction for this architecture.
    Linux,
    /// A gate by flow that is not one: a hypervisor call, a secure monitor
    /// call, or the 32-bit entries on x86.
    Other,
}

fn gate(arch: &Arch, mnemonic: &str) -> Option<Gate> {
    match arch {
        Arch::X86_64 => match mnemonic {
            "syscall" => Some(Gate::Linux),
            "int" | "sysenter" => Some(Gate::Other),
            _ => None,
        },
        Arch::AArch64 => match mnemonic {
            "svc" => Some(Gate::Linux),
            "hvc" | "smc" => Some(Gate::Other),
            _ => None,
        },
        _ => None,
    }
}

/// An indirect edge an execution settled, and the evidence for it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Resolved {
    /// The branching instruction.
    pub at: Addr,
    /// Where it went.
    pub to: Addr,
    /// True when it was a call rather than a branch.
    pub call: bool,
    /// Every argument vector a run took this edge under.
    ///
    /// This is the whole of the evidence and it is deliberately not thrown
    /// away. An executed edge is a statement that control went here for these
    /// inputs, which is a weaker and more honest thing than a claim that the
    /// branch has this target: the edges an obfuscator hides are exactly the
    /// ones whose target depends on something.
    pub under: Vec<Vec<u64>>,
}

/// Run a function once per argument vector and collect the indirect edges.
///
/// This is how a flattened or opaquely-predicated control flow is opened up:
/// the targets are computed, so computing them is the only way to see them, and
/// the set that comes back is the set those inputs reached and no larger.
pub fn resolve(p: &Program, f: &Function, setup: &Setup, inputs: &[Vec<u64>]) -> Vec<Resolved> {
    let mut found: BTreeMap<(Addr, Addr, bool), Vec<Vec<u64>>> = BTreeMap::new();
    for args in inputs {
        let s = Setup {
            arguments: args.clone(),
            ..setup.clone()
        };
        let run = run(p, f, &s);
        let mut seen = BTreeSet::new();
        for b in &run.branches {
            if seen.insert((b.at, b.to, b.call)) {
                found
                    .entry((b.at, b.to, b.call))
                    .or_default()
                    .push(args.clone());
            }
        }
    }
    found
        .into_iter()
        .map(|((at, to, call), under)| Resolved {
            at,
            to,
            call,
            under,
        })
        .collect()
}

/// What running a switch said about a recovered jump table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Confirmed {
    /// The indirect branch the table resolves.
    pub at: Addr,
    /// Where the branch went, per index that reached it.
    pub taken: BTreeMap<u64, Addr>,
    /// Indices whose run never reached the branch, which is what a guard
    /// rejecting an out-of-range index looks like from here.
    pub rejected: Vec<u64>,
    /// Targets execution reached, sorted.
    pub reached: BTreeSet<Addr>,
    /// Targets the table claims that no index reached.
    ///
    /// A table sized by scanning rather than by the guard collects these: the
    /// entries past the real end are plausible addresses that nothing selects.
    pub unreached: Vec<Addr>,
    /// Targets execution reached that the table does not claim, which would
    /// mean recovery stopped short.
    pub extra: Vec<Addr>,
}

impl Confirmed {
    /// True when execution reached every target the table claims and no other.
    pub fn agrees(&self) -> bool {
        self.unreached.is_empty() && self.extra.is_empty()
    }
}

/// Run a switch once per index and report what the indirect branch did.
///
/// `slot` is which integer argument carries the switch value; the rest of
/// [`Setup::arguments`] is passed through unchanged, so a function that takes
/// the value alongside other arguments still runs.
///
/// Recovery bounds a table by the compare that guards the switch, and where
/// that compare cannot be found every byte of a compact table yields a
/// plausible target. Running the branch is the check that tells the two apart:
/// a target nothing selects is reported in [`Confirmed::unreached`] rather than
/// believed.
pub fn confirm(
    p: &Program,
    f: &Function,
    table: &JumpTable,
    setup: &Setup,
    slot: usize,
    indices: &[u64],
) -> Confirmed {
    let mut taken = BTreeMap::new();
    let mut rejected = Vec::new();
    let mut reached = BTreeSet::new();

    for i in indices {
        let mut arguments = setup.arguments.clone();
        if arguments.len() <= slot {
            arguments.resize(slot + 1, 0);
        }
        arguments[slot] = *i;
        let s = Setup {
            arguments,
            stop_at_indirect: Some(table.at),
            ..setup.clone()
        };
        let run = run(p, f, &s);
        match run.branches.iter().find(|b| b.at == table.at) {
            Some(b) => {
                taken.insert(*i, b.to);
                reached.insert(b.to);
            }
            None => rejected.push(*i),
        }
    }

    let claimed: BTreeSet<Addr> = table.targets.iter().copied().collect();
    Confirmed {
        at: table.at,
        taken,
        rejected,
        unreached: claimed.difference(&reached).copied().collect(),
        extra: reached.difference(&claimed).copied().collect(),
        reached,
    }
}
