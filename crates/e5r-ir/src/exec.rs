//! Running lifted code.
//!
//! Decode, lift, interpret, one machine instruction at a time. This is the
//! harness the lifter tests use: compile a function, run it here, and compare
//! against the answer computed independently. A lifter cannot be checked by
//! reading it.

use e5r_core::{Addr, Arch, MemoryMap};

use crate::interp::{Machine, Step, Stop, step};
use crate::lift;

/// How a run ended, and what it did on the way.
#[derive(Debug, Clone)]
pub struct Outcome {
    /// Why it stopped.
    pub stop: Stop,
    /// Machine instructions executed.
    pub insns: u64,
    /// IR operations executed.
    pub ops: u64,
    /// Instructions the lifter did not model, by address.
    pub unlifted: Vec<Addr>,
}

impl Outcome {
    /// True when the run ended by returning, with nothing unmodelled.
    pub fn returned_cleanly(&self) -> bool {
        self.stop == Stop::Returned && self.unlifted.is_empty()
    }
}

/// Run from `entry` until the code returns or the budget runs out, without
/// following calls: a call stops the run and reports its target.
pub fn run(m: &mut Machine<'_>, image: &MemoryMap, arch: &Arch, entry: Addr) -> Outcome {
    run_with(m, image, arch, entry, 0)
}

/// Run, following calls up to `depth` frames deep.
///
/// Following calls is what makes a function that uses a helper, or recurses,
/// testable at all; the depth limit is what keeps a runaway from being
/// indistinguishable from a hang.
pub fn run_with(
    m: &mut Machine<'_>,
    image: &MemoryMap,
    arch: &Arch,
    entry: Addr,
    depth: u32,
) -> Outcome {
    let mut pc = entry;
    let mut insns = 0u64;
    let mut ops = 0u64;
    let mut unlifted = Vec::new();
    let mut budget = m.budget;
    let mut frames = 0u32;

    loop {
        if budget == 0 {
            return Outcome {
                stop: Stop::Budget,
                insns,
                ops,
                unlifted,
            };
        }
        let Some(window) = image.decode_window(pc, arch.max_insn_len()) else {
            return Outcome {
                stop: Stop::NoCode(pc),
                insns,
                ops,
                unlifted,
            };
        };
        let Some(insn) = e5r_arch::decode(arch, window, pc) else {
            return Outcome {
                stop: Stop::NoCode(pc),
                insns,
                ops,
                unlifted,
            };
        };
        let lifted = lift::lift(arch, &insn);
        if !lifted.complete {
            unlifted.push(pc);
        }

        m.end_instruction();
        let mut next = insn.next();
        let mut jumped = false;
        for ir in &lifted.ops {
            budget = budget.saturating_sub(1);
            ops += 1;
            match step(m, ir) {
                Step::Next => {}
                Step::Jump(t) => {
                    next = t;
                    jumped = true;
                    break;
                }
                Step::Call(target) => {
                    if frames >= depth {
                        return Outcome {
                            stop: Stop::Call(target),
                            insns: insns + 1,
                            ops,
                            unlifted,
                        };
                    }
                    frames += 1;
                    next = target;
                    jumped = true;
                    break;
                }
                Step::Leave(target) => {
                    if frames == 0 {
                        return Outcome {
                            stop: Stop::Returned,
                            insns: insns + 1,
                            ops,
                            unlifted,
                        };
                    }
                    frames -= 1;
                    next = target;
                    jumped = true;
                    break;
                }
                Step::Halt(s) => {
                    return Outcome {
                        stop: s,
                        insns: insns + 1,
                        ops,
                        unlifted,
                    };
                }
            }
        }
        let _ = jumped;
        insns += 1;
        pc = next;
    }
}
