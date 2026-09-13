//! Running a function.
//!
//! The interpreter the lifters are tested against, offered as a tool. Set the
//! arguments, run, and report what came back and what the run touched. It is
//! the same machine the semantics gate uses, so what it says a function
//! computes is what that gate has been checking against real hardware.
//!
//! Nothing here escapes the process: memory is a map that starts as the
//! image's own bytes, a system call stops the run rather than being made, and
//! the budget bounds it.

use std::collections::BTreeMap;

use r12e_analysis::{Function, Program};
use r12e_core::Addr;
use r12e_ir::{Machine, Stop};

/// What a run did.
#[derive(Debug, Clone)]
pub struct Run {
    /// Why it stopped.
    pub stop: Stop,
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
}

impl Run {
    /// True when the function returned with nothing unmodelled.
    pub fn clean(&self) -> bool {
        self.stop == Stop::Returned && self.unlifted.is_empty()
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
        }
    }
}

/// Run one function.
pub fn run(p: &Program, f: &Function, setup: &Setup) -> Run {
    let abi = r12e_ir::abi::of(&p.object.arch);
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
    let reserved = match p.object.arch {
        r12e_core::Arch::X86_64 => 8,
        _ => 0,
    };
    for (n, a) in setup.arguments.iter().skip(registers).enumerate() {
        m.write_mem(setup.stack + reserved + n as u64 * 8, &a.to_le_bytes());
    }
    // Somewhere that is not code, so the outermost return stops the run.
    const SENTINEL: u64 = 0xdead_0000;
    match p.object.arch {
        r12e_core::Arch::X86_64 => m.write_mem(setup.stack, &SENTINEL.to_le_bytes()),
        _ => m.set_reg(r12e_ir::lift::aarch64::gpr_offset(30), 8, SENTINEL),
    }

    let before = m.written().clone();
    let outcome = r12e_ir::run_with(
        &mut m,
        &p.object.memory,
        &p.object.arch,
        f.entry,
        setup.depth,
    );
    let result = m.reg(abi.results.first().copied().unwrap_or(0), 8);
    let written = m
        .written()
        .iter()
        .filter(|(a, v)| before.get(a) != Some(v))
        .map(|(a, v)| (*a, *v))
        .collect();

    Run {
        stop: outcome.stop,
        result,
        insns: outcome.insns,
        ops: outcome.ops,
        unlifted: outcome.unlifted,
        written,
    }
}
