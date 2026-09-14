//! Turning decoded instructions into IR.
//!
//! One lifter per architecture, each producing operations with no implicit
//! effects. A machine instruction that sets four flags becomes four operations,
//! because dataflow that has to know which instruction touches which flag is
//! dataflow with a bug in it.
//!
//! An instruction the lifter does not model produces a single
//! [`Op::Unimplemented`], which stops the interpreter and is visible in the
//! coverage number. Producing nothing, or producing something approximate,
//! would make a wrong answer look like a right one.

pub mod aarch64;
pub mod arm;
pub mod neon;
pub mod sse;
pub mod x86;

use r12e_arch::Insn;
use r12e_core::Arch;

use crate::op::{IrOp, Op, Varnode};

/// The most temporaries one instruction's lifting may use. Block building
/// shifts each instruction's temporaries by this much so they stay distinct.
pub const MAX_TEMPS: u64 = 64;

/// The IR for one machine instruction.
#[derive(Debug, Clone, Default)]
pub struct Lifted {
    /// The operations, in order.
    pub ops: Vec<IrOp>,
    /// True when the instruction was modelled completely.
    pub complete: bool,
}

impl Lifted {
    /// True when nothing was produced.
    pub fn is_empty(&self) -> bool {
        self.ops.is_empty()
    }
}

/// A builder that hands out temporaries and collects operations.
pub struct Builder {
    addr: r12e_core::Addr,
    ops: Vec<IrOp>,
    next_temp: u64,
    /// How wide a pointer is on the machine this came from.
    ///
    /// The same instruction set is lifted at two widths -- x86 in long mode
    /// and in protected mode -- and every address, stack adjustment and return
    /// address differs by exactly this. Carrying it here rather than in each
    /// lifter's own threading keeps one number in one place.
    pub ptr: u8,
}

impl Builder {
    /// A builder for the instruction at `addr`, on a 64-bit machine.
    pub fn new(addr: r12e_core::Addr) -> Builder {
        Builder::sized(addr, 8)
    }

    /// The same, for a machine whose pointers are `ptr` bytes.
    pub fn sized(addr: r12e_core::Addr, ptr: u8) -> Builder {
        Builder {
            addr,
            ops: Vec::new(),
            next_temp: 0,
            ptr,
        }
    }

    /// A fresh temporary of `size` bytes.
    pub fn temp(&mut self, size: u8) -> Varnode {
        // Wrapping rather than growing without bound: no instruction needs
        // this many, and a runaway lifter should not silently corrupt another
        // instruction's temporaries.
        let v = Varnode::temp(self.next_temp % MAX_TEMPS, size);
        self.next_temp += 1;
        v
    }

    /// Emit an operation.
    pub fn emit(&mut self, op: Op, out: Option<Varnode>, inputs: &[Varnode]) {
        let mut ir = IrOp::new(self.addr, op, out);
        for i in inputs {
            ir = ir.with(*i);
        }
        self.ops.push(ir);
    }

    /// Emit an operation into a fresh temporary and return it.
    pub fn eval(&mut self, op: Op, size: u8, inputs: &[Varnode]) -> Varnode {
        let t = self.temp(size);
        self.emit(op, Some(t), inputs);
        t
    }

    /// Finish, saying whether the instruction was modelled completely.
    pub fn finish(self, complete: bool) -> Lifted {
        Lifted {
            ops: self.ops,
            complete,
        }
    }

    /// Finish a complete instruction without consuming the builder, for a
    /// lifter that decides as it goes whether it handled the instruction.
    pub fn clone_finish(&self) -> Lifted {
        Lifted {
            ops: self.ops.clone(),
            complete: true,
        }
    }

    /// Give up on this instruction, honestly.
    pub fn unimplemented(mut self) -> Lifted {
        self.emit(Op::Unimplemented, None, &[]);
        Lifted {
            ops: self.ops,
            complete: false,
        }
    }
}

/// Lift one instruction.
pub fn lift(arch: &Arch, insn: &Insn) -> Lifted {
    match arch {
        Arch::AArch64 => aarch64::lift(insn),
        Arch::X86_64 => x86::lift(insn),
        Arch::X86 => x86::lift32(insn),
        Arch::Arm => arm::lift(insn),
        _ => Builder::new(insn.addr).unimplemented(),
    }
}
