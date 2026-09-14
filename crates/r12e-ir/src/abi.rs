//! What the calling convention says, per architecture.
//!
//! Two passes need this and neither can work without it. Dead code elimination
//! has to know which registers the caller may read after a return, or it
//! deletes the result. The decompiler has to know which registers arrive with
//! values, or every function takes no arguments.
//!
//! This is the default convention, not a recovered one. A function that does
//! something else is M4's per-function detection, which this is the floor for.

use r12e_core::Arch;

use crate::lift::{aarch64, x86};
use crate::op::Space;
use crate::ssa::Location;

/// The registers a convention uses, as byte offsets into the register file.
#[derive(Debug, Clone)]
pub struct Abi {
    /// Integer argument registers, in order.
    pub integer_arguments: Vec<u64>,
    /// Floating point argument registers, in order.
    pub float_arguments: Vec<u64>,
    /// Registers holding the result.
    pub results: Vec<u64>,
    /// Registers the callee must restore, so the caller may read them after.
    pub callee_saved: Vec<u64>,
    /// Registers a call may leave holding anything.
    pub caller_saved: Vec<u64>,
    /// The stack pointer.
    pub stack_pointer: u64,
    /// Where the vector registers start, for naming.
    pub vector_base: u64,
    /// Offset from the entry stack pointer of the first argument passed there.
    ///
    /// x86 pushes the return address as part of the call, so its stack
    /// arguments start one slot past the entry pointer; AArch64 puts the
    /// return address in a register and starts at zero.
    pub stack_argument_base: i64,
}

impl Abi {
    /// The locations live when a function returns: the result and everything
    /// the caller is entitled to find unchanged.
    pub fn live_at_return(&self) -> Vec<Location> {
        let mut out: Vec<Location> = self
            .results
            .iter()
            .chain(self.callee_saved.iter())
            .map(|offset| Location {
                space: Space::Register,
                offset: *offset,
                size: 8,
            })
            .collect();
        out.push(Location {
            space: Space::Register,
            offset: self.stack_pointer,
            size: 8,
        });
        out
    }

    /// The name an incoming value gets, when it arrives in a register the
    /// convention passes arguments in.
    pub fn argument_name(&self, offset: u64) -> Option<String> {
        if let Some(n) = self.integer_arguments.iter().position(|o| *o == offset) {
            return Some(format!("arg{n}"));
        }
        if let Some(n) = self.float_arguments.iter().position(|o| *o == offset) {
            return Some(format!("farg{n}"));
        }
        None
    }
}

/// The default convention for an architecture.
pub fn of(arch: &Arch) -> Abi {
    match arch {
        Arch::X86_64 => Abi {
            // System V: rdi, rsi, rdx, rcx, r8, r9.
            integer_arguments: [7u8, 6, 2, 1, 8, 9]
                .iter()
                .map(|n| x86::gpr_offset(*n))
                .collect(),
            float_arguments: (0..8).map(x86::vec_offset).collect(),
            results: vec![x86::gpr_offset(0), x86::gpr_offset(2), x86::vec_offset(0)],
            // rbx, rbp, r12 through r15.
            callee_saved: [3u8, 5, 12, 13, 14, 15]
                .iter()
                .map(|n| x86::gpr_offset(*n))
                .collect(),
            // rax, rcx, rdx, rsi, rdi and r8 through r11.
            caller_saved: [0u8, 1, 2, 6, 7, 8, 9, 10, 11]
                .iter()
                .map(|n| x86::gpr_offset(*n))
                .collect(),
            stack_pointer: x86::sp_offset(),
            vector_base: x86::vec_offset(0),
            stack_argument_base: 8,
        },
        _ => Abi {
            integer_arguments: (0..8).map(aarch64::gpr_offset).collect(),
            float_arguments: (0..8).map(aarch64::vec_offset).collect(),
            results: vec![
                aarch64::gpr_offset(0),
                aarch64::gpr_offset(1),
                aarch64::vec_offset(0),
            ],
            // x19 through x28, and the frame pointer.
            callee_saved: (19..=29).map(aarch64::gpr_offset).collect(),
            // x0 through x18, which a callee may use for anything.
            caller_saved: (0..=18).map(aarch64::gpr_offset).collect(),
            stack_pointer: aarch64::sp_offset(),
            vector_base: aarch64::vec_offset(0),
            stack_argument_base: 0,
        },
    }
}
