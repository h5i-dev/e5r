//! Instruction decoders.
//!
//! One [`Insn`] type for every architecture, so analysis is written once.
//! Decoders are hand-written for the architectures where speed matters and
//! resolve aliases themselves: `sbfm` with a full-width extraction is `asr`,
//! and analysis that has to know both spellings has a bug waiting in it.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod aarch64;
pub mod insn;
pub mod x86;

pub use insn::{
    AddrMode, Cond, Extend, Flow, Insn, Lanes, MAX_OPERANDS, Mem, Operand, Reg, RegClass, Shift,
    Width,
};

use r12e_core::{Addr, Arch};

/// Decode one instruction for `arch`, or `None` when the bytes are not an
/// allocated encoding.
pub fn decode(arch: &Arch, bytes: &[u8], addr: Addr) -> Option<Insn> {
    match arch {
        Arch::AArch64 => aarch64::decode(bytes, addr),
        Arch::X86_64 => x86::decode(bytes, addr),
        _ => None,
    }
}

/// Render an instruction the way the architecture's usual disassembler does.
pub fn format(arch: &Arch, i: &Insn, objdump: bool) -> String {
    match arch {
        Arch::AArch64 => aarch64::format(i, aarch64::text::Style { objdump }),
        Arch::X86_64 => x86::format(i, x86::Style::default()),
        _ => i.mnemonic.to_string(),
    }
}
