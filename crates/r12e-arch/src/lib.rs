//! Instruction decoders.
//!
//! One [`Insn`] type for every architecture, so analysis is written once.
//! Decoders are hand-written for the architectures where speed matters and
//! resolve aliases themselves: `sbfm` with a full-width extraction is `asr`,
//! and analysis that has to know both spellings has a bug waiting in it.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod aarch64;
pub mod arm;
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
        Arch::X86 => x86::decode32(bytes, addr),
        Arch::Arm => arm::decode(bytes, addr),
        // Outside an IT block, which is where a caller that hands over one
        // address at a time always is. `arm::Thumb` walks a run and carries
        // the state across it; this is the single-instruction view.
        Arch::Thumb => arm::decode_thumb(bytes, addr, arm::ItState::default()).map(|(i, _)| i),
        _ => None,
    }
}

/// Render an instruction the way the architecture's usual disassembler does.
pub fn format(arch: &Arch, i: &Insn, objdump: bool) -> String {
    match arch {
        Arch::AArch64 => aarch64::format(i, aarch64::text::Style { objdump }),
        Arch::X86_64 | Arch::X86 => x86::format(i, x86::Style::default()),
        Arch::Arm | Arch::Thumb => arm::format(i),
        _ => i.mnemonic.to_string(),
    }
}
