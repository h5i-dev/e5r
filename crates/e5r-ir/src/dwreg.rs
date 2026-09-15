//! DWARF register numbers, and where they land in e5r's register file.
//!
//! DWARF numbers registers its own way, once per architecture, and the number
//! is the only thing a `DW_OP_reg` or a `DW_TAG_call_site_parameter` location
//! carries. Without this table the compiler's own record of what each call
//! passes where is unreadable: it says "register 5" and nothing here knows
//! that means `rdi`.
//!
//! The numbering is deliberately not the encoding order on x86-64. The System
//! V psABI assigns 0 to `rax`, 1 to `rdx` and 2 to `rcx`, where the instruction
//! encoding has `rcx` at 1 and `rdx` at 2, so a mapping that looked like the
//! identity would be wrong for exactly the two registers the convention cares
//! about most.
//!
//! Nothing here depends on a DWARF reader, so the IR keeps no debug-format
//! dependency: a caller that has parsed the numbers passes them in.

use e5r_core::Arch;

use crate::lift::{aarch64, x86};

/// x86-64 DWARF number to encoding number, for the first eight registers. The
/// System V psABI, figure 3.36: rax, rdx, rcx, rbx, rsi, rdi, rbp, rsp.
const X86_64_LOW: [u8; 8] = [0, 2, 1, 3, 6, 7, 5, 4];

/// The register file offset a DWARF register number names.
///
/// `None` when the number names a register e5r does not model, which is an
/// honest gap rather than a guess: a segment register or an x87 stack slot has
/// no offset here, and inventing one would misplace an argument.
pub fn offset(arch: &Arch, number: u16) -> Option<u64> {
    match arch {
        Arch::X86_64 => match number {
            0..=7 => Some(x86::gpr_offset(X86_64_LOW[number as usize])),
            8..=15 => Some(x86::gpr_offset(number as u8)),
            // 16 is the return address, which lives on the stack rather than
            // in a register, and 17 through 32 are xmm0 through xmm15.
            17..=32 => Some(x86::vec_offset((number - 17) as u8)),
            _ => None,
        },
        Arch::X86 => match number {
            // eax, ecx, edx, ebx, esp, ebp, esi, edi: the encoding order, for
            // once. 8 is eip and 9 is eflags.
            0..=7 => Some(x86::gpr_offset(number as u8)),
            21..=28 => Some(x86::vec_offset((number - 21) as u8)),
            _ => None,
        },
        Arch::AArch64 => match number {
            // x0 through x30, then the stack pointer. 32 is the PC and 33 the
            // exception link register, neither of which is in the file.
            0..=30 => Some(aarch64::gpr_offset(number as u8)),
            31 => Some(aarch64::sp_offset()),
            // v0 through v31. 48 through 63 are the SVE predicates and 96
            // upwards the SVE vectors, none of which are modelled.
            64..=95 => Some(aarch64::vec_offset((number - 64) as u8)),
            _ => None,
        },
        _ => None,
    }
}

/// The DWARF register number for a register file offset, the other way round.
///
/// Useful for reporting: a detected convention that names offsets can say what
/// the compiler would have called them.
pub fn number(arch: &Arch, offset_of: u64) -> Option<u16> {
    // Small enough that a search beats a second table that could disagree with
    // the first one.
    let limit = match arch {
        Arch::X86_64 => 33u16,
        Arch::X86 => 29,
        Arch::AArch64 => 96,
        _ => 0,
    };
    (0..limit).find(|n| offset(arch, *n) == Some(offset_of))
}

/// True when the architecture has a mapping at all.
pub fn known(arch: &Arch) -> bool {
    matches!(arch, Arch::X86 | Arch::X86_64 | Arch::AArch64)
}
