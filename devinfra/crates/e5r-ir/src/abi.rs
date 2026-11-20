//! What the calling convention says, per architecture.
//!
//! Two passes need this and neither can work without it. Dead code elimination
//! has to know which registers the caller may read after a return, or it
//! deletes the result. The decompiler has to know which registers arrive with
//! values, or every function takes no arguments.
//!
//! This is the default convention, not a recovered one. A function that does
//! something else is [`crate::conv`]'s per-function detection, which this is
//! the floor for: detection is a comparison, and this is the thing compared
//! against.
//!
//! More than one convention exists per architecture. The same x86-64 code
//! passes its first argument in `rdi` under System V and in `rcx` under the
//! Microsoft convention, so the container decides as much as the machine does
//! and [`of_named`] takes the convention as an argument. [`of`] keeps the
//! platform default for an architecture, which is what every existing caller
//! wants.

use e5r_core::Arch;

use crate::lift::{aarch64, arm, x86};
use crate::op::Space;
use crate::ssa::Location;

/// A calling convention with a name, as opposed to one a compiler invented.
///
/// Naming them is what lets detection say "this is `__fastcall`" rather than
/// "this is not the default": a non-standard convention that happens to be
/// another platform's standard one is a different finding from a convention
/// with no name at all.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Named {
    /// System V AMD64, the ELF and Mach-O default on x86-64.
    SysV,
    /// AAPCS64, the default on AArch64 everywhere including Windows.
    Aapcs64,
    /// AAPCS32, the default on 32-bit ARM: four integer registers and the
    /// stack, with the return address in the link register.
    Aapcs32,
    /// The Microsoft x64 convention: four integer registers, four vector
    /// ones, and thirty-two bytes of shadow space the caller reserves.
    Win64,
    /// 32-bit x86 `cdecl`: everything on the stack, the caller pops.
    Cdecl,
    /// 32-bit x86 `__stdcall`: everything on the stack, the callee pops.
    Stdcall,
    /// 32-bit x86 `__fastcall`: `ecx` and `edx`, then the stack, callee pops.
    Fastcall,
    /// 32-bit x86 `__thiscall`: the object in `ecx`, the rest on the stack,
    /// callee pops.
    Thiscall,
    /// 32-bit x86 `__vectorcall`: `__fastcall` plus `xmm0` through `xmm5`.
    Vectorcall,
}

impl Named {
    /// The word used in output and in JSON.
    pub fn as_str(self) -> &'static str {
        match self {
            Named::SysV => "sysv",
            Named::Aapcs64 => "aapcs64",
            Named::Aapcs32 => "aapcs32",
            Named::Win64 => "win64",
            Named::Cdecl => "cdecl",
            Named::Stdcall => "stdcall",
            Named::Fastcall => "fastcall",
            Named::Thiscall => "thiscall",
            Named::Vectorcall => "vectorcall",
        }
    }
}

impl std::fmt::Display for Named {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// The registers a convention uses, as byte offsets into the register file.
#[derive(Debug, Clone)]
pub struct Abi {
    /// Which convention this is.
    pub name: Named,
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
    /// return address in a register and starts at zero. The Microsoft x64
    /// convention adds thirty-two bytes of shadow space on top of that.
    pub stack_argument_base: i64,
    /// Bytes the call itself pushes, which the callee has to step over on the
    /// way out. The return address on x86, nothing on AArch64.
    pub return_address_bytes: u64,
    /// True when the callee removes the stack arguments before returning,
    /// which on x86 is visible as a `ret imm16`.
    pub callee_pops: bool,
    /// The register a member function receives the object in, when the
    /// convention gives it one of its own rather than making it the first
    /// ordinary argument.
    pub this_register: Option<u64>,
    /// The register the caller puts the address of a memory-returned result
    /// in, when it is not simply the first argument register.
    pub indirect_result: Option<u64>,
    /// The register a variadic call reports its vector register count in.
    /// System V uses `al`; nothing else here does.
    pub varargs_count: Option<u64>,
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

    /// Which argument slot a register is, when it is one.
    pub fn slot(&self, offset: u64) -> Option<Slot> {
        if let Some(n) = self.integer_arguments.iter().position(|o| *o == offset) {
            return Some(Slot::Integer(n));
        }
        if let Some(n) = self.float_arguments.iter().position(|o| *o == offset) {
            return Some(Slot::Float(n));
        }
        None
    }

    /// True when the convention passes an argument in this register.
    pub fn passes_arguments_in(&self, offset: u64) -> bool {
        self.slot(offset).is_some()
    }

    /// True when the convention lets a caller read this register back
    /// unchanged.
    pub fn preserves(&self, offset: u64) -> bool {
        self.callee_saved.contains(&offset) || offset == self.stack_pointer
    }
}

/// Which argument register of a convention a register is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Slot {
    /// The nth integer argument register.
    Integer(usize),
    /// The nth floating point one.
    Float(usize),
}

/// The default convention for an architecture.
///
/// The ELF and Mach-O answer. A PE loader wants [`Named::Win64`] on x86-64 and
/// says so through [`of_named`].
pub fn of(arch: &Arch) -> Abi {
    match arch {
        Arch::X86_64 => of_named(arch, Named::SysV),
        Arch::X86 => of_named(arch, Named::Cdecl),
        Arch::Arm | Arch::Thumb => of_named(arch, Named::Aapcs32),
        _ => of_named(arch, Named::Aapcs64),
    }
}

/// The default convention for an architecture under a container.
///
/// The same instruction set has a different default depending on who linked
/// it, and the machine code cannot say which. This is the one place that
/// decision is written down.
pub fn of_container(arch: &Arch, windows: bool) -> Abi {
    match (arch, windows) {
        (Arch::X86_64, true) => of_named(arch, Named::Win64),
        _ => of(arch),
    }
}

/// A named convention's registers.
pub fn of_named(arch: &Arch, name: Named) -> Abi {
    match name {
        Named::Win64 => win64(),
        Named::SysV if *arch == Arch::X86_64 => sysv64(),
        Named::Aapcs32 => aapcs32(),
        Named::Cdecl | Named::Stdcall | Named::Fastcall | Named::Thiscall | Named::Vectorcall => {
            x86_32(name)
        }
        // Everything else is the 64-bit ARM convention, which is also what an
        // architecture with no model of its own falls back to.
        _ => aapcs64(),
    }
}

fn sysv64() -> Abi {
    Abi {
        name: Named::SysV,
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
        return_address_bytes: 8,
        callee_pops: false,
        this_register: None,
        indirect_result: None,
        // `al` carries the vector register count of a variadic call, so a read
        // of rax at entry is the convention and not a custom argument.
        varargs_count: Some(x86::gpr_offset(0)),
    }
}

fn win64() -> Abi {
    Abi {
        name: Named::Win64,
        // rcx, rdx, r8, r9, and no more: the fifth argument is on the stack.
        integer_arguments: [1u8, 2, 8, 9].iter().map(|n| x86::gpr_offset(*n)).collect(),
        float_arguments: (0..4).map(x86::vec_offset).collect(),
        results: vec![x86::gpr_offset(0), x86::vec_offset(0)],
        // rbx, rbp, rsi, rdi, r12 through r15. The vector half of the list is
        // xmm6 upwards, which matters to dead code elimination across a call.
        callee_saved: [3u8, 5, 6, 7, 12, 13, 14, 15]
            .iter()
            .map(|n| x86::gpr_offset(*n))
            .chain((6..16).map(x86::vec_offset))
            .collect(),
        caller_saved: [0u8, 1, 2, 8, 9, 10, 11]
            .iter()
            .map(|n| x86::gpr_offset(*n))
            .chain((0..6).map(x86::vec_offset))
            .collect(),
        stack_pointer: x86::sp_offset(),
        vector_base: x86::vec_offset(0),
        // The return address, then thirty-two bytes of shadow space the caller
        // reserves for the four register arguments. The fifth argument is the
        // first one actually passed on the stack.
        stack_argument_base: 40,
        return_address_bytes: 8,
        callee_pops: false,
        this_register: None,
        indirect_result: None,
        varargs_count: None,
    }
}

/// The 32-bit x86 conventions, which differ from each other only in how many
/// registers they use and who pops.
/// AAPCS32, the 32-bit ARM convention.
///
/// Four integer registers and then the stack, the result in r0 and r1, and the
/// return address in the link register rather than on the stack -- the same
/// shape as AAPCS64 with half the registers.
fn aapcs32() -> Abi {
    Abi {
        name: Named::Aapcs32,
        integer_arguments: (0..4).map(arm::gpr_offset).collect(),
        // Floating point arguments go in the VFP registers under the hard
        // float variant and in the integer ones under the soft float variant.
        // The hard float set is named here; a soft float call still resolves,
        // because its arguments are in the integer registers above.
        float_arguments: (0..8).map(arm::vec_offset).collect(),
        results: vec![arm::gpr_offset(0), arm::gpr_offset(1), arm::vec_offset(0)],
        // r4 through r11.
        callee_saved: (4..=11).map(arm::gpr_offset).collect(),
        // r0 through r3, and r12, which is the intra-procedure scratch.
        caller_saved: (0..=3)
            .chain(std::iter::once(12))
            .map(arm::gpr_offset)
            .collect(),
        stack_pointer: arm::sp_offset(),
        vector_base: arm::vec_offset(0),
        stack_argument_base: 0,
        // The call leaves the return address in the link register.
        return_address_bytes: 0,
        callee_pops: false,
        this_register: None,
        // A result too large for the registers is written through a pointer
        // the caller passes in r0, which shifts every declared argument along.
        indirect_result: Some(arm::gpr_offset(0)),
        varargs_count: None,
    }
}

fn x86_32(name: Named) -> Abi {
    let integer_arguments: Vec<u64> = match name {
        // ecx, edx.
        Named::Fastcall | Named::Vectorcall => vec![x86::gpr_offset(1), x86::gpr_offset(2)],
        // The object, and nothing else.
        Named::Thiscall => vec![x86::gpr_offset(1)],
        _ => Vec::new(),
    };
    let float_arguments: Vec<u64> = match name {
        Named::Vectorcall => (0..6).map(x86::vec_offset).collect(),
        _ => Vec::new(),
    };
    Abi {
        name,
        integer_arguments,
        float_arguments,
        // eax, then edx for the upper half of a 64-bit value.
        results: vec![x86::gpr_offset(0), x86::gpr_offset(2), x86::vec_offset(0)],
        // ebx, ebp, esi, edi.
        callee_saved: [3u8, 5, 6, 7].iter().map(|n| x86::gpr_offset(*n)).collect(),
        // eax, ecx, edx.
        caller_saved: [0u8, 1, 2].iter().map(|n| x86::gpr_offset(*n)).collect(),
        stack_pointer: x86::sp_offset(),
        vector_base: x86::vec_offset(0),
        stack_argument_base: 4,
        return_address_bytes: 4,
        callee_pops: name != Named::Cdecl,
        this_register: (name == Named::Thiscall).then(|| x86::gpr_offset(1)),
        indirect_result: None,
        varargs_count: None,
    }
}

fn aapcs64() -> Abi {
    Abi {
        name: Named::Aapcs64,
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
        // The call leaves the return address in x30, not on the stack.
        return_address_bytes: 0,
        callee_pops: false,
        this_register: None,
        // x8 carries the address of a result returned in memory, so a read of
        // it at entry is the convention rather than a custom argument.
        indirect_result: Some(aarch64::gpr_offset(8)),
        varargs_count: None,
    }
}
