//! The decoded instruction, shared by every decoder.
//!
//! Allocation-free: operands live in a fixed array, so decoding a million
//! instructions costs no heap traffic. Five is enough for every AArch64 and
//! x86 form, since a shift or extend rides inside its register operand.

use std::fmt;

use e5r_core::Addr;

/// Register width in bits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Width {
    /// 8-bit.
    W8,
    /// 16-bit.
    W16,
    /// 32-bit.
    W32,
    /// 64-bit.
    W64,
    /// 128-bit, a vector register.
    W128,
}

impl Width {
    /// Size in bytes.
    pub const fn bytes(self) -> u64 {
        match self {
            Width::W8 => 1,
            Width::W16 => 2,
            Width::W32 => 4,
            Width::W64 => 8,
            Width::W128 => 16,
        }
    }
}

/// What kind of register an operand names.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RegClass {
    /// General purpose.
    Gpr,
    /// The high byte of one of the first four x86 registers: `ah`, `ch`, `dh`,
    /// `bh`. A separate bank because `ah` is not the low byte of `rax`, and
    /// code that treats it as one is wrong in a way that is hard to see.
    GprHigh,
    /// An x86 segment register.
    Seg,
    /// The stack pointer, which AArch64 encodes as register 31 in some forms.
    Sp,
    /// The zero register, which is register 31 in the other forms.
    Zr,
    /// Vector or floating point.
    Vec,
    /// A system register.
    Sys,
    /// The program counter, where an architecture exposes it.
    Pc,
    /// The condition flags.
    Flags,
}

/// One register.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Reg {
    /// Which bank.
    pub class: RegClass,
    /// Number within the bank.
    pub num: u8,
    /// Width being used, which can be narrower than the register.
    pub width: Width,
}

impl Reg {
    /// A general purpose register.
    pub const fn gpr(num: u8, width: Width) -> Reg {
        Reg {
            class: RegClass::Gpr,
            num,
            width,
        }
    }

    /// A vector or floating point register.
    pub const fn vec(num: u8, width: Width) -> Reg {
        Reg {
            class: RegClass::Vec,
            num,
            width,
        }
    }

    /// True when writes to this register go nowhere.
    pub fn is_zero(self) -> bool {
        self.class == RegClass::Zr
    }
}

/// Shift applied to a register operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Shift {
    /// Logical left.
    Lsl,
    /// Logical right.
    Lsr,
    /// Arithmetic right.
    Asr,
    /// Rotate right.
    Ror,
    /// Shift left filling with ones, which only the SIMD immediate forms use.
    Msl,
}

impl Shift {
    /// The lowercase name.
    pub const fn as_str(self) -> &'static str {
        match self {
            Shift::Lsl => "lsl",
            Shift::Lsr => "lsr",
            Shift::Asr => "asr",
            Shift::Ror => "ror",
            Shift::Msl => "msl",
        }
    }
}

/// Extension applied to a register operand before use.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Extend {
    /// Unsigned byte.
    Uxtb,
    /// Unsigned halfword.
    Uxth,
    /// Unsigned word.
    Uxtw,
    /// Unsigned doubleword, which is a no-op and prints as `lsl` when shifted.
    Uxtx,
    /// Signed byte.
    Sxtb,
    /// Signed halfword.
    Sxth,
    /// Signed word.
    Sxtw,
    /// Signed doubleword.
    Sxtx,
    /// A plain shift with no extension, for indexed addressing.
    Lsl,
    /// `lsl #0`, which the architecture prints explicitly when the scale bit is
    /// set even though the amount is zero.
    LslZero,
}

impl Extend {
    /// The lowercase name.
    pub const fn as_str(self) -> &'static str {
        match self {
            Extend::Uxtb => "uxtb",
            Extend::Uxth => "uxth",
            Extend::Uxtw => "uxtw",
            Extend::Uxtx => "uxtx",
            Extend::Sxtb => "sxtb",
            Extend::Sxth => "sxth",
            Extend::Sxtw => "sxtw",
            Extend::Sxtx => "sxtx",
            Extend::Lsl | Extend::LslZero => "lsl",
        }
    }
}

/// How a memory operand computes its address.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AddrMode {
    /// `[base, #disp]`.
    Offset,
    /// `[base, #disp]!`, base updated before the access.
    PreIndex,
    /// `[base], #disp`, base updated after the access.
    PostIndex,
}

/// A memory reference.
///
/// General enough for both architectures: AArch64 always has a base and never
/// a segment, x86 can have neither base nor index (`[0x1234]`) and can scale
/// its index by 1, 2, 4 or 8.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Mem {
    /// Segment override, on the architectures that have one.
    pub seg: Option<Reg>,
    /// Base register, absent for an absolute or index-only address.
    pub base: Option<Reg>,
    /// Index register with its extension and shift amount. The shift is the
    /// log2 of x86's scale.
    pub index: Option<(Reg, Extend, u8)>,
    /// Constant displacement.
    pub disp: i64,
    /// Whether the base is updated.
    pub mode: AddrMode,
    /// Bytes transferred, for reporting and for data typing.
    pub size: u64,
}

impl Mem {
    /// True when the base is the program counter, so the displacement is
    /// relative to the end of the instruction.
    pub fn is_pc_relative(&self) -> bool {
        self.base.map(|b| b.class) == Some(RegClass::Pc)
    }

    /// The absolute address a pc-relative operand names, given where the
    /// instruction ends.
    pub fn pc_target(&self, insn_end: Addr) -> Option<Addr> {
        self.is_pc_relative()
            .then(|| insn_end.wrapping_offset(self.disp))
    }

    /// A plain `[base + disp]`.
    pub const fn base_disp(base: Reg, disp: i64, size: u64) -> Mem {
        Mem {
            seg: None,
            base: Some(base),
            index: None,
            disp,
            mode: AddrMode::Offset,
            size,
        }
    }
}

/// How a SIMD register's bits are divided into lanes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Lanes {
    /// Eight bytes.
    B8,
    /// Sixteen bytes.
    B16,
    /// Four halfwords.
    H4,
    /// Eight halfwords.
    H8,
    /// Two words.
    S2,
    /// Four words.
    S4,
    /// One doubleword.
    D1,
    /// Two doublewords.
    D2,
    /// One quadword.
    Q1,
}

impl Lanes {
    /// The suffix a listing prints, as in `v0.16b`.
    pub const fn as_str(self) -> &'static str {
        match self {
            Lanes::B8 => "8b",
            Lanes::B16 => "16b",
            Lanes::H4 => "4h",
            Lanes::H8 => "8h",
            Lanes::S2 => "2s",
            Lanes::S4 => "4s",
            Lanes::D1 => "1d",
            Lanes::D2 => "2d",
            Lanes::Q1 => "1q",
        }
    }
}

/// A condition code, in the architecture's own numbering.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Cond(pub u8);

/// One operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operand {
    /// A plain register.
    Reg(Reg),
    /// A register with a shift applied.
    Shifted(Reg, Shift, u8),
    /// A register with an extension applied.
    Extended(Reg, Extend, u8),
    /// A constant, printed in hex.
    Imm(i64),
    /// A bit pattern, printed unsigned at the operand's width. A logical
    /// immediate of all-ones is `0xffffffffffffffff`, not `-0x1`.
    UImm(u64),
    /// A count, index or bit position, printed in decimal. Shift amounts, bit
    /// numbers and bitfield widths read as decimal everywhere, so they are a
    /// different operand rather than a formatter special case.
    Count(i64),
    /// A bare shift qualifier, as in `movk w0, #0x5a5a, lsl #16`.
    ShiftOp(Shift, u8),
    /// A named option, as in `bti c`. The decoder supplies the name.
    Name(&'static str),
    /// A floating point literal, held as its IEEE-754 double bit pattern so the
    /// operand stays `Eq` and the instruction stays comparable.
    FpImm(u64),
    /// A SIMD register viewed as lanes, as in `v0.16b`.
    Vector(u8, Lanes),
    /// One lane of a SIMD register, as in `v0.s[2]`.
    VectorLane(u8, Width, u8),
    /// A list of consecutive SIMD registers, as in `{v0.16b, v1.16b}`. The
    /// fields are the first register, how many there are, and the lanes.
    VectorList(u8, u8, Lanes),
    /// An absolute address, the resolved target of a branch or a pc-relative
    /// computation. Kept distinct from `Imm` so analysis can find targets
    /// without re-deriving them.
    Addr(Addr),
    /// A memory reference.
    Mem(Mem),
    /// A condition code.
    Cond(Cond),
    /// A system register or barrier option, printed by the decoder's namer.
    Sys(u32),
}

/// What the instruction does to control flow.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Flow {
    /// Execution continues at the next instruction.
    Next,
    /// Unconditional branch to a known address.
    Branch(Addr),
    /// Branch taken or not; both successors are live.
    CondBranch(Addr),
    /// Unconditional branch through a register.
    IndirectBranch,
    /// Call to a known address; the callee is expected to return.
    Call(Addr),
    /// Call through a register.
    IndirectCall,
    /// Return to the caller.
    Return,
    /// Execution stops here: a breakpoint or an undefined instruction.
    Trap,
    /// A system call, which returns.
    Syscall,
}

impl Flow {
    /// True when the next instruction in address order is a successor.
    pub fn falls_through(self) -> bool {
        matches!(
            self,
            Flow::Next | Flow::CondBranch(_) | Flow::Call(_) | Flow::IndirectCall | Flow::Syscall
        )
    }

    /// The direct target, when there is one.
    pub fn target(self) -> Option<Addr> {
        match self {
            Flow::Branch(a) | Flow::CondBranch(a) | Flow::Call(a) => Some(a),
            _ => None,
        }
    }

    /// True when this ends a basic block.
    pub fn ends_block(self) -> bool {
        !matches!(self, Flow::Next)
    }

    /// True when this transfers to a callee.
    pub fn is_call(self) -> bool {
        matches!(self, Flow::Call(_) | Flow::IndirectCall)
    }
}

/// The most operands any supported encoding uses.
///
/// Six, which is what ARM's `mcr` and `mrc` take: a coprocessor, an opcode,
/// a core register, two coprocessor registers and a second opcode. Everything
/// else needs fewer. [`Insn::push`] drops anything past this rather than
/// growing, so a decoder that needs more would silently produce an instruction
/// missing an operand -- which is why this is the widest encoding and not a
/// round number.
pub const MAX_OPERANDS: usize = 6;

/// A decoded instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Insn {
    /// Where it starts.
    pub addr: Addr,
    /// How many bytes it occupies.
    pub len: u8,
    /// The mnemonic, already resolved through any alias the architecture
    /// prefers, so `sbfm` with the right fields arrives as `asr`.
    pub mnemonic: &'static str,
    /// What the flow analysis needs to know.
    pub flow: Flow,
    /// A prefix that modifies the whole instruction rather than an operand:
    /// x86's `lock`, `rep` and `repne`. Printed ahead of the mnemonic.
    pub prefix: Option<&'static str>,
    ops: [Operand; MAX_OPERANDS],
    n_ops: u8,
}

impl Insn {
    /// Build an instruction with no operands.
    pub fn new(addr: Addr, len: u8, mnemonic: &'static str, flow: Flow) -> Insn {
        Insn {
            addr,
            len,
            mnemonic,
            flow,
            prefix: None,
            ops: [Operand::Imm(0); MAX_OPERANDS],
            n_ops: 0,
        }
    }

    /// Append an operand. Beyond [`MAX_OPERANDS`] it is dropped, which cannot
    /// happen for any encoding the decoders produce.
    pub fn push(&mut self, op: Operand) -> &mut Self {
        if (self.n_ops as usize) < MAX_OPERANDS {
            self.ops[self.n_ops as usize] = op;
            self.n_ops += 1;
        }
        self
    }

    /// Replace one operand, for a spelling that changes how it reads.
    pub fn set_operand(&mut self, n: usize, op: Operand) {
        if n < self.n_ops as usize {
            self.ops[n] = op;
        }
    }

    /// The operands.
    pub fn operands(&self) -> &[Operand] {
        &self.ops[..self.n_ops as usize]
    }

    /// One past the last byte.
    pub fn end(&self) -> Addr {
        self.addr.wrapping_offset(self.len as i64)
    }

    /// The address of the next instruction in address order.
    pub fn next(&self) -> Addr {
        self.end()
    }

    /// Every address this instruction can transfer to directly.
    pub fn successors(&self) -> impl Iterator<Item = Addr> {
        let target = match self.flow {
            Flow::Branch(a) | Flow::CondBranch(a) => Some(a),
            _ => None,
        };
        let fallthrough = self.flow.falls_through().then(|| self.next());
        target.into_iter().chain(fallthrough)
    }
}

impl fmt::Display for Insn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.mnemonic)
    }
}
