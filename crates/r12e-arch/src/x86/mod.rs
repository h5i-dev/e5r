//! x86 decoder, 64-bit and 32-bit.
//!
//! Variable length, so decoding is a walk: legacy prefixes, then REX, then one
//! to three opcode bytes, then ModRM and SIB, then a displacement, then an
//! immediate. Each stage can end the instruction, and the length is whatever
//! the walk consumed.
//!
//! The two modes share one table and differ in [`Mode`]. The difference is not
//! cosmetic: the opcodes 32-bit mode spends on `inc`/`dec`, `pusha` and the
//! BCD instructions are REX prefixes in long mode, so a decoder that guesses
//! the mode desynchronizes on the first byte rather than misnaming one
//! instruction.

pub mod table;
pub mod text;

pub use text::{Style, format};

use r12e_core::Addr;

use crate::insn::{AddrMode, Flow, Insn, Mem, Operand, Reg, RegClass, Width};
use table::{CC, Entry, GROUPS, Op};

/// Which mode the processor is in, which the caller knows and the bytes do not.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// 64-bit mode: REX prefixes, 64-bit addresses, and no one-byte `inc`.
    #[default]
    Long,
    /// 32-bit protected mode, which is what an i386 image holds.
    Protected,
}

/// The prefixes and fields gathered before the opcode is looked up.
#[derive(Clone, Copy)]
struct Prefixes {
    /// The mode being decoded for.
    mode: Mode,
    /// `0x66`, which halves the operand size or selects an SSE variant.
    opsize: bool,
    /// `0x67`, which halves the address size.
    addrsize: bool,
    /// `0xf3`.
    rep: bool,
    /// `0xf2`.
    repne: bool,
    /// `0xf0`.
    lock: bool,
    /// A segment override, as a register number, if any.
    seg: Option<u8>,
    /// REX.W: 64-bit operand size.
    w: bool,
    /// REX.R: extends ModRM reg.
    r: bool,
    /// REX.X: extends the SIB index.
    x: bool,
    /// REX.B: extends ModRM r/m, SIB base, or the opcode register.
    b: bool,
    /// Whether any REX byte was present, which changes which byte registers
    /// the low three bits name.
    rex: bool,
    /// Whether the last `0xf2` or `0xf3` sat where a mandatory prefix has to
    /// sit: immediately before the opcode, or before the `0x66` or REX byte
    /// that is. Anywhere else it is only a repeat prefix, and llvm then spells
    /// it out even on a two-byte opcode that ignores it.
    repeat_is_mandatory: bool,
    /// The opcode defaults to 64-bit operands in long mode, so `push rbp`
    /// needs no REX.W. True for push, pop, near call and near jmp.
    default64: bool,
    /// The opcode names a register through r/m whatever the mod field holds,
    /// which is how `mov cr0, eax` encodes: the mod bits are ignored, not
    /// reserved, so decoding them as memory reads displacement bytes that are
    /// really the next instruction.
    force_reg_rm: bool,
}

impl Prefixes {
    fn new(mode: Mode) -> Self {
        Prefixes {
            mode,
            opsize: false,
            addrsize: false,
            rep: false,
            repne: false,
            lock: false,
            seg: None,
            w: false,
            r: false,
            x: false,
            b: false,
            rex: false,
            repeat_is_mandatory: false,
            default64: false,
            force_reg_rm: false,
        }
    }

    fn long(&self) -> bool {
        self.mode == Mode::Long
    }

    /// The operand size in bytes for an `Ev`-style operand.
    fn opsize_bytes(&self) -> u64 {
        if !self.long() {
            // No REX and nothing defaults to 64-bit, so `0x66` is the only
            // thing that can move the size off the 32-bit default.
            return if self.opsize { 2 } else { 4 };
        }
        if self.w || (self.default64 && !self.opsize) {
            8
        } else if self.opsize {
            2
        } else {
            4
        }
    }

    /// The address size in bytes. `0x67` halves it in both modes, which means
    /// it selects 32-bit addressing in long mode and 16-bit addressing here.
    fn addr_bytes(&self) -> u64 {
        match (self.long(), self.addrsize) {
            (true, false) => 8,
            (true, true) => 4,
            (false, false) => 4,
            (false, true) => 2,
        }
    }

    fn addr_width(&self) -> Width {
        width_of(self.addr_bytes())
    }

    /// The size of an operand the table forces to 64 bits. In 32-bit mode
    /// there is no such width, so those operands are doublewords.
    fn forced_qword(&self) -> u64 {
        if self.long() { 8 } else { 4 }
    }

    fn width(&self) -> Width {
        match self.opsize_bytes() {
            8 => Width::W64,
            2 => Width::W16,
            _ => Width::W32,
        }
    }
}

/// A cursor over the instruction's bytes.
struct Cursor<'a> {
    b: &'a [u8],
    at: usize,
}

impl<'a> Cursor<'a> {
    fn u8(&mut self) -> Option<u8> {
        let v = *self.b.get(self.at)?;
        self.at += 1;
        Some(v)
    }

    fn peek(&self) -> Option<u8> {
        self.b.get(self.at).copied()
    }

    fn i8(&mut self) -> Option<i64> {
        Some(self.u8()? as i8 as i64)
    }

    fn u16(&mut self) -> Option<u64> {
        let a = self.u8()? as u64;
        let b = self.u8()? as u64;
        Some(a | (b << 8))
    }

    fn i16(&mut self) -> Option<i64> {
        Some(self.u16()? as u16 as i16 as i64)
    }

    fn u32(&mut self) -> Option<u64> {
        let mut v = 0u64;
        for i in 0..4 {
            v |= (self.u8()? as u64) << (8 * i);
        }
        Some(v)
    }

    fn i32(&mut self) -> Option<i64> {
        Some(self.u32()? as u32 as i32 as i64)
    }

    fn u64(&mut self) -> Option<u64> {
        let mut v = 0u64;
        for i in 0..8 {
            v |= (self.u8()? as u64) << (8 * i);
        }
        Some(v)
    }
}

/// A general purpose register at a width, honouring the REX rule for byte
/// registers: without REX, numbers 4 to 7 name `ah`, `ch`, `dh` and `bh`.
fn gpr(num: u8, width: Width, rex: bool) -> Reg {
    if width == Width::W8 && !rex && (4..8).contains(&num) {
        return Reg {
            class: RegClass::GprHigh,
            num: num - 4,
            width,
        };
    }
    Reg::gpr(num, width)
}

/// The MMX register file, which prints by name: it aliases the x87 stack and
/// [`RegClass`] has no class of its own for it.
const MM: [&str; 8] = ["mm0", "mm1", "mm2", "mm3", "mm4", "mm5", "mm6", "mm7"];

fn xmm(num: u8) -> Reg {
    Reg {
        class: RegClass::Vec,
        num,
        width: Width::W128,
    }
}

/// Debug register names, which print by name because [`RegClass`] has a single
/// system class and it already spells itself `cr`.
const DR: [&str; 16] = [
    "dr0", "dr1", "dr2", "dr3", "dr4", "dr5", "dr6", "dr7", "dr8", "dr9", "dr10", "dr11", "dr12",
    "dr13", "dr14", "dr15",
];

fn width_of(bytes: u64) -> Width {
    match bytes {
        1 => Width::W8,
        2 => Width::W16,
        8 => Width::W64,
        16 => Width::W128,
        _ => Width::W32,
    }
}

/// Decoded ModRM, SIB and displacement.
struct ModRm {
    reg: u8,
    /// The r/m operand, already built. `None` until [`decode_modrm`] runs.
    rm: RmOperand,
}

enum RmOperand {
    Reg(u8),
    Mem(Mem),
}

/// The base and index register pairs of 16-bit addressing, indexed by r/m.
/// `NONE16` marks the half of a pair that is absent. These forms exist only
/// under `0x67` in 32-bit mode, where they are the survivors of real mode.
const NONE16: u8 = 0xff;
const BASE16: [(u8, u8); 8] = [
    (3, 6),
    (3, 7),
    (5, 6),
    (5, 7),
    (6, NONE16),
    (7, NONE16),
    (5, NONE16),
    (3, NONE16),
];

/// Decode ModRM plus any SIB and displacement.
fn decode_modrm(c: &mut Cursor<'_>, p: &Prefixes, size: u64) -> Option<ModRm> {
    let modrm = c.u8()?;
    let md = if p.force_reg_rm { 3 } else { modrm >> 6 };
    let reg = ((modrm >> 3) & 7) | if p.r { 8 } else { 0 };
    let rm = modrm & 7;

    if md == 3 {
        return Some(ModRm {
            reg,
            rm: RmOperand::Reg(rm | if p.b { 8 } else { 0 }),
        });
    }

    let seg = p.seg.map(|s| Reg {
        class: RegClass::Seg,
        num: s,
        width: Width::W16,
    });

    if p.addr_bytes() == 2 {
        // 16-bit addressing: no SIB, a fixed set of base and index pairs, and
        // `[bp]` with mod 0 spelled as an absolute 16-bit displacement.
        let (b, x) = BASE16[rm as usize];
        let mut base = None;
        let mut index = None;
        let mut disp = 0i64;
        if rm == 6 && md == 0 {
            disp = c.i16()?;
        } else {
            base = Some(Reg::gpr(b, Width::W16));
            if x != NONE16 {
                index = Some((Reg::gpr(x, Width::W16), crate::insn::Extend::Lsl, 0));
            }
        }
        match md {
            1 => disp = disp.wrapping_add(c.i8()?),
            2 => disp = disp.wrapping_add(c.i16()?),
            _ => {}
        }
        return Some(ModRm {
            reg,
            rm: RmOperand::Mem(Mem {
                seg,
                base,
                index,
                disp,
                mode: AddrMode::Offset,
                size,
            }),
        });
    }

    let addr_width = p.addr_width();
    let mut base: Option<Reg> = None;
    let mut index: Option<(Reg, crate::insn::Extend, u8)> = None;
    let mut disp: i64 = 0;
    let mut rip_relative = false;

    if rm == 4 {
        // A SIB byte follows.
        let sib = c.u8()?;
        let scale = sib >> 6;
        let idx = ((sib >> 3) & 7) | if p.x { 8 } else { 0 };
        let bse = (sib & 7) | if p.b { 8 } else { 0 };
        // Index 4 without REX.X means no index at all, and llvm then prints
        // the zero register `eiz` in its place, so that the scale stays
        // visible. The one exception is the canonical `[esp]` form, scale one
        // over the stack pointer, which is how every `[esp + n]` encodes.
        if idx != 4 {
            index = Some((gpr(idx, addr_width, true), crate::insn::Extend::Lsl, scale));
        } else if scale != 0 || sib & 7 != 4 {
            let no_base = sib & 7 == 5 && md == 0;
            if !(p.long() && no_base) {
                index = Some((
                    Reg {
                        class: RegClass::Zr,
                        num: 0,
                        width: addr_width,
                    },
                    crate::insn::Extend::Lsl,
                    scale,
                ));
            }
        }
        // Base 5 with mod 0 means a 32-bit displacement and no base.
        if sib & 7 == 5 && md == 0 {
            disp = c.i32()?;
        } else {
            base = Some(gpr(bse, addr_width, true));
        }
    } else if rm == 5 && md == 0 {
        // RIP-relative in long mode. In 32-bit mode the same encoding is the
        // plain absolute address it always was.
        disp = c.i32()?;
        rip_relative = p.long();
    } else {
        base = Some(gpr(rm | if p.b { 8 } else { 0 }, addr_width, true));
    }

    match md {
        1 => disp = disp.wrapping_add(c.i8()?),
        2 => disp = disp.wrapping_add(c.i32()?),
        _ => {}
    }

    if rip_relative {
        // The displacement stays as the bytes encode it, relative to the end
        // of the instruction. Resolving it here would make the text disagree
        // with the encoding; `Mem::rip_target` does it for analysis.
        base = Some(Reg {
            class: RegClass::Pc,
            num: 0,
            // `0x67` shrinks the program counter the displacement is taken
            // from, and llvm prints `eip` rather than `rip` when it does.
            width: addr_width,
        });
    }

    Some(ModRm {
        reg,
        rm: RmOperand::Mem(Mem {
            seg,
            base,
            index,
            disp,
            mode: AddrMode::Offset,
            size,
        }),
    })
}

/// The x87 stack registers, which print by name: [`RegClass`] has no class
/// for them and the whole file is eight registers wide.
const ST: [&str; 8] = [
    "st(0)", "st(1)", "st(2)", "st(3)", "st(4)", "st(5)", "st(6)", "st(7)",
];

/// Which operands an x87 register form prints.
enum StOps {
    /// No operands.
    None,
    /// One stack register.
    Sti,
    /// `st` and a stack register.
    StSti,
    /// A stack register and `st`.
    StiSt,
    /// `ax`, which only `fnstsw` uses.
    Ax,
}

/// The register forms of the x87 escapes: `0xd8` to `0xdf` with a ModRM byte
/// of 0xc0 or above. The memory forms go through [`table::X87_MEM`] and the
/// ordinary ModRM walk; these do not, because the ModRM byte is an opcode
/// extension rather than an operand specifier.
fn x87_reg(op: u8, m: u8) -> Option<(&'static str, StOps)> {
    let reg = ((m >> 3) & 7) as usize;
    let name = |n: &'static str| if n.is_empty() { None } else { Some(n) };
    Some(match op {
        0xd8 => {
            let n = name(table::X87_D8_REG[reg])?;
            // `fcom` and `fcomp` read the stack top without naming it.
            let form = if matches!(reg, 2 | 3) {
                StOps::Sti
            } else {
                StOps::StSti
            };
            (n, form)
        }
        0xd9 => match m {
            0xc0..=0xc7 => ("fld", StOps::Sti),
            0xc8..=0xcf => ("fxch", StOps::Sti),
            0xd0 => ("fnop", StOps::None),
            0xe0..=0xff => (name(table::X87_D9_E0[(m - 0xe0) as usize])?, StOps::None),
            _ => return None,
        },
        0xda => match m {
            0xc0..=0xdf => (fcmov(false, reg)?, StOps::StSti),
            0xe9 => ("fucompp", StOps::None),
            _ => return None,
        },
        0xdb => match m {
            0xc0..=0xdf => (fcmov(true, reg)?, StOps::StSti),
            0xe2 => ("fnclex", StOps::None),
            0xe3 => ("fninit", StOps::None),
            0xe8..=0xef => ("fucomi", StOps::StSti),
            0xf0..=0xf7 => ("fcomi", StOps::StSti),
            _ => return None,
        },
        0xdc => (name(table::X87_DC_REG[reg])?, StOps::StiSt),
        0xdd => (name(table::X87_DD_REG[reg])?, StOps::Sti),
        0xde => match m {
            0xd9 => ("fcompp", StOps::None),
            0xd0..=0xdf => return None,
            _ => (name(table::X87_DE_REG[reg])?, StOps::StiSt),
        },
        0xdf => match m {
            0xc0..=0xc7 => ("ffreep", StOps::Sti),
            0xe0 => ("fnstsw", StOps::Ax),
            0xe8..=0xef => ("fucompi", StOps::StSti),
            0xf0..=0xf7 => ("fcompi", StOps::StSti),
            _ => return None,
        },
        _ => return None,
    })
}

/// The conditional move names, which differ only by an `n`.
fn fcmov(negated: bool, reg: usize) -> Option<&'static str> {
    const P: [&str; 4] = ["fcmovb", "fcmove", "fcmovbe", "fcmovu"];
    const N: [&str; 4] = ["fcmovnb", "fcmovne", "fcmovnbe", "fcmovnu"];
    let _ = table::X87_FCMOV;
    if negated { N.get(reg) } else { P.get(reg) }.copied()
}

/// Decode one of the eight x87 escapes.
fn decode_x87(c: &mut Cursor<'_>, p: &Prefixes, op: u8, addr: Addr) -> Option<Insn> {
    let prefix = if p.lock {
        Some("lock")
    } else if p.rep {
        Some("rep")
    } else if p.repne {
        Some("repne")
    } else {
        None
    };
    let m = c.peek()?;
    if m >= 0xc0 {
        c.at += 1;
        let (name, form) = x87_reg(op, m)?;
        let mut i = Insn::new(addr, c.at as u8, name, Flow::Next);
        let sti = Operand::Name(ST[(m & 7) as usize]);
        match form {
            StOps::None => {}
            StOps::Sti => {
                i.push(sti);
            }
            StOps::StSti => {
                i.push(Operand::Name("st"));
                i.push(sti);
            }
            StOps::StiSt => {
                i.push(sti);
                i.push(Operand::Name("st"));
            }
            StOps::Ax => {
                i.push(Operand::Reg(Reg::gpr(0, Width::W16)));
            }
        }
        i.prefix = prefix_text(
            prefix,
            names_addr_size(p, &i).then_some(addr_prefix_name(p)),
        );
        return Some(i);
    }
    let (name, size) = table::X87_MEM[(op - 0xd8) as usize][((m >> 3) & 7) as usize];
    if name.is_empty() {
        return None;
    }
    let rm = decode_modrm(c, p, size as u64)?;
    let RmOperand::Mem(mem) = rm.rm else {
        return None;
    };
    let mut i = Insn::new(addr, c.at as u8, name, Flow::Next);
    i.push(Operand::Mem(mem));
    i.prefix = prefix_text(
        prefix,
        names_addr_size(p, &i).then_some(addr_prefix_name(p)),
    );
    Some(i)
}

/// Decode one instruction at `addr`, in 64-bit mode.
pub fn decode(bytes: &[u8], addr: Addr) -> Option<Insn> {
    decode_in(Mode::Long, bytes, addr)
}

/// Decode one instruction at `addr`, in 32-bit protected mode.
pub fn decode32(bytes: &[u8], addr: Addr) -> Option<Insn> {
    decode_in(Mode::Protected, bytes, addr)
}

/// Decode one instruction at `addr` in `mode`.
pub fn decode_in(mode: Mode, bytes: &[u8], addr: Addr) -> Option<Insn> {
    let mut c = Cursor { b: bytes, at: 0 };
    let mut p = Prefixes::new(mode);

    // Legacy prefixes, then at most one REX immediately before the opcode.
    loop {
        match c.peek()? {
            0x66 => p.opsize = true,
            0x67 => p.addrsize = true,
            0xf0 => p.lock = true,
            // The last repeat prefix wins, and llvm reports that one.
            b @ (0xf2 | 0xf3) => {
                p.repne = b == 0xf2;
                p.rep = b == 0xf3;
                p.repeat_is_mandatory = match c.b.get(c.at + 1) {
                    Some(0x0f | 0x66) => true,
                    Some(n) => mode == Mode::Long && (0x40..0x50).contains(n),
                    None => false,
                };
            }
            0x2e => p.seg = Some(1),
            0x36 => p.seg = Some(2),
            0x3e => p.seg = Some(3),
            0x26 => p.seg = Some(0),
            0x64 => p.seg = Some(4),
            0x65 => p.seg = Some(5),
            _ => break,
        }
        c.at += 1;
    }
    if let Some(b) = c.peek() {
        // Only long mode has REX. In 32-bit mode these bytes are `inc` and
        // `dec`, and consuming one as a prefix would eat the next opcode.
        if p.long() && (0x40..0x50).contains(&b) {
            p.rex = true;
            p.w = b & 8 != 0;
            p.r = b & 4 != 0;
            p.x = b & 2 != 0;
            p.b = b & 1 != 0;
            c.at += 1;
        }
    }

    let op = c.u8()?;
    if (0xd8..=0xdf).contains(&op) {
        return decode_x87(&mut c, &p, op, addr);
    }
    let (entry, two_byte, opcode) = if op == 0x0f {
        let op2 = c.u8()?;
        // The three-byte maps, which is where SSSE3 and SSE4 live.
        if op2 == 0x38 || op2 == 0x3a {
            let op3 = c.u8()?;
            // With no prefix at all these maps hold the MMX forms; 0x66
            // selects the SSE ones, which is where the useful half lives.
            let mmx = !p.opsize;
            let t = match (op2 == 0x38, mmx) {
                (true, false) => table::THREE_BYTE_38_66[op3 as usize],
                (true, true) => table::THREE_BYTE_38[op3 as usize],
                (false, false) => table::THREE_BYTE_3A_66[op3 as usize],
                (false, true) => table::THREE_BYTE_3A[op3 as usize],
            };
            if t.m.is_empty() {
                return None;
            }
            p.opsize = false;
            return build(&mut c, &p, t, op3, true, addr, bytes);
        }
        // `endbr32` and `endbr64` are the only two allocations at 0x0f 0x1e,
        // and the ModRM byte picks between them rather than describing an
        // operand, so neither the table nor the operand walk can express it.
        if op2 == 0x1e && p.rep {
            let name = match c.peek() {
                Some(0xfa) => "endbr64",
                Some(0xfb) => "endbr32",
                _ => return None,
            };
            c.at += 1;
            return Some(Insn::new(addr, c.at as u8, name, Flow::Next));
        }
        // A mandatory prefix selects a different instruction entirely, and
        // REP/REPNE win over 0x66 when both are present.
        let t = if p.rep {
            table::TWO_BYTE_F3[op2 as usize]
        } else if p.repne {
            table::TWO_BYTE_F2[op2 as usize]
        } else if p.opsize {
            table::TWO_BYTE_66[op2 as usize]
        } else {
            table::TWO_BYTE[op2 as usize]
        };
        // Fall back to the unprefixed map when the prefixed one has no entry,
        // which is how 0x66 acts as a plain operand-size override on the
        // integer instructions that share the map.
        let t = if t.m.is_empty() && t.group == 0 {
            table::TWO_BYTE[op2 as usize]
        } else {
            t
        };
        (t, true, op2)
    } else if p.long() {
        (table::ONE_BYTE[op as usize], false, op)
    } else {
        (table::ONE_BYTE_32[op as usize], false, op)
    };

    if entry.m.is_empty() && entry.group == 0 {
        return None;
    }

    // The 0x66 that selected an SSE variant is a mandatory prefix, not an
    // operand-size override, so `movd xmm0, edi` keeps its 32-bit source.
    if two_byte && (p.opsize || p.rep || p.repne) {
        let prefixed = if p.rep {
            table::TWO_BYTE_F3[opcode as usize]
        } else if p.repne {
            table::TWO_BYTE_F2[opcode as usize]
        } else {
            table::TWO_BYTE_66[opcode as usize]
        };
        if !prefixed.m.is_empty() {
            p.opsize = false;
            p.rep = false;
            p.repne = false;
        }
    }
    // push, pop and the near call and jmp cannot be 32-bit in long mode.
    // Under 0xff only /2 to /6 are those; /0 and /1 are inc and dec, which
    // keep the ordinary operand size. None of this applies in 32-bit mode,
    // where the stack is four bytes wide and `0x66` is the only lever.
    let ff_is_default64 = opcode == 0xff && c.peek().is_some_and(|m| matches!((m >> 3) & 7, 2..=6));
    p.default64 = p.long()
        && !two_byte
        && (matches!(
            opcode,
            0x50..=0x5f | 0xe8 | 0xe9 | 0xc2 | 0xc3 | 0x8f | 0x68 | 0x6a
        ) || ff_is_default64);

    p.force_reg_rm = two_byte && matches!(opcode, 0x20..=0x23);

    build(&mut c, &p, entry, opcode, two_byte, addr, bytes)
}

/// Assemble the instruction from its table entry.
fn build(
    c: &mut Cursor<'_>,
    p: &Prefixes,
    entry: Entry,
    opcode: u8,
    two_byte: bool,
    addr: Addr,
    all: &[u8],
) -> Option<Insn> {
    // Any operand that reads ModRM does so once, before the immediate.
    let needs_modrm = entry.ops.iter().any(|o| {
        matches!(
            o,
            Op::Eb
                | Op::Ew
                | Op::Ed
                | Op::Ev
                | Op::Eq
                | Op::Gb
                | Op::Gw
                | Op::Gd
                | Op::Gv
                | Op::M
                | Op::Mp
                | Op::Vx
                | Op::Wx
                | Op::Ux
                | Op::Pq
                | Op::Qq
                | Op::Nq
                | Op::Ewm
                | Op::Ebm
                | Op::Sw
                | Op::Cd
                | Op::Dd
        )
    }) || entry.group != 0;

    // A group's slots can touch different amounts of memory, and a few touch
    // different amounts again when r/m is a register, so the size is looked up
    // from the ModRM byte before it is consumed.
    let group_size = if entry.group != 0 {
        c.peek().and_then(|m| {
            let sel = ((m >> 3) & 7) as usize;
            if m >> 6 == 3 {
                table::group_msize_reg(entry.group, sel)
            } else {
                table::group_msize(entry.group, sel)
            }
        })
    } else {
        None
    };
    // `lea` computes an address rather than accessing memory, and a far
    // pointer load names no scalar either, so neither prints a size hint.
    let rm_size = if entry.m == "lea" || entry.ops[1] == Op::Mp {
        0
    } else if let Some(n) = group_size {
        n as u64
    } else if entry.msize != 0 {
        entry.msize as u64
    } else {
        rm_size_of(&entry, p)
    };
    let modrm = if needs_modrm {
        Some(decode_modrm(c, p, rm_size)?)
    } else {
        None
    };

    // A group's ModRM reg field picks the mnemonic.
    let mut mnemonic = entry.m;
    let mut ops = entry.ops;
    if entry.group != 0 {
        let g = GROUPS.get(entry.group as usize - 1)?;
        let sel = (modrm.as_ref()?.reg & 7) as usize;
        mnemonic = g.0[sel];
        if mnemonic.is_empty() {
            return None;
        }
        // 0xf6 and 0xf7 /0 and /1 are both `test`, and both take an immediate
        // the table cannot know about until the group is resolved.
        if (entry.group == table::G_F6 || entry.group == table::G_F7) && sel <= 1 {
            ops[1] = if entry.group == table::G_F6 {
                Op::Ib
            } else {
                Op::Iz
            };
        }
        // `call`, `jmp` and `push` through 0xff are always 64-bit in long
        // mode. In 32-bit mode they take the ordinary operand size.
        if p.long() && entry.group == table::G_FF && matches!(sel, 2..=6) {
            ops[0] = Op::Eq;
        }
        // `psrldq` and `pslldq` shift a whole 128-bit vector along, so they
        // exist only in the 0x66 map. The MMX group shares the table with it
        // and those two slots of the MMX group are unallocated, which the
        // operand kind is what distinguishes.
        if matches!(mnemonic, "psrldq" | "pslldq") && entry.ops[0] == Op::Nq {
            return None;
        }
        // A far call or jump loads a segment and an offset from memory. The
        // register form is not a shorter spelling of it, it is an encoding the
        // processor faults on, and decoding one would hand the caller a
        // control flow edge that never exists.
        if entry.group == table::G_FF
            && matches!(sel, 3 | 5)
            && matches!(modrm.as_ref()?.rm, RmOperand::Reg(_))
        {
            return None;
        }
        // 0x0f 0xae is two groups sharing one opcode: the fences when r/m is a
        // register, the state-save instructions when it is memory.
        if entry.group == table::G_0FAE && matches!(modrm.as_ref()?.rm, RmOperand::Reg(_)) {
            mnemonic = GROUPS.get(table::G_0FAE_REG as usize - 1)?.0[sel];
            if mnemonic.is_empty() {
                return None;
            }
            ops = [Op::None; 3];
        }
    }

    // 0x0f 0x12 and 0x0f 0x16 load half a vector from memory, and with a
    // register source there is no half to load: the encoding names the
    // register-to-register move instead. The test is the mnemonic the table
    // already resolved rather than the prefix bytes, because `0xf3` and
    // `0xf2` reach these opcodes by two different routes: at 0x12 they select
    // a real instruction of their own, and at 0x16 only `0xf3` does, so `0xf2`
    // there falls back to `movhps` and takes this rewrite with it.
    if two_byte
        && matches!(opcode, 0x12 | 0x16)
        && matches!(mnemonic, "movlps" | "movlpd" | "movhps" | "movhpd")
        && matches!(modrm.as_ref()?.rm, RmOperand::Reg(_))
    {
        mnemonic = if mnemonic.starts_with("movl") {
            "movhlps"
        } else {
            "movlhps"
        };
        ops = [Op::Vx, Op::Ux, Op::None];
    }

    // These name memory and only memory: the non-temporal stores bypass the
    // cache, the half-vector moves transfer the half a register does not have,
    // and `lddqu` exists to cross a cache line. A register in r/m is a fault
    // rather than a shorter form, so the bytes are not an instruction. The
    // half-vector loads are not on this list because their register form is
    // `movhlps` and `movlhps`, which the rewrite above has already named.
    if matches!(
        mnemonic,
        "movlps"
            | "movhps"
            | "movlpd"
            | "movhpd"
            | "movntps"
            | "movntpd"
            | "movntss"
            | "movntsd"
            | "movntq"
            | "movntdq"
            | "movnti"
            | "lddqu"
    ) && matches!(modrm.as_ref()?.rm, RmOperand::Reg(_))
    {
        return None;
    }

    // llvm prints `xchg` with the ModRM reg operand first when r/m is also a
    // register, and the memory operand first when it is not. The table carries
    // the memory order, so the register form swaps.
    if !two_byte && matches!(opcode, 0x86 | 0x87) && matches!(modrm.as_ref()?.rm, RmOperand::Reg(_))
    {
        ops.swap(0, 1);
    }

    let moffs = ops.iter().any(|o| matches!(o, Op::Ob | Op::Ov));
    let mut i = Insn::new(addr, 0, mnemonic, Flow::Next);

    for kind in ops.iter() {
        if *kind == Op::None {
            continue;
        }
        let operand = match kind {
            Op::Eb | Op::Ew | Op::Ed | Op::Ev | Op::Eq | Op::M | Op::Mp => {
                let m = modrm.as_ref()?;
                let w = width_of(rm_size);
                match &m.rm {
                    RmOperand::Reg(r) => {
                        if matches!(kind, Op::M | Op::Mp) {
                            return None; // memory-only form with a register
                        }
                        Operand::Reg(gpr(*r, w, p.rex))
                    }
                    RmOperand::Mem(mem) => Operand::Mem(*mem),
                }
            }
            Op::Wx | Op::Ux => {
                let m = modrm.as_ref()?;
                match &m.rm {
                    RmOperand::Reg(r) => Operand::Reg(xmm(*r)),
                    RmOperand::Mem(mem) => {
                        if *kind == Op::Ux {
                            return None;
                        }
                        Operand::Mem(*mem)
                    }
                }
            }
            Op::Qq | Op::Nq => {
                let m = modrm.as_ref()?;
                match &m.rm {
                    RmOperand::Reg(r) => Operand::Name(MM[(*r & 7) as usize]),
                    RmOperand::Mem(mem) => {
                        if *kind == Op::Nq {
                            return None;
                        }
                        Operand::Mem(*mem)
                    }
                }
            }
            // The segment store writes a word to memory and the whole register
            // when the destination is one.
            Op::Ewm | Op::Ebm => {
                let m = modrm.as_ref()?;
                let size = if *kind == Op::Ebm { 1 } else { 2 };
                match &m.rm {
                    RmOperand::Reg(r) => Operand::Reg(gpr(*r, p.width(), p.rex)),
                    RmOperand::Mem(mem) => Operand::Mem(Mem { size, ..*mem }),
                }
            }
            Op::Gb => Operand::Reg(gpr(modrm.as_ref()?.reg, Width::W8, p.rex)),
            Op::Gw => Operand::Reg(gpr(modrm.as_ref()?.reg, Width::W16, p.rex)),
            Op::Gd => Operand::Reg(gpr(modrm.as_ref()?.reg, Width::W32, p.rex)),
            Op::Gv => Operand::Reg(gpr(modrm.as_ref()?.reg, p.width(), p.rex)),
            Op::Vx => Operand::Reg(xmm(modrm.as_ref()?.reg)),
            Op::Pq => Operand::Name(MM[(modrm.as_ref()?.reg & 7) as usize]),
            Op::Sw => Operand::Reg(Reg {
                class: RegClass::Seg,
                num: modrm.as_ref()?.reg & 7,
                width: Width::W16,
            }),
            Op::Sr => Operand::Reg(Reg {
                class: RegClass::Seg,
                num: (opcode >> 3) & 7,
                width: Width::W16,
            }),
            Op::Cd => Operand::Reg(Reg {
                class: RegClass::Sys,
                num: modrm.as_ref()?.reg,
                width: Width::W64,
            }),
            // A debug register is not a control register, and [`RegClass`] has
            // one system class for both, so this one prints by name.
            Op::Dd => Operand::Name(DR[(modrm.as_ref()?.reg & 15) as usize]),
            // A far pointer immediate is stored offset first and printed
            // segment first, and llvm prints the segment as a signed word.
            Op::Ap => {
                let off = if p.opsize { c.u16()? } else { c.u32()? };
                let seg = c.u16()? as u16 as i16 as i64;
                i.push(Operand::Imm(seg));
                Operand::UImm(off)
            }
            // An immediate prints as the bytes encode it, unsigned at its own
            // width, except where the encoding sign-extends into a wider
            // operand: `add rax, -0x1` really is minus one.
            Op::Ib | Op::Ibs => Operand::Imm(c.i8()?),
            Op::Ibu => Operand::UImm(c.u8()? as u64),
            Op::Iw => Operand::Imm(c.i16()?),
            Op::Id => Operand::UImm(c.u32()?),
            Op::Iz => {
                if p.opsize && !p.w {
                    Operand::UImm(c.u16()?)
                } else if p.w {
                    Operand::Imm(c.i32()?)
                } else {
                    Operand::UImm(c.u32()?)
                }
            }
            Op::Iv => {
                if p.w {
                    Operand::UImm(c.u64()?)
                } else if p.opsize {
                    Operand::UImm(c.u16()?)
                } else {
                    Operand::UImm(c.u32()?)
                }
            }
            Op::Jb => {
                let d = c.i8()?;
                Operand::Addr(branch(p, addr, c.at as i64 + d))
            }
            Op::Jz => {
                let d = if p.opsize { c.i16()? } else { c.i32()? };
                Operand::Addr(branch(p, addr, c.at as i64 + d))
            }
            Op::AL => Operand::Reg(gpr(0, Width::W8, p.rex)),
            Op::EAX => Operand::Reg(gpr(0, p.width(), p.rex)),
            Op::CL => Operand::Reg(gpr(1, Width::W8, p.rex)),
            Op::DX => Operand::Reg(gpr(2, Width::W16, p.rex)),
            Op::Rb => Operand::Reg(gpr(
                (opcode & 7) | if p.b { 8 } else { 0 },
                Width::W8,
                p.rex,
            )),
            Op::Rv => Operand::Reg(gpr(
                (opcode & 7) | if p.b { 8 } else { 0 },
                p.width(),
                p.rex,
            )),
            Op::Ob | Op::Ov => Operand::Mem(Mem {
                seg: p.seg.map(|r| Reg {
                    class: RegClass::Seg,
                    num: r,
                    width: Width::W16,
                }),
                base: None,
                index: None,
                // An absolute offset is as wide as the address size, so it is
                // eight bytes only in long mode without `0x67`.
                disp: match p.addr_bytes() {
                    2 => c.u16()? as i64,
                    4 => c.u32()? as i64,
                    _ => c.u64()? as i64,
                },
                mode: AddrMode::Offset,
                size: if *kind == Op::Ob { 1 } else { p.opsize_bytes() },
            }),
            Op::XMM0 => Operand::Reg(xmm(0)),
            Op::One => Operand::Imm(1),
            Op::None => continue,
        };
        i.push(operand);
    }

    let len = c.at;
    if len == 0 || len > 15 {
        return None;
    }
    i.len = len as u8;

    i.flow = flow_of(mnemonic, two_byte, opcode, &i);
    i.mnemonic = rename(mnemonic, p, &i);
    // An absolute-offset move is `movabs` in long mode whatever it moves.
    if p.long() && !two_byte && matches!(opcode, 0xa0..=0xa3) {
        i.mnemonic = "movabs";
    }
    // `aam` and `aad` hide the base-ten immediate they almost always carry.
    if matches!(i.mnemonic, "aam" | "aad") && i.operands() == [Operand::Imm(10)] {
        i = Insn::new(i.addr, i.len, i.mnemonic, i.flow);
    }
    // llvm's sixteen-bit forms of `ret`, `retf` and the far branches print
    // their word operand unsigned, where the 32-bit forms print it signed.
    if !two_byte && p.opsize && matches!(opcode, 0xc2 | 0xca | 0x9a | 0xea) {
        if let Some(Operand::Imm(v)) = i.operands().first().copied() {
            i.set_operand(0, Operand::UImm(v as u16 as u64));
        }
    }
    // A 64-bit immediate move reads as a signed number, which is how a
    // negative constant written in source appears again in the listing.
    if i.mnemonic == "movabs" {
        if let Some(Operand::UImm(v)) = i.operands().get(1).copied() {
            i.set_operand(1, Operand::Imm(v as i64));
        }
    }
    if let Some(with_ops) = string_operands(&i, p) {
        i = with_ops;
    }
    // `cmpps` and friends fold their predicate immediate into the mnemonic.
    if let Some(folded) = fold_compare_predicate(&i) {
        i = folded;
    }
    if let Some(with_ops) = string_operands(&i, p) {
        i = with_ops;
    }
    // `lock`, `rep` and `repne` modify the whole instruction. `rep` and
    // `repne` are only prefixes on the string instructions; elsewhere the
    // same bytes select a different opcode entirely.
    // llvm names the address size when the operand shows no register to imply
    // it, which is the 16-bit absolute form and nothing else.
    // llvm names the address size whenever no operand implies it: either there
    // is no memory operand at all, or the one there is has no base and no
    // index register. An absolute offset is the exception, since its own
    // opcode already says how wide it is.
    let addr_override =
        !moffs && !matches!(i.mnemonic, "jcxz" | "jecxz" | "jrcxz") && names_addr_size(p, &i);
    // llvm prints a repeat prefix only on a one-byte opcode. On a two-byte one
    // the byte is a mandatory prefix slot, and an opcode that does not use it
    // drops it rather than reporting it.
    let repeat = i.mnemonic != "pause" && (!two_byte || !p.repeat_is_mandatory);
    i.prefix = prefix_text(
        if p.lock {
            Some("lock")
        } else if p.rep && repeat {
            Some("rep")
        } else if p.repne && repeat {
            Some("repne")
        } else {
            None
        },
        addr_override.then_some(addr_prefix_name(p)),
    );
    let _ = all;
    Some(i)
}

/// Whether llvm spells the address-size override out in front of the mnemonic.
/// It does so when no operand implies the size: either there is no memory
/// operand at all, or the one there is has no base and no index register and
/// so shows no register whose width would give the answer away.
fn names_addr_size(p: &Prefixes, i: &Insn) -> bool {
    p.addrsize
        && i.operands()
            .iter()
            .all(|o| !matches!(o, Operand::Mem(m) if m.base.is_some() || m.index.is_some()))
}

/// The name of the address size `0x67` selects, which is the other one.
fn addr_prefix_name(p: &Prefixes) -> &'static str {
    if p.long() { "addr32" } else { "addr16" }
}

/// `cmpps xmm0, xmm1, 2` is spelled `cmpleps xmm0, xmm1`: the predicate
/// immediate is part of the name. Predicates past seven keep the raw form.
fn fold_compare_predicate(i: &Insn) -> Option<Insn> {
    let stem = match i.mnemonic {
        "cmpps" => "ps",
        "cmppd" => "pd",
        "cmpss" => "ss",
        "cmpsd" if i.operands().len() == 3 => "sd",
        _ => return None,
    };
    let pred = match i.operands().get(2)? {
        Operand::UImm(v) if *v < 8 => *v as usize,
        _ => return None,
    };
    let name: &'static str = match (stem, table::CMP_PRED[pred]) {
        ("ps", p) => concat_pred("ps", p)?,
        ("pd", p) => concat_pred("pd", p)?,
        ("ss", p) => concat_pred("ss", p)?,
        (_, p) => concat_pred("sd", p)?,
    };
    let mut out = Insn::new(i.addr, i.len, name, i.flow);
    out.prefix = i.prefix;
    out.push(*i.operands().first()?);
    out.push(*i.operands().get(1)?);
    Some(out)
}

/// Every `cmp<pred><kind>` name as a static string, since [`Insn`] holds one.
fn concat_pred(kind: &str, pred: &str) -> Option<&'static str> {
    const NAMES: [&str; 32] = [
        "cmpeqps",
        "cmpltps",
        "cmpleps",
        "cmpunordps",
        "cmpneqps",
        "cmpnltps",
        "cmpnleps",
        "cmpordps",
        "cmpeqpd",
        "cmpltpd",
        "cmplepd",
        "cmpunordpd",
        "cmpneqpd",
        "cmpnltpd",
        "cmpnlepd",
        "cmpordpd",
        "cmpeqss",
        "cmpltss",
        "cmpless",
        "cmpunordss",
        "cmpneqss",
        "cmpnltss",
        "cmpnless",
        "cmpordss",
        "cmpeqsd",
        "cmpltsd",
        "cmplesd",
        "cmpunordsd",
        "cmpneqsd",
        "cmpnltsd",
        "cmpnlesd",
        "cmpordsd",
    ];
    let k = ["ps", "pd", "ss", "sd"].iter().position(|x| *x == kind)?;
    let p = table::CMP_PRED.iter().position(|x| *x == pred)?;
    NAMES.get(k * 8 + p).copied()
}

/// `es:[rdi]` and `[rsi]`, the implicit operands of the string instructions.
///
/// They carry no ModRM, so the table has no operands for them, but every
/// disassembler prints them because they are what the instruction touches.
fn string_operands(i: &Insn, p: &Prefixes) -> Option<Insn> {
    let (name, size) = match i.mnemonic {
        m if matches!(m, "insb" | "insw" | "insd" | "outsb" | "outsw" | "outsd")
            || m.starts_with("movs")
            || m.starts_with("stos")
            || m.starts_with("lods")
            || m.starts_with("scas")
            || m.starts_with("cmps") =>
        {
            let size = match m.as_bytes().last()? {
                b'b' => 1,
                b'w' => 2,
                b'q' => 8,
                _ => 4,
            };
            (m, size)
        }
        _ => return None,
    };
    if !i.operands().is_empty() {
        return None; // an SSE movsd, not the string one
    }

    let es = Reg {
        class: RegClass::Seg,
        num: 0,
        width: Width::W16,
    };
    let aw = p.addr_width();
    let di = Mem {
        seg: Some(es),
        base: Some(Reg::gpr(7, aw)),
        index: None,
        disp: 0,
        mode: AddrMode::Offset,
        size,
    };
    let si = Mem {
        // A segment override applies to the source, which is the only string
        // operand whose segment is not fixed at `es`.
        seg: p.seg.map(|r| Reg {
            class: RegClass::Seg,
            num: r,
            width: Width::W16,
        }),
        base: Some(Reg::gpr(6, aw)),
        index: None,
        disp: 0,
        mode: AddrMode::Offset,
        size,
    };
    let acc = Operand::Reg(gpr(0, width_of(size), p.rex));

    let mut out = Insn::new(i.addr, i.len, i.mnemonic, i.flow);
    out.prefix = i.prefix;
    match if name.starts_with("ins") {
        name
    } else {
        &name[..4]
    } {
        "movs" => {
            out.push(Operand::Mem(di));
            out.push(Operand::Mem(si));
        }
        "stos" => {
            out.push(Operand::Mem(di));
            out.push(acc);
        }
        "lods" => {
            out.push(acc);
            out.push(Operand::Mem(si));
        }
        "scas" => {
            out.push(acc);
            out.push(Operand::Mem(di));
        }
        "cmps" => {
            out.push(Operand::Mem(si));
            out.push(Operand::Mem(di));
        }
        "insb" | "insw" | "insd" => {
            out.push(Operand::Mem(di));
            out.push(Operand::Reg(Reg::gpr(2, Width::W16)));
        }
        "outs" => {
            out.push(Operand::Reg(Reg::gpr(2, Width::W16)));
            out.push(Operand::Mem(si));
        }
        _ => return None,
    }
    Some(out)
}

/// The size in bytes of the ModRM r/m operand for this entry.
fn rm_size_of(entry: &Entry, p: &Prefixes) -> u64 {
    for o in &entry.ops {
        match o {
            Op::Eb => return 1,
            Op::Ew => return 2,
            Op::Ed => return 4,
            Op::Eq => return p.forced_qword(),
            Op::Ev | Op::Ewm => return p.opsize_bytes(),
            Op::Wx | Op::Ux => return 16,
            Op::Qq | Op::Nq => return 8,
            _ => {}
        }
    }
    p.opsize_bytes()
}

/// Control flow for a decoded instruction.
fn flow_of(m: &str, two_byte: bool, opcode: u8, i: &Insn) -> Flow {
    let direct = i.operands().first().and_then(|o| match o {
        Operand::Addr(a) => Some(*a),
        _ => None,
    });
    match m {
        "call" => match direct {
            Some(a) => Flow::Call(a),
            None => Flow::IndirectCall,
        },
        "jmp" => match direct {
            Some(a) => Flow::Branch(a),
            None => Flow::IndirectBranch,
        },
        "ret" | "lret" | "iret" | "sysret" | "sysexit" => Flow::Return,
        "hlt" | "ud2" => Flow::Trap,
        "int3" => Flow::Trap,
        "int" | "syscall" | "sysenter" => Flow::Syscall,
        "loop" | "loope" | "loopne" | "jrcxz" => match direct {
            Some(a) => Flow::CondBranch(a),
            None => Flow::Next,
        },
        _ => {
            // The conditional jumps, in both their short and near forms.
            let is_jcc = (!two_byte && (0x70..0x80).contains(&opcode))
                || (two_byte && (0x80..0x90).contains(&opcode));
            match (is_jcc, direct) {
                (true, Some(a)) => Flow::CondBranch(a),
                _ => Flow::Next,
            }
        }
    }
}

/// Spellings that depend on the prefixes or the operands.
/// A relative branch target. The program counter is as wide as the mode, so a
/// 32-bit branch that runs off the top of the address space wraps there rather
/// than reaching into the 64-bit range.
fn branch(p: &Prefixes, addr: Addr, delta: i64) -> Addr {
    let to = addr.wrapping_offset(delta);
    if p.long() {
        to
    } else {
        Addr(to.get() & 0xffff_ffff)
    }
}

/// Two prefixes can want printing at once, and [`Insn`] holds one string, so
/// the pairs are spelled out. The tab pair is what llvm puts between them.
fn prefix_text(repeat: Option<&'static str>, addr: Option<&'static str>) -> Option<&'static str> {
    Some(match (repeat, addr) {
        (None, None) => return None,
        (Some(r), None) => r,
        (None, Some(a)) => a,
        (Some("lock"), Some("addr16")) => "lock\t\taddr16",
        (Some("lock"), Some(_)) => "lock\t\taddr32",
        (Some("rep"), Some("addr16")) => "rep\t\taddr16",
        (Some("rep"), Some(_)) => "rep\t\taddr32",
        (Some(_), Some("addr16")) => "repne\t\taddr16",
        (Some(_), Some(_)) => "repne\t\taddr32",
    })
}

fn is_indirect(i: &Insn) -> bool {
    matches!(i.operands().first(), Some(Operand::Mem(_)))
}

fn rename(m: &'static str, p: &Prefixes, i: &Insn) -> &'static str {
    // The string instructions take their size from the operand size, and the
    // table carries only the doubleword spelling.
    let sized = |b: &'static str, w: &'static str, d: &'static str, q: &'static str| match p
        .opsize_bytes()
    {
        2 => w,
        8 => q,
        _ => {
            let _ = b;
            d
        }
    };
    let base = match m {
        "movsd" if i.operands().is_empty() => sized("movsb", "movsw", "movsd", "movsq"),
        "cmpsd" if i.operands().is_empty() => sized("cmpsb", "cmpsw", "cmpsd", "cmpsq"),
        "stosd" => sized("stosb", "stosw", "stosd", "stosq"),
        "lodsd" => sized("lodsb", "lodsw", "lodsd", "lodsq"),
        "scasd" => sized("scasb", "scasw", "scasd", "scasq"),
        "insd" => sized("insb", "insw", "insd", "insd"),
        "outsd" => sized("outsb", "outsw", "outsd", "outsd"),
        "cwde" => match p.opsize_bytes() {
            2 => "cbw",
            8 => "cdqe",
            _ => "cwde",
        },
        "cdq" => match p.opsize_bytes() {
            2 => "cwd",
            8 => "cqo",
            _ => "cdq",
        },
        // The flag transfers and the counted loops name their own width, and
        // llvm leaves the 16-bit forms unsuffixed.
        "iret" => match p.opsize_bytes() {
            2 => "iret",
            8 => "iretq",
            _ => "iretd",
        },
        // llvm spells the far return `retf`, and suffixes only the 64-bit one.
        "lret" => match p.opsize_bytes() {
            8 => "retfq",
            _ => "retf",
        },
        // The descriptor table instructions take a `d` in 32-bit mode, where
        // the operand they load is six bytes rather than ten.
        // The descriptor table instructions carry the operand size in their
        // name outside long mode, where the table pointer is six bytes rather
        // than ten.
        "sgdt" | "sidt" | "lgdt" | "lidt" if !p.long() => {
            let w = p.opsize_bytes() == 2;
            match (m, w) {
                ("sgdt", true) => "sgdtw",
                ("sgdt", _) => "sgdtd",
                ("sidt", true) => "sidtw",
                ("sidt", _) => "sidtd",
                ("lgdt", true) => "lgdtw",
                ("lgdt", _) => "lgdtd",
                (_, true) => "lidtw",
                _ => "lidtd",
            }
        }
        "pushal" if p.opsize => "pushaw",
        "popal" if p.opsize => "popaw",
        // 0xf3 0x90 is its own instruction, not a repeated `nop`.
        "nop" if p.rep && i.operands().is_empty() => "pause",
        "pushf" => match p.opsize_bytes() {
            2 => "pushf",
            8 => "pushfq",
            _ => "pushfd",
        },
        "popf" => match p.opsize_bytes() {
            2 => "popf",
            8 => "popfq",
            _ => "popfd",
        },
        "jrcxz" => match p.addr_bytes() {
            2 => "jcxz",
            8 => "jrcxz",
            _ => "jecxz",
        },
        // 0xff /3 and /5 are the far indirect branches, which llvm spells
        // `call` and `jmp` at 32 and 64 bits and `lcall` and `ljmp` at 16.
        // The 0x9a and 0xea forms keep the long name at every size, and they
        // are the ones whose operand is an immediate rather than memory.
        "lcall" if p.opsize_bytes() != 2 && is_indirect(i) => "call",
        "ljmp" if p.opsize_bytes() != 2 && is_indirect(i) => "jmp",
        // The 64-bit form of movd has its own name.
        "movd" if p.w => "movq",
        // A 64-bit immediate move has its own name.
        "mov" if p.w && matches!(i.operands().get(1), Some(Operand::UImm(_))) && i.len >= 10 => {
            "movabs"
        }
        other => other,
    };
    let _ = CC;
    base
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dis(bytes: &[u8]) -> String {
        let i = decode(bytes, Addr(0x1000)).expect("decode");
        assert_eq!(i.len as usize, bytes.len(), "length mismatch");
        format(&i, Style::default())
    }

    #[test]
    fn the_basics() {
        assert_eq!(dis(&[0x85, 0xff]), "test\tedi, edi");
        assert_eq!(dis(&[0x89, 0xf9]), "mov\tecx, edi");
        assert_eq!(dis(&[0x31, 0xc0]), "xor\teax, eax");
        assert_eq!(dis(&[0xc3]), "ret");
    }

    #[test]
    fn rex_w_widens_to_64_bits() {
        assert_eq!(dis(&[0x48, 0x89, 0xf9]), "mov\trcx, rdi");
        assert_eq!(dis(&[0x48, 0x0f, 0xaf, 0xc1]), "imul\trax, rcx");
    }

    #[test]
    fn rex_r_and_b_reach_the_high_registers() {
        assert_eq!(dis(&[0x4d, 0x89, 0xc1]), "mov\tr9, r8");
    }

    #[test]
    fn without_rex_the_high_byte_registers_are_named() {
        // 0x88 /r with reg=4 is ah, not spl.
        assert_eq!(dis(&[0x88, 0xe0]), "mov\tal, ah");
        // With any REX byte it is spl.
        assert_eq!(dis(&[0x40, 0x88, 0xe0]), "mov\tal, spl");
    }

    #[test]
    fn memory_operands_print_intel_style() {
        assert_eq!(dis(&[0x8d, 0x47, 0xff]), "lea\teax, [rdi - 0x1]");
        assert_eq!(
            dis(&[0x8b, 0x04, 0x88]),
            "mov\teax, dword ptr [rax + 4*rcx]"
        );
    }

    #[test]
    fn rip_relative_keeps_the_encoded_displacement() {
        // The text says what the bytes say; analysis resolves the target.
        let i = decode(&[0x48, 0x8d, 0x05, 0x10, 0x00, 0x00, 0x00], Addr(0x1000)).unwrap();
        assert_eq!(i.len, 7);
        assert_eq!(format(&i, Style::default()), "lea\trax, [rip + 0x10]");
        let Operand::Mem(m) = i.operands()[1] else {
            panic!("expected a memory operand");
        };
        assert!(m.is_pc_relative());
        // 0x1000 + 7 + 0x10.
        assert_eq!(m.pc_target(i.end()), Some(Addr(0x1017)));
    }

    #[test]
    fn a_call_carries_its_target() {
        // e8 rel32 at 0x1000, 5 bytes, displacement 0x10 -> 0x1015.
        let i = decode(&[0xe8, 0x10, 0x00, 0x00, 0x00], Addr(0x1000)).unwrap();
        assert_eq!(i.flow, Flow::Call(Addr(0x1015)));
    }

    #[test]
    fn a_conditional_jump_has_both_successors() {
        let i = decode(&[0x78, 0x0f], Addr(0x1000)).unwrap();
        assert_eq!(i.flow, Flow::CondBranch(Addr(0x1011)));
        assert!(i.flow.falls_through());
    }

    #[test]
    fn groups_pick_their_mnemonic_from_modrm() {
        // 83 /5 ib is sub, /0 is add.
        assert_eq!(dis(&[0x83, 0xe8, 0x01]), "sub\teax, 0x1");
        assert_eq!(dis(&[0x83, 0xc0, 0x01]), "add\teax, 0x1");
        // f7 /3 is neg, and takes no immediate.
        assert_eq!(dis(&[0xf7, 0xd8]), "neg\teax");
        // f7 /0 is test, and does.
        assert_eq!(dis(&[0xf7, 0xc0, 0x01, 0x00, 0x00, 0x00]), "test\teax, 0x1");
    }

    #[test]
    fn shifts_by_one_are_implicit() {
        assert_eq!(dis(&[0x48, 0xd1, 0xe8]), "shr\trax");
    }

    #[test]
    fn mandatory_prefixes_select_a_different_instruction() {
        assert_eq!(dis(&[0x0f, 0x10, 0xc1]), "movups\txmm0, xmm1");
        assert_eq!(dis(&[0x66, 0x0f, 0x10, 0xc1]), "movupd\txmm0, xmm1");
        assert_eq!(dis(&[0xf3, 0x0f, 0x10, 0xc1]), "movss\txmm0, xmm1");
        assert_eq!(dis(&[0xf2, 0x0f, 0x10, 0xc1]), "movsd\txmm0, xmm1");
    }

    #[test]
    fn nothing_decodes_past_fifteen_bytes() {
        // A pile of prefixes with no opcode must not produce an instruction.
        assert!(decode(&[0x66; 32], Addr(0x1000)).is_none());
    }

    #[test]
    fn a_truncated_instruction_is_not_decoded() {
        assert!(decode(&[0xe8, 0x10], Addr(0x1000)).is_none());
        assert!(decode(&[], Addr(0x1000)).is_none());
    }

    #[test]
    fn no_byte_sequence_panics() {
        let mut buf = [0u8; 8];
        for seed in 0u32..20000 {
            let mut x = seed.wrapping_mul(2654435761);
            for b in buf.iter_mut() {
                x = x.wrapping_mul(1103515245).wrapping_add(12345);
                *b = (x >> 16) as u8;
            }
            let _ = decode(&buf, Addr(0x1000));
        }
    }
}
