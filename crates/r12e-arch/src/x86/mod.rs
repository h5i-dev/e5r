//! x86-64 decoder.
//!
//! Variable length, so decoding is a walk: legacy prefixes, then REX, then one
//! to three opcode bytes, then ModRM and SIB, then a displacement, then an
//! immediate. Each stage can end the instruction, and the length is whatever
//! the walk consumed.
//!
//! Only 64-bit mode. The opcodes 32-bit mode spends on `inc`/`dec`, `pusha`
//! and the BCD instructions are REX prefixes here, and pretending otherwise is
//! how a disassembler desynchronizes on the first byte.

pub mod table;
pub mod text;

pub use text::{Style, format};

use r12e_core::Addr;

use crate::insn::{AddrMode, Flow, Insn, Mem, Operand, Reg, RegClass, Width};
use table::{CC, Entry, GROUPS, Op};

/// The prefixes and fields gathered before the opcode is looked up.
#[derive(Default, Clone, Copy)]
struct Prefixes {
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
    /// The opcode defaults to 64-bit operands in long mode, so `push rbp`
    /// needs no REX.W. True for push, pop, near call and near jmp.
    default64: bool,
}

impl Prefixes {
    /// The operand size in bytes for an `Ev`-style operand.
    fn opsize_bytes(&self) -> u64 {
        if self.w || (self.default64 && !self.opsize) {
            8
        } else if self.opsize {
            2
        } else {
            4
        }
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

fn xmm(num: u8) -> Reg {
    Reg {
        class: RegClass::Vec,
        num,
        width: Width::W128,
    }
}

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

/// Decode ModRM plus any SIB and displacement, in 64-bit mode.
fn decode_modrm(c: &mut Cursor<'_>, p: &Prefixes, size: u64) -> Option<ModRm> {
    let modrm = c.u8()?;
    let md = modrm >> 6;
    let reg = ((modrm >> 3) & 7) | if p.r { 8 } else { 0 };
    let rm = modrm & 7;

    if md == 3 {
        return Some(ModRm {
            reg,
            rm: RmOperand::Reg(rm | if p.b { 8 } else { 0 }),
        });
    }

    let addr_width = if p.addrsize { Width::W32 } else { Width::W64 };
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
        // Index 4 without REX.X means no index at all.
        if idx != 4 {
            index = Some((gpr(idx, addr_width, true), crate::insn::Extend::Lsl, scale));
        }
        // Base 5 with mod 0 means a 32-bit displacement and no base.
        if sib & 7 == 5 && md == 0 {
            disp = c.i32()?;
        } else {
            base = Some(gpr(bse, addr_width, true));
        }
    } else if rm == 5 && md == 0 {
        // RIP-relative, the 64-bit replacement for absolute addressing.
        disp = c.i32()?;
        rip_relative = true;
    } else {
        base = Some(gpr(rm | if p.b { 8 } else { 0 }, addr_width, true));
    }

    match md {
        1 => disp = disp.wrapping_add(c.i8()?),
        2 => disp = disp.wrapping_add(c.i32()?),
        _ => {}
    }

    let seg = p.seg.map(|s| Reg {
        class: RegClass::Seg,
        num: s,
        width: Width::W16,
    });

    if rip_relative {
        // The displacement stays as the bytes encode it, relative to the end
        // of the instruction. Resolving it here would make the text disagree
        // with the encoding; `Mem::rip_target` does it for analysis.
        base = Some(Reg {
            class: RegClass::Pc,
            num: 0,
            width: Width::W64,
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

/// Decode one instruction at `addr`.
pub fn decode(bytes: &[u8], addr: Addr) -> Option<Insn> {
    let mut c = Cursor { b: bytes, at: 0 };
    let mut p = Prefixes::default();

    // Legacy prefixes, then at most one REX immediately before the opcode.
    loop {
        match c.peek()? {
            0x66 => p.opsize = true,
            0x67 => p.addrsize = true,
            0xf0 => p.lock = true,
            0xf2 => p.repne = true,
            0xf3 => p.rep = true,
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
        if (0x40..0x50).contains(&b) {
            p.rex = true;
            p.w = b & 8 != 0;
            p.r = b & 4 != 0;
            p.x = b & 2 != 0;
            p.b = b & 1 != 0;
            c.at += 1;
        }
    }

    let op = c.u8()?;
    let (entry, two_byte, opcode) = if op == 0x0f {
        let op2 = c.u8()?;
        // The three-byte maps, which is where SSSE3 and SSE4 live.
        if op2 == 0x38 || op2 == 0x3a {
            let op3 = c.u8()?;
            let t = if op2 == 0x38 {
                table::THREE_BYTE_38_66[op3 as usize]
            } else {
                table::THREE_BYTE_3A_66[op3 as usize]
            };
            if t.m.is_empty() {
                return None;
            }
            p.opsize = false;
            return build(&mut c, &p, t, op3, true, addr, bytes);
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
    } else {
        (table::ONE_BYTE[op as usize], false, op)
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
        }
    }
    // push, pop and the near call and jmp cannot be 32-bit in long mode.
    // Under 0xff only /2 to /6 are those; /0 and /1 are inc and dec, which
    // keep the ordinary operand size.
    let ff_is_default64 = opcode == 0xff && c.peek().is_some_and(|m| matches!((m >> 3) & 7, 2..=6));
    p.default64 = !two_byte
        && (matches!(
            opcode,
            0x50..=0x5f | 0xe8 | 0xe9 | 0xc2 | 0xc3 | 0x8f | 0x68 | 0x6a
        ) || ff_is_default64);

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
                | Op::Sw
                | Op::Cd
                | Op::Dd
        )
    }) || entry.group != 0;

    // `lea` computes an address rather than accessing memory, so its operand
    // carries no size and no `ptr` hint is printed for it.
    let rm_size = if entry.m == "lea" {
        0
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
        // `call`, `jmp` and `push` through 0xff are always 64-bit here.
        if entry.group == table::G_FF && matches!(sel, 2..=6) {
            ops[0] = Op::Eq;
        }
    }

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
            Op::Qq => {
                let m = modrm.as_ref()?;
                match &m.rm {
                    RmOperand::Reg(r) => Operand::Reg(xmm(*r)),
                    RmOperand::Mem(mem) => Operand::Mem(*mem),
                }
            }
            Op::Gb => Operand::Reg(gpr(modrm.as_ref()?.reg, Width::W8, p.rex)),
            Op::Gw => Operand::Reg(gpr(modrm.as_ref()?.reg, Width::W16, p.rex)),
            Op::Gd => Operand::Reg(gpr(modrm.as_ref()?.reg, Width::W32, p.rex)),
            Op::Gv => Operand::Reg(gpr(modrm.as_ref()?.reg, p.width(), p.rex)),
            Op::Vx | Op::Pq => Operand::Reg(xmm(modrm.as_ref()?.reg)),
            Op::Sw => Operand::Reg(Reg {
                class: RegClass::Seg,
                num: modrm.as_ref()?.reg & 7,
                width: Width::W16,
            }),
            Op::Cd | Op::Dd => Operand::Reg(Reg {
                class: RegClass::Sys,
                num: modrm.as_ref()?.reg,
                width: Width::W64,
            }),
            // An immediate prints as the bytes encode it, unsigned at its own
            // width, except where the encoding sign-extends into a wider
            // operand: `add rax, -0x1` really is minus one.
            Op::Ib => Operand::UImm(c.u8()? as u64),
            Op::Ibs => Operand::Imm(c.i8()?),
            Op::Iw => Operand::UImm(c.u16()?),
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
                Operand::Addr(addr.wrapping_offset(c.at as i64 + d))
            }
            Op::Jz => {
                let d = if p.opsize { c.i16()? } else { c.i32()? };
                Operand::Addr(addr.wrapping_offset(c.at as i64 + d))
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
                seg: None,
                base: None,
                index: None,
                disp: c.u64()? as i64,
                mode: AddrMode::Offset,
                size: if *kind == Op::Ob { 1 } else { p.opsize_bytes() },
            }),
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
    i.prefix = if p.lock {
        Some("lock")
    } else if i
        .operands()
        .iter()
        .any(|o| matches!(o, Operand::Mem(m) if m.seg.is_some()))
    {
        if p.rep {
            Some("rep")
        } else if p.repne {
            Some("repne")
        } else {
            None
        }
    } else {
        None
    };
    let _ = all;
    Some(i)
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
        m if m.starts_with("movs")
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
    let di = Mem {
        seg: Some(es),
        base: Some(Reg::gpr(7, Width::W64)),
        index: None,
        disp: 0,
        mode: AddrMode::Offset,
        size,
    };
    let si = Mem {
        seg: None,
        base: Some(Reg::gpr(6, Width::W64)),
        index: None,
        disp: 0,
        mode: AddrMode::Offset,
        size,
    };
    let acc = Operand::Reg(gpr(0, width_of(size), p.rex));

    let mut out = Insn::new(i.addr, i.len, i.mnemonic, i.flow);
    out.prefix = i.prefix;
    match &name[..4] {
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
            Op::Eq => return 8,
            Op::Ev => return p.opsize_bytes(),
            Op::Wx | Op::Ux | Op::Qq => return 16,
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
        "pushf" => "pushfq",
        "popf" => "popfq",
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
