//! x86-64 encoding: one [`Insn`] to between one and fifteen bytes.
//!
//! REX is computed rather than tabulated. Every form decides an operand size
//! and a set of register numbers, and the prefix falls out of those two facts:
//! W from the size, R, X and B from whichever register numbers reach past
//! seven. A table of REX bytes per opcode is a table that goes wrong quietly
//! the first time a form is added, which is the failure this crate cannot have.
//!
//! Where more than one encoding exists the shortest is chosen, except where
//! the shorter one decodes to a different [`Insn`] than the text named. That
//! exception is what keeps the round trip exact: `shl eax, 0x1` encodes as the
//! count form rather than the one-byte `d1` shift, because the decoder prints
//! `d1` with no count at all and the two would not compare equal.

use r12e_arch::insn::{AddrMode, Insn, Mem, Operand, Reg, RegClass, Width};
use r12e_core::Addr;

use crate::Encoded;
use crate::error::AsmError;

// ------------------------------------------------------------------- naming

/// Every mnemonic this encoder accepts.
///
/// Sorted, because the lookup is a binary search and because a duplicate or a
/// stray entry shows up as a failing sort test rather than as a wrong encoding.
const MNEMONICS: &[&str] = &[
    "adc", "add", "and", "bsf", "bsr", "bswap", "bt", "btc", "btr", "bts", "call", "cbw", "cdq",
    "cdqe", "clc", "cld", "cmc", "cmova", "cmovae", "cmovb", "cmovbe", "cmove", "cmovg", "cmovge",
    "cmovl", "cmovle", "cmovne", "cmovno", "cmovnp", "cmovns", "cmovo", "cmovp", "cmovs", "cmp",
    "cmpxchg", "cqo", "cwd", "cwde", "dec", "div", "endbr32", "endbr64", "hlt", "idiv", "imul",
    "inc", "int", "int3", "ja", "jae", "jb", "jbe", "je", "jg", "jge", "jl", "jle", "jmp", "jne",
    "jno", "jnp", "jns", "jo", "jp", "js", "lea", "leave", "lfence", "mfence", "mov", "movabs",
    "movsx", "movsxd", "movzx", "mul", "neg", "nop", "not", "or", "pause", "pop", "popfq", "push",
    "pushfq", "rcl", "rcr", "ret", "rol", "ror", "sar", "sbb", "seta", "setae", "setb", "setbe",
    "sete", "setg", "setge", "setl", "setle", "setne", "setno", "setnp", "setns", "seto", "setp",
    "sets", "sfence", "shl", "shr", "stc", "std", "sub", "syscall", "test", "ud2", "xadd", "xchg",
    "xor",
];

/// Resolve a mnemonic to the static string an [`Insn`] can hold.
pub(crate) fn intern(s: &str) -> Option<&'static str> {
    MNEMONICS.binary_search(&s).ok().map(|n| MNEMONICS[n]).or({
        // `sal` is the assembler's other spelling of `shl`; the decoder never
        // prints it, so it is accepted rather than listed.
        match s {
            "sal" => Some("shl"),
            "repz" => Some("rep"),
            _ => None,
        }
    })
}

/// Bare words that are operands rather than registers. x86 has none the
/// encoder handles, but the parser asks, so the answer is written down.
pub(crate) fn name(_s: &str) -> Option<&'static str> {
    None
}

const GPR64: [&str; 16] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
    "r14", "r15",
];
const GPR32: [&str; 16] = [
    "eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi", "r8d", "r9d", "r10d", "r11d", "r12d",
    "r13d", "r14d", "r15d",
];
const GPR16: [&str; 16] = [
    "ax", "cx", "dx", "bx", "sp", "bp", "si", "di", "r8w", "r9w", "r10w", "r11w", "r12w", "r13w",
    "r14w", "r15w",
];
const GPR8: [&str; 16] = [
    "al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil", "r8b", "r9b", "r10b", "r11b", "r12b",
    "r13b", "r14b", "r15b",
];
const GPR8H: [&str; 4] = ["ah", "ch", "dh", "bh"];
const SEG: [&str; 6] = ["es", "cs", "ss", "ds", "fs", "gs"];

fn find(table: &[&str], s: &str) -> Option<u8> {
    table.iter().position(|n| *n == s).map(|n| n as u8)
}

/// Parse a register name, in any of the four general purpose widths plus the
/// high byte bank, the segments, the vector bank and the program counter.
pub(crate) fn register(s: &str) -> Option<Reg> {
    if let Some(n) = find(&GPR64, s) {
        return Some(Reg::gpr(n, Width::W64));
    }
    if let Some(n) = find(&GPR32, s) {
        return Some(Reg::gpr(n, Width::W32));
    }
    if let Some(n) = find(&GPR16, s) {
        return Some(Reg::gpr(n, Width::W16));
    }
    if let Some(n) = find(&GPR8, s) {
        return Some(Reg::gpr(n, Width::W8));
    }
    if let Some(n) = find(&GPR8H, s) {
        return Some(Reg {
            class: RegClass::GprHigh,
            num: n,
            width: Width::W8,
        });
    }
    if let Some(n) = find(&SEG, s) {
        return Some(Reg {
            class: RegClass::Seg,
            num: n,
            width: Width::W16,
        });
    }
    match s {
        "rip" => Some(Reg {
            class: RegClass::Pc,
            num: 0,
            width: Width::W64,
        }),
        "eip" => Some(Reg {
            class: RegClass::Pc,
            num: 0,
            width: Width::W32,
        }),
        // The phantom SIB index llvm prints when the index field is empty but
        // the scale still has to show.
        "riz" => Some(Reg {
            class: RegClass::Zr,
            num: 0,
            width: Width::W64,
        }),
        "eiz" => Some(Reg {
            class: RegClass::Zr,
            num: 0,
            width: Width::W32,
        }),
        _ => s
            .strip_prefix("xmm")
            .and_then(|n| n.parse::<u8>().ok())
            .filter(|n| *n < 16)
            .map(|n| Reg::vec(n, Width::W128)),
    }
}

/// A segment register, for the `fs:` style override the parser reads.
pub(crate) fn segment(s: &str) -> Option<Reg> {
    find(&SEG, s).map(|n| Reg {
        class: RegClass::Seg,
        num: n,
        width: Width::W16,
    })
}

/// The condition number a `jcc`, `setcc` or `cmovcc` suffix names.
fn cond(suffix: &str) -> Option<u8> {
    const CC: [&str; 16] = [
        "o", "no", "b", "ae", "e", "ne", "be", "a", "s", "ns", "p", "np", "l", "ge", "le", "g",
    ];
    // The synonyms objdump never prints but a person writes by habit.
    let canon = match suffix {
        "nae" | "c" => "b",
        "nb" | "nc" => "ae",
        "z" => "e",
        "nz" => "ne",
        "na" => "be",
        "nbe" => "a",
        "pe" => "p",
        "po" => "np",
        "nge" => "l",
        "nl" => "ge",
        "ng" => "le",
        "nle" => "g",
        other => other,
    };
    find(&CC, canon)
}

// ------------------------------------------------------------------ helpers

fn form(i: &Insn, detail: &'static str) -> AsmError {
    AsmError::UnsupportedForm {
        mnemonic: i.mnemonic.to_string(),
        detail,
    }
}

/// What a ModRM r/m field can name.
#[derive(Clone, Copy)]
enum Rm {
    Reg(Reg),
    Mem(Mem),
}

fn rm_of(i: &Insn, op: &Operand) -> Result<Rm, AsmError> {
    match op {
        Operand::Reg(r) => Ok(Rm::Reg(*r)),
        Operand::Mem(m) => Ok(Rm::Mem(*m)),
        _ => Err(form(i, "expected a register or a memory operand")),
    }
}

/// The number a register encodes as. The high byte bank is numbered from zero
/// in [`Reg`] because `ah` is not the low byte of `rax`, but the ModRM field it
/// lands in is the same four to seven the low bytes would use without REX.
fn rnum(r: Reg) -> u8 {
    match r.class {
        RegClass::GprHigh => r.num + 4,
        _ => r.num,
    }
}

fn imm_of(op: &Operand) -> Option<i64> {
    match op {
        Operand::Imm(v) | Operand::Count(v) => Some(*v),
        Operand::UImm(v) => Some(*v as i64),
        Operand::Addr(a) => Some(a.get() as i64),
        _ => None,
    }
}

fn addr_of(op: &Operand) -> Option<Addr> {
    match op {
        Operand::Addr(a) => Some(*a),
        Operand::Imm(v) | Operand::Count(v) => Some(Addr(*v as u64)),
        Operand::UImm(v) => Some(Addr(*v)),
        _ => None,
    }
}

/// True when `v` reaches the field either as a signed or as an unsigned
/// number. `mov al, 0xff` and `mov al, -0x1` are the same byte, and refusing
/// one of them would make half the disassembly in the world unassemblable.
fn imm_fits(v: i64, bytes: u8, extends: bool) -> bool {
    let bits = bytes as u32 * 8;
    if bits >= 64 {
        return true;
    }
    let low = -(1i64 << (bits - 1));
    // An immediate narrower than the operand is sign-extended by the
    // processor, so only the signed half of the field is reachable:
    // `mov eax, 0xffffffff` is the doubleword form and `mov rax, 0xffffffff`
    // cannot be, because that field would sign-extend to all ones.
    let high = if extends {
        (1i64 << (bits - 1)) - 1
    } else {
        (1i64 << bits) - 1
    };
    (low..=high).contains(&v)
}

fn check_imm(v: i64, bytes: u8, extends: bool) -> Result<(), AsmError> {
    if imm_fits(v, bytes, extends) {
        return Ok(());
    }
    let bits = bytes as u32 * 8;
    Err(AsmError::Range {
        what: "immediate",
        value: v,
        low: -(1i64 << (bits - 1)),
        high: if extends {
            (1i64 << (bits - 1)) - 1
        } else {
            (1i64 << bits) - 1
        },
    })
}

/// How many bytes the immediate field of a form at this operand size is, and
/// whether the processor sign-extends it.
fn imm_field(w: Width) -> (u8, bool) {
    match w {
        Width::W8 => (1, false),
        Width::W16 => (2, false),
        Width::W64 => (4, true),
        _ => (4, false),
    }
}

fn width_bytes(w: Width) -> u64 {
    w.bytes()
}

/// The operand size a form works at, taken from whichever operand states one.
///
/// A register settles it; failing that the `byte ptr` on a memory operand
/// does. When neither says, the instruction is genuinely ambiguous and the
/// refusal names the keyword the user has to add.
fn operand_width(i: &Insn, ops: &[&Operand]) -> Result<Width, AsmError> {
    for op in ops {
        if let Operand::Reg(r) = op
            && matches!(r.class, RegClass::Gpr | RegClass::GprHigh)
        {
            return Ok(r.width);
        }
    }
    for op in ops {
        if let Operand::Mem(m) = op {
            return match m.size {
                1 => Ok(Width::W8),
                2 => Ok(Width::W16),
                4 => Ok(Width::W32),
                8 => Ok(Width::W64),
                _ => Err(AsmError::UnsizedOperand {
                    mnemonic: i.mnemonic.to_string(),
                }),
            };
        }
    }
    Err(AsmError::UnsizedOperand {
        mnemonic: i.mnemonic.to_string(),
    })
}

// ------------------------------------------------------------------ emitter

/// The pieces of one encoding, gathered before any byte is written.
///
/// Built in this shape because the prefix bytes depend on decisions the
/// operand walk makes after the opcode is already chosen: whether a register
/// number reaches past seven, whether an address register is 32 bits, whether
/// a byte register needs REX to exist at all.
#[derive(Default)]
struct Emit {
    lock: bool,
    rep: Option<u8>,
    seg: Option<u8>,
    o16: bool,
    a32: bool,
    w: bool,
    r: bool,
    x: bool,
    b: bool,
    /// A byte register that only exists with REX present: `spl` and friends.
    force_rex: bool,
    /// A byte register that cannot coexist with REX: `ah` and friends.
    deny_rex: bool,
    opcode: [u8; 3],
    opcode_len: u8,
    modrm: Option<u8>,
    sib: Option<u8>,
    disp: Option<(i64, u8)>,
    imm: Option<(i64, u8)>,
}

impl Emit {
    fn op(&mut self, bytes: &[u8]) {
        self.opcode_len = bytes.len() as u8;
        self.opcode[..bytes.len()].copy_from_slice(bytes);
    }

    /// Set the operand size, which is where REX.W and the `0x66` prefix come
    /// from. Byte and 32-bit operands need neither.
    fn width(&mut self, w: Width) {
        self.o16 = w == Width::W16;
        self.w = w == Width::W64;
    }

    /// Record a register used as a plain operand, for the REX rules that are
    /// about the register bank rather than about a ModRM field.
    fn note(&mut self, r: Reg) {
        if r.class == RegClass::GprHigh {
            self.deny_rex = true;
        }
        if r.class == RegClass::Gpr && r.width == Width::W8 && (4..8).contains(&r.num) {
            self.force_rex = true;
        }
    }

    fn finish(&self, i: &Insn) -> Result<Encoded, AsmError> {
        let rex_bits = (u8::from(self.w) << 3)
            | (u8::from(self.r) << 2)
            | (u8::from(self.x) << 1)
            | u8::from(self.b);
        let rex = rex_bits != 0 || self.force_rex;
        if rex && self.deny_rex {
            return Err(form(
                i,
                "ah, ch, dh and bh cannot appear alongside a register or size that needs REX",
            ));
        }
        let mut out: Vec<u8> = Vec::with_capacity(crate::MAX_INSN);
        if self.lock {
            out.push(0xf0);
        }
        if let Some(p) = self.rep {
            out.push(p);
        }
        if let Some(s) = self.seg {
            out.push(s);
        }
        if self.o16 {
            out.push(0x66);
        }
        if self.a32 {
            out.push(0x67);
        }
        if rex {
            out.push(0x40 | rex_bits);
        }
        out.extend_from_slice(&self.opcode[..self.opcode_len as usize]);
        if let Some(m) = self.modrm {
            out.push(m);
        }
        if let Some(s) = self.sib {
            out.push(s);
        }
        if let Some((v, n)) = self.disp {
            out.extend_from_slice(&v.to_le_bytes()[..n as usize]);
        }
        if let Some((v, n)) = self.imm {
            out.extend_from_slice(&v.to_le_bytes()[..n as usize]);
        }
        Encoded::from_slice(&out)
    }

    /// Fill in ModRM, SIB, the displacement and the REX extension bits for a
    /// `reg, r/m` pair.
    fn modrm_pair(&mut self, i: &Insn, reg_field: u8, rm: Rm) -> Result<(), AsmError> {
        self.r = reg_field >= 8;
        match rm {
            Rm::Reg(r) => {
                self.note(r);
                let n = match r.class {
                    RegClass::Gpr | RegClass::Vec | RegClass::GprHigh => rnum(r),
                    _ => return Err(form(i, "this operand must be a general purpose register")),
                };
                self.b = n >= 8;
                self.modrm = Some(0xc0 | ((reg_field & 7) << 3) | (n & 7));
                Ok(())
            }
            Rm::Mem(m) => self.modrm_mem(i, reg_field, &m),
        }
    }

    fn modrm_mem(&mut self, i: &Insn, reg_field: u8, m: &Mem) -> Result<(), AsmError> {
        // Set here as well as in `modrm_pair`, because the forms that know
        // their operand is memory call straight into this one.
        self.r = reg_field >= 8;
        if m.mode != AddrMode::Offset {
            return Err(form(i, "x86 has no pre- or post-indexed addressing"));
        }
        if let Some(s) = m.seg {
            if s.class != RegClass::Seg || s.num > 5 {
                return Err(form(i, "expected a segment register"));
            }
            self.seg = Some([0x26u8, 0x2e, 0x36, 0x3e, 0x64, 0x65][s.num as usize]);
        }
        let reg3 = (reg_field & 7) << 3;

        // A rip-relative operand carries the displacement the bytes hold, not
        // a resolved address: the decoder leaves it that way so the text and
        // the encoding cannot disagree, and this is the other half of that.
        if let Some(base) = m.base
            && base.class == RegClass::Pc
        {
            if m.index.is_some() {
                return Err(form(i, "a rip-relative address takes no index"));
            }
            self.a32 = base.width == Width::W32;
            check_imm(m.disp, 4, true)?;
            self.modrm = Some(reg3 | 0b101);
            self.disp = Some((m.disp, 4));
            return Ok(());
        }

        // Every address register has to agree on its width, since one `0x67`
        // covers the whole operand.
        let mut a32 = false;
        for r in [m.base, m.index.map(|x| x.0)].into_iter().flatten() {
            match r.width {
                Width::W32 => a32 = true,
                Width::W64 => {}
                _ => return Err(form(i, "an address register is 32 or 64 bits")),
            }
        }
        self.a32 = a32;

        let base = match m.base {
            Some(b) if matches!(b.class, RegClass::Gpr) => Some(b.num),
            Some(_) => return Err(form(i, "a base register is general purpose")),
            None => None,
        };
        let index = match m.index {
            Some((r, ext, shift)) => {
                if !matches!(
                    ext,
                    r12e_arch::insn::Extend::Lsl | r12e_arch::insn::Extend::LslZero
                ) {
                    return Err(form(i, "an x86 index is scaled, never extended"));
                }
                if shift > 3 {
                    return Err(AsmError::Range {
                        what: "index scale",
                        value: 1i64 << shift,
                        low: 1,
                        high: 8,
                    });
                }
                match r.class {
                    // `riz` is no index at all, kept so the scale stays visible.
                    RegClass::Zr => Some((4u8, shift)),
                    RegClass::Gpr => {
                        if r.num == 4 {
                            return Err(form(i, "rsp cannot be an index register"));
                        }
                        Some((r.num, shift))
                    }
                    _ => return Err(form(i, "an index register is general purpose")),
                }
            }
            None => None,
        };
        if let Some((n, _)) = index {
            self.x = n >= 8;
        }

        let Some(base) = base else {
            // No base: the only 64-bit form is a SIB with base 101 and a full
            // displacement, which is how an absolute address encodes.
            check_imm(m.disp, 4, true)?;
            let (ix, scale) = index.unwrap_or((4, 0));
            self.modrm = Some(reg3 | 0b100);
            self.sib = Some((scale << 6) | ((ix & 7) << 3) | 0b101);
            self.disp = Some((m.disp, 4));
            return Ok(());
        };
        self.b = base >= 8;

        // rbp and r13 have no mod-zero form, so a zero displacement there is
        // still written out as a byte.
        let md = if m.disp == 0 && base & 7 != 5 {
            0u8
        } else if (-0x80..=0x7f).contains(&m.disp) {
            1
        } else {
            check_imm(m.disp, 4, true)?;
            2
        };
        let need_sib = index.is_some() || base & 7 == 4;
        if need_sib {
            let (ix, scale) = index.unwrap_or((4, 0));
            self.modrm = Some((md << 6) | reg3 | 0b100);
            self.sib = Some((scale << 6) | ((ix & 7) << 3) | (base & 7));
        } else {
            self.modrm = Some((md << 6) | reg3 | (base & 7));
        }
        self.disp = match md {
            1 => Some((m.disp, 1)),
            2 => Some((m.disp, 4)),
            _ => None,
        };
        Ok(())
    }
}

// ----------------------------------------------------------------- dispatch

/// The eight arithmetic and logic operations, in opcode order.
fn arith_index(m: &str) -> Option<u8> {
    Some(match m {
        "add" => 0,
        "or" => 1,
        "adc" => 2,
        "sbb" => 3,
        "and" => 4,
        "sub" => 5,
        "xor" => 6,
        "cmp" => 7,
        _ => return None,
    })
}

/// The eight shifts and rotates, in ModRM reg order.
fn shift_index(m: &str) -> Option<u8> {
    Some(match m {
        "rol" => 0,
        "ror" => 1,
        "rcl" => 2,
        "rcr" => 3,
        "shl" => 4,
        "shr" => 5,
        "sar" => 7,
        _ => return None,
    })
}

/// Encode one instruction.
pub fn encode(i: &Insn) -> Result<Encoded, AsmError> {
    let mut e = Emit::default();
    match i.prefix {
        None => {}
        Some("lock") => e.lock = true,
        Some("rep") => e.rep = Some(0xf3),
        Some("repne") => e.rep = Some(0xf2),
        Some(_) => return Err(form(i, "unknown prefix")),
    }
    let m = i.mnemonic;
    if let Some(n) = arith_index(m) {
        return arith(i, e, n);
    }
    if shift_index(m).is_some() {
        return shift(i, e);
    }
    if let Some(c) = m.strip_prefix("set").and_then(cond) {
        return setcc(i, e, c);
    }
    if let Some(c) = m.strip_prefix("cmov").and_then(cond) {
        return two_byte_rm_reg(i, e, 0x40 + c);
    }
    if m.len() >= 2
        && m.starts_with('j')
        && m != "jmp"
        && let Some(c) = cond(&m[1..])
    {
        return jcc(i, e, c);
    }
    match m {
        "mov" | "movabs" => mov(i, e),
        "lea" => lea(i, e),
        "push" => push(i, e),
        "pop" => pop(i, e),
        "test" => test(i, e),
        "xchg" => xchg(i, e),
        "jmp" | "call" => jmp_call(i, e),
        "ret" => ret(i, e),
        "nop" => nop(i, e),
        "movzx" | "movsx" => movx(i, e),
        "movsxd" => movsxd(i, e),
        "imul" => imul(i, e),
        "inc" | "dec" => inc_dec(i, e),
        "not" | "neg" | "mul" | "div" | "idiv" => unary(i, e),
        "bt" | "bts" | "btr" | "btc" => bit_test(i, e),
        "bsf" | "bsr" => two_byte_rm_reg(i, e, if m == "bsf" { 0xbc } else { 0xbd }),
        "bswap" => bswap(i, e),
        "cmpxchg" => cmpxchg(i, e),
        "xadd" => xadd(i, e),
        "int" => int_n(i, e),
        _ => no_operand(i, e),
    }
}

/// The forms that are a fixed byte string and nothing else.
fn no_operand(i: &Insn, e: Emit) -> Result<Encoded, AsmError> {
    if !i.operands().is_empty() {
        return Err(form(i, "this mnemonic takes no operands"));
    }
    let bytes: &[u8] = match i.mnemonic {
        "int3" => &[0xcc],
        "leave" => &[0xc9],
        "hlt" => &[0xf4],
        "syscall" => &[0x0f, 0x05],
        "ud2" => &[0x0f, 0x0b],
        "endbr64" => &[0xf3, 0x0f, 0x1e, 0xfa],
        "endbr32" => &[0xf3, 0x0f, 0x1e, 0xfb],
        "pause" => &[0xf3, 0x90],
        "clc" => &[0xf8],
        "stc" => &[0xf9],
        "cmc" => &[0xf5],
        "cld" => &[0xfc],
        "std" => &[0xfd],
        "lfence" => &[0x0f, 0xae, 0xe8],
        "mfence" => &[0x0f, 0xae, 0xf0],
        "sfence" => &[0x0f, 0xae, 0xf8],
        "pushfq" => &[0x9c],
        "popfq" => &[0x9d],
        "cbw" => &[0x66, 0x98],
        "cwde" => &[0x98],
        "cdqe" => &[0x48, 0x98],
        "cwd" => &[0x66, 0x99],
        "cdq" => &[0x99],
        "cqo" => &[0x48, 0x99],
        _ => return Err(form(i, "no encoder for this mnemonic")),
    };
    // These are written out whole, prefixes included, so the builder's own
    // prefix slots have nowhere to go.
    if e.lock || e.rep.is_some() {
        return Err(form(i, "this mnemonic takes no prefix"));
    }
    Encoded::from_slice(bytes)
}

fn two(i: &Insn) -> Result<(&Operand, &Operand), AsmError> {
    let ops = i.operands();
    match (ops.first(), ops.get(1)) {
        (Some(a), Some(b)) if ops.len() == 2 => Ok((a, b)),
        _ => Err(form(i, "needs exactly two operands")),
    }
}

fn arith(i: &Insn, mut e: Emit, n: u8) -> Result<Encoded, AsmError> {
    let (dst, src) = two(i)?;
    let w = operand_width(i, &[dst, src])?;
    e.width(w);
    let byte = w == Width::W8;
    let base = n * 8;
    match (dst, src) {
        // Register to register takes the `r/m, reg` direction, which is what
        // every assembler picks and therefore what most corpora hold.
        (Operand::Reg(d), Operand::Reg(s)) => {
            e.note(*s);
            e.op(&[base + u8::from(!byte)]);
            e.modrm_pair(i, rnum(*s), Rm::Reg(*d))?;
        }
        (Operand::Mem(m), Operand::Reg(s)) => {
            e.note(*s);
            e.op(&[base + u8::from(!byte)]);
            e.modrm_mem(i, rnum(*s), m)?;
        }
        (Operand::Reg(d), Operand::Mem(m)) => {
            e.note(*d);
            e.op(&[base + 2 + u8::from(!byte)]);
            e.modrm_mem(i, rnum(*d), m)?;
        }
        (rm, imm) => {
            let v = imm_of(imm).ok_or(form(i, "expected a register, memory or an immediate"))?;
            let rm = rm_of(i, rm)?;
            arith_imm(i, &mut e, n, w, rm, v)?;
        }
    }
    e.finish(i)
}

fn arith_imm(i: &Insn, e: &mut Emit, n: u8, w: Width, rm: Rm, v: i64) -> Result<(), AsmError> {
    if w == Width::W8 {
        check_imm(v, 1, false)?;
        if let Rm::Reg(r) = rm
            && r.class == RegClass::Gpr
            && r.num == 0
        {
            e.op(&[n * 8 + 4]);
            e.imm = Some((v, 1));
            return Ok(());
        }
        e.op(&[0x80]);
        e.modrm_pair(i, n, rm)?;
        e.imm = Some((v, 1));
        return Ok(());
    }
    // Shortest first: the sign-extended byte, then the accumulator form, then
    // the general one.
    if (-0x80..=0x7f).contains(&v) {
        e.op(&[0x83]);
        e.modrm_pair(i, n, rm)?;
        e.imm = Some((v, 1));
        return Ok(());
    }
    let (zbytes, extends) = imm_field(w);
    check_imm(v, zbytes, extends)?;
    if let Rm::Reg(r) = rm
        && r.class == RegClass::Gpr
        && r.num == 0
    {
        e.op(&[n * 8 + 5]);
        e.imm = Some((v, zbytes));
        return Ok(());
    }
    e.op(&[0x81]);
    e.modrm_pair(i, n, rm)?;
    e.imm = Some((v, zbytes));
    Ok(())
}

fn mov(i: &Insn, mut e: Emit) -> Result<Encoded, AsmError> {
    let (dst, src) = two(i)?;
    let w = operand_width(i, &[dst, src])?;
    e.width(w);
    let byte = w == Width::W8;
    match (dst, src) {
        (Operand::Reg(d), Operand::Reg(s))
            if matches!(d.class, RegClass::Seg) || matches!(s.class, RegClass::Seg) =>
        {
            segment_move(i, e, *d, *s)
        }
        (Operand::Reg(d), Operand::Reg(s)) => {
            e.note(*s);
            e.op(&[0x88 + u8::from(!byte)]);
            e.modrm_pair(i, rnum(*s), Rm::Reg(*d))?;
            e.finish(i)
        }
        (Operand::Mem(m), Operand::Reg(s)) => {
            e.note(*s);
            if s.class == RegClass::Seg {
                e.width(Width::W16);
                e.o16 = false;
                e.op(&[0x8c]);
                e.modrm_mem(i, s.num, m)?;
                return e.finish(i);
            }
            e.op(&[0x88 + u8::from(!byte)]);
            e.modrm_mem(i, rnum(*s), m)?;
            e.finish(i)
        }
        (Operand::Reg(d), Operand::Mem(m)) => {
            e.note(*d);
            if d.class == RegClass::Seg {
                e.width(Width::W16);
                e.o16 = false;
                e.op(&[0x8e]);
                e.modrm_mem(i, d.num, m)?;
                return e.finish(i);
            }
            e.op(&[0x8a + u8::from(!byte)]);
            e.modrm_mem(i, rnum(*d), m)?;
            e.finish(i)
        }
        (Operand::Reg(d), imm) => {
            let v = imm_of(imm).ok_or(form(i, "expected a register, memory or an immediate"))?;
            e.note(*d);
            if d.class != RegClass::Gpr && d.class != RegClass::GprHigh {
                return Err(form(i, "expected a general purpose register"));
            }
            let full = width_bytes(w) as u8;
            // The ten-byte form is the only one that carries a full 64-bit
            // immediate, and it is the only thing `movabs` ever means.
            let wide = i.mnemonic == "movabs" || (w == Width::W64 && !imm_fits(v, 4, true));
            if wide || w != Width::W64 {
                if !wide {
                    check_imm(v, full, false)?;
                }
                let n = rnum(*d);
                e.b = n >= 8;
                e.op(&[(if byte { 0xb0 } else { 0xb8 }) + (n & 7)]);
                e.imm = Some((v, full));
                return e.finish(i);
            }
            check_imm(v, 4, true)?;
            e.op(&[0xc7]);
            e.modrm_pair(i, 0, Rm::Reg(*d))?;
            e.imm = Some((v, 4));
            e.finish(i)
        }
        (Operand::Mem(m), imm) => {
            let v = imm_of(imm).ok_or(form(i, "expected a register or an immediate"))?;
            let (bytes, extends) = imm_field(w);
            check_imm(v, bytes, extends)?;
            e.op(&[0xc6 + u8::from(!byte)]);
            e.modrm_mem(i, 0, m)?;
            e.imm = Some((v, bytes));
            e.finish(i)
        }
        _ => Err(form(i, "expected a register or a memory destination")),
    }
}

fn segment_move(i: &Insn, mut e: Emit, d: Reg, s: Reg) -> Result<Encoded, AsmError> {
    // The segment moves are sixteen bits wide in the register file but take
    // no operand-size prefix, because the other operand's width selects the
    // form rather than a prefix.
    e.o16 = false;
    e.w = false;
    if d.class == RegClass::Seg {
        if s.class != RegClass::Gpr {
            return Err(form(i, "expected a general purpose source"));
        }
        e.op(&[0x8e]);
        e.modrm_pair(i, d.num, Rm::Reg(s))?;
    } else {
        if d.class != RegClass::Gpr {
            return Err(form(i, "expected a general purpose destination"));
        }
        e.w = d.width == Width::W64;
        e.op(&[0x8c]);
        e.modrm_pair(i, s.num, Rm::Reg(d))?;
    }
    e.finish(i)
}

fn lea(i: &Insn, mut e: Emit) -> Result<Encoded, AsmError> {
    let (dst, src) = two(i)?;
    let (Operand::Reg(d), Operand::Mem(m)) = (dst, src) else {
        return Err(form(i, "lea takes a register and a memory operand"));
    };
    e.width(d.width);
    e.note(*d);
    e.op(&[0x8d]);
    e.modrm_mem(i, rnum(*d), m)?;
    e.finish(i)
}

/// Push, pop, and the indirect branches default to 64-bit operands in long
/// mode, so a 64-bit form needs no REX.W and a 32-bit one cannot be written.
fn stack_width(i: &Insn, w: Width, e: &mut Emit) -> Result<(), AsmError> {
    match w {
        Width::W64 => Ok(()),
        Width::W16 => {
            e.o16 = true;
            Ok(())
        }
        _ => Err(form(i, "long mode pushes and pops 64 or 16 bits, never 32")),
    }
}

fn push(i: &Insn, mut e: Emit) -> Result<Encoded, AsmError> {
    let ops = i.operands();
    let [op] = ops else {
        return Err(form(i, "needs one operand"));
    };
    match op {
        Operand::Reg(r) => {
            stack_width(i, r.width, &mut e)?;
            if r.class != RegClass::Gpr {
                return Err(form(i, "expected a general purpose register"));
            }
            e.b = r.num >= 8;
            e.op(&[0x50 + (r.num & 7)]);
        }
        Operand::Mem(m) => {
            stack_width(i, if m.size == 2 { Width::W16 } else { Width::W64 }, &mut e)?;
            e.op(&[0xff]);
            e.modrm_mem(i, 6, m)?;
        }
        other => {
            let v = imm_of(other).ok_or(form(i, "expected a register, memory or an immediate"))?;
            if (-0x80..=0x7f).contains(&v) {
                e.op(&[0x6a]);
                e.imm = Some((v, 1));
            } else {
                check_imm(v, 4, true)?;
                e.op(&[0x68]);
                e.imm = Some((v, 4));
            }
        }
    }
    e.finish(i)
}

fn pop(i: &Insn, mut e: Emit) -> Result<Encoded, AsmError> {
    let ops = i.operands();
    let [op] = ops else {
        return Err(form(i, "needs one operand"));
    };
    match op {
        Operand::Reg(r) => {
            stack_width(i, r.width, &mut e)?;
            if r.class != RegClass::Gpr {
                return Err(form(i, "expected a general purpose register"));
            }
            e.b = r.num >= 8;
            e.op(&[0x58 + (r.num & 7)]);
        }
        Operand::Mem(m) => {
            stack_width(i, if m.size == 2 { Width::W16 } else { Width::W64 }, &mut e)?;
            e.op(&[0x8f]);
            e.modrm_mem(i, 0, m)?;
        }
        _ => return Err(form(i, "pop takes a register or a memory operand")),
    }
    e.finish(i)
}

fn test(i: &Insn, mut e: Emit) -> Result<Encoded, AsmError> {
    let (dst, src) = two(i)?;
    let w = operand_width(i, &[dst, src])?;
    e.width(w);
    let byte = w == Width::W8;
    match (dst, src) {
        (rm, Operand::Reg(s)) => {
            e.note(*s);
            e.op(&[0x84 + u8::from(!byte)]);
            e.modrm_pair(i, rnum(*s), rm_of(i, rm)?)?;
        }
        (rm, imm) => {
            let v = imm_of(imm).ok_or(form(i, "expected a register or an immediate"))?;
            let (bytes, extends) = imm_field(w);
            check_imm(v, bytes, extends)?;
            // The accumulator form is a byte shorter and carries no ModRM.
            if let Rm::Reg(r) = rm_of(i, rm)?
                && r.class == RegClass::Gpr
                && r.num == 0
            {
                e.note(r);
                e.op(&[0xa8 + u8::from(!byte)]);
                e.imm = Some((v, bytes));
                return e.finish(i);
            }
            e.op(&[0xf6 + u8::from(!byte)]);
            e.modrm_pair(i, 0, rm_of(i, rm)?)?;
            e.imm = Some((v, bytes));
        }
    }
    e.finish(i)
}

fn xchg(i: &Insn, mut e: Emit) -> Result<Encoded, AsmError> {
    let (a, b) = two(i)?;
    let w = operand_width(i, &[a, b])?;
    e.width(w);
    let byte = w == Width::W8;
    if let (Operand::Reg(x), Operand::Reg(y)) = (a, b) {
        // The one-byte accumulator form, except where it would encode 0x90,
        // which is `nop` and decodes as `nop`.
        let short = |acc: &Reg, other: &Reg| {
            !byte
                && acc.class == RegClass::Gpr
                && acc.num == 0
                && other.class == RegClass::Gpr
                && !(other.num == 0 && w == Width::W32)
        };
        if short(x, y) {
            e.b = y.num >= 8;
            e.op(&[0x90 + (y.num & 7)]);
            return e.finish(i);
        }
        if short(y, x) {
            e.b = x.num >= 8;
            e.op(&[0x90 + (x.num & 7)]);
            return e.finish(i);
        }
    }
    // The decoder prints the ModRM reg operand first for a register pair and
    // the memory operand first otherwise, so the two orders are read here the
    // way they were printed.
    let (reg, rm) = match (a, b) {
        (Operand::Reg(r), other) if !matches!(other, Operand::Reg(_)) => (*r, rm_of(i, other)?),
        (other, Operand::Reg(r)) => (*r, rm_of(i, other)?),
        _ => return Err(form(i, "xchg needs at least one register operand")),
    };
    e.note(reg);
    e.op(&[0x86 + u8::from(!byte)]);
    e.modrm_pair(i, rnum(reg), rm)?;
    e.finish(i)
}

fn shift(i: &Insn, mut e: Emit) -> Result<Encoded, AsmError> {
    let n = shift_index(i.mnemonic).ok_or(form(i, "not a shift"))?;
    let ops = i.operands();
    let dst = ops.first().ok_or(form(i, "needs a destination"))?;
    let w = operand_width(i, &[dst])?;
    e.width(w);
    let byte = w == Width::W8;
    match ops.get(1) {
        // The opcode itself is the count of one, which is how the decoder
        // prints it: with no second operand at all.
        None => {
            e.op(&[0xd0 + u8::from(!byte)]);
            e.modrm_pair(i, n, rm_of(i, dst)?)?;
        }
        Some(Operand::Reg(r)) if r.class == RegClass::Gpr && r.num == 1 && r.width == Width::W8 => {
            e.op(&[0xd2 + u8::from(!byte)]);
            e.modrm_pair(i, n, rm_of(i, dst)?)?;
        }
        Some(op) => {
            let v = imm_of(op).ok_or(form(i, "a shift count is cl or an immediate"))?;
            if !(0..=0xff).contains(&v) {
                return Err(AsmError::Range {
                    what: "shift count",
                    value: v,
                    low: 0,
                    high: 0xff,
                });
            }
            e.op(&[0xc0 + u8::from(!byte)]);
            e.modrm_pair(i, n, rm_of(i, dst)?)?;
            e.imm = Some((v, 1));
        }
    }
    if ops.len() > 2 {
        return Err(form(i, "a shift takes at most two operands"));
    }
    e.finish(i)
}

fn setcc(i: &Insn, mut e: Emit, c: u8) -> Result<Encoded, AsmError> {
    let ops = i.operands();
    let [dst] = ops else {
        return Err(form(i, "needs one operand"));
    };
    let w = operand_width(i, &[dst])?;
    if w != Width::W8 {
        return Err(form(i, "setcc writes one byte"));
    }
    e.op(&[0x0f, 0x90 + c]);
    e.modrm_pair(i, 0, rm_of(i, dst)?)?;
    e.finish(i)
}

/// The `reg, r/m` two-byte forms: `cmovcc`, `bsf`, `bsr`.
fn two_byte_rm_reg(i: &Insn, mut e: Emit, op2: u8) -> Result<Encoded, AsmError> {
    let (dst, src) = two(i)?;
    let Operand::Reg(d) = dst else {
        return Err(form(i, "the destination is a register"));
    };
    let w = operand_width(i, &[dst, src])?;
    if w == Width::W8 {
        return Err(form(i, "this form has no byte width"));
    }
    e.width(w);
    e.note(*d);
    e.op(&[0x0f, op2]);
    e.modrm_pair(i, rnum(*d), rm_of(i, src)?)?;
    e.finish(i)
}

fn movx(i: &Insn, mut e: Emit) -> Result<Encoded, AsmError> {
    let (dst, src) = two(i)?;
    let Operand::Reg(d) = dst else {
        return Err(form(i, "the destination is a register"));
    };
    let src_bytes = match src {
        Operand::Reg(r) => width_bytes(r.width),
        Operand::Mem(m) => m.size,
        _ => return Err(form(i, "expected a register or a memory source")),
    };
    let op2 = match (i.mnemonic, src_bytes) {
        ("movzx", 1) => 0xb6u8,
        ("movzx", 2) => 0xb7,
        ("movsx", 1) => 0xbe,
        ("movsx", 2) => 0xbf,
        (_, 4) => return Err(form(i, "a 32-bit source widens with movsxd, not movsx")),
        _ => {
            return Err(AsmError::UnsizedOperand {
                mnemonic: i.mnemonic.to_string(),
            });
        }
    };
    if let Operand::Reg(s) = src {
        e.note(*s);
    }
    e.width(d.width);
    e.note(*d);
    e.op(&[0x0f, op2]);
    e.modrm_pair(i, rnum(*d), rm_of(i, src)?)?;
    e.finish(i)
}

fn movsxd(i: &Insn, mut e: Emit) -> Result<Encoded, AsmError> {
    let (dst, src) = two(i)?;
    let Operand::Reg(d) = dst else {
        return Err(form(i, "the destination is a register"));
    };
    if d.width != Width::W64 {
        return Err(form(i, "movsxd writes a 64-bit register"));
    }
    e.width(Width::W64);
    e.op(&[0x63]);
    e.modrm_pair(i, rnum(*d), rm_of(i, src)?)?;
    e.finish(i)
}

fn imul(i: &Insn, mut e: Emit) -> Result<Encoded, AsmError> {
    let ops = i.operands();
    match ops.len() {
        1 => unary(i, e),
        2 => two_byte_rm_reg(i, e, 0xaf),
        3 => {
            let Operand::Reg(d) = ops[0] else {
                return Err(form(i, "the destination is a register"));
            };
            let w = operand_width(i, &[&ops[0], &ops[1]])?;
            if w == Width::W8 {
                return Err(form(i, "the three-operand multiply has no byte width"));
            }
            e.width(w);
            let v = imm_of(&ops[2]).ok_or(form(i, "expected an immediate"))?;
            let bytes = if (-0x80..=0x7f).contains(&v) {
                e.op(&[0x6b]);
                1u8
            } else {
                let (n, extends) = imm_field(w);
                check_imm(v, n, extends)?;
                e.op(&[0x69]);
                n
            };
            e.modrm_pair(i, rnum(d), rm_of(i, &ops[1])?)?;
            e.imm = Some((v, bytes));
            e.finish(i)
        }
        _ => Err(form(i, "imul takes one, two or three operands")),
    }
}

fn unary(i: &Insn, mut e: Emit) -> Result<Encoded, AsmError> {
    let n = match i.mnemonic {
        "not" => 2u8,
        "neg" => 3,
        "mul" => 4,
        "imul" => 5,
        "div" => 6,
        _ => 7,
    };
    let ops = i.operands();
    let [dst] = ops else {
        return Err(form(i, "needs one operand"));
    };
    let w = operand_width(i, &[dst])?;
    e.width(w);
    e.op(&[0xf6 + u8::from(w != Width::W8)]);
    e.modrm_pair(i, n, rm_of(i, dst)?)?;
    e.finish(i)
}

fn inc_dec(i: &Insn, mut e: Emit) -> Result<Encoded, AsmError> {
    let ops = i.operands();
    let [dst] = ops else {
        return Err(form(i, "needs one operand"));
    };
    let w = operand_width(i, &[dst])?;
    e.width(w);
    e.op(&[0xfe + u8::from(w != Width::W8)]);
    e.modrm_pair(i, u8::from(i.mnemonic == "dec"), rm_of(i, dst)?)?;
    e.finish(i)
}

fn bit_test(i: &Insn, mut e: Emit) -> Result<Encoded, AsmError> {
    let (dst, src) = two(i)?;
    let n = match i.mnemonic {
        "bt" => 4u8,
        "bts" => 5,
        "btr" => 6,
        _ => 7,
    };
    let w = operand_width(i, &[dst, src])?;
    if w == Width::W8 {
        return Err(form(i, "a bit test has no byte width"));
    }
    e.width(w);
    if let Operand::Reg(s) = src
        && matches!(s.class, RegClass::Gpr)
    {
        e.op(&[0x0f, 0x83 + n * 8]);
        e.modrm_pair(i, rnum(*s), rm_of(i, dst)?)?;
        return e.finish(i);
    }
    let v = imm_of(src).ok_or(form(i, "expected a register or an immediate"))?;
    if !(0..=0xff).contains(&v) {
        return Err(AsmError::Range {
            what: "bit number",
            value: v,
            low: 0,
            high: 0xff,
        });
    }
    e.op(&[0x0f, 0xba]);
    e.modrm_pair(i, n, rm_of(i, dst)?)?;
    e.imm = Some((v, 1));
    e.finish(i)
}

fn bswap(i: &Insn, mut e: Emit) -> Result<Encoded, AsmError> {
    let ops = i.operands();
    let [Operand::Reg(r)] = ops else {
        return Err(form(i, "bswap takes one register"));
    };
    if !matches!(r.width, Width::W32 | Width::W64) {
        return Err(form(i, "bswap is 32 or 64 bits"));
    }
    e.width(r.width);
    e.b = r.num >= 8;
    e.op(&[0x0f, 0xc8 + (r.num & 7)]);
    e.finish(i)
}

fn cmpxchg(i: &Insn, mut e: Emit) -> Result<Encoded, AsmError> {
    let (dst, src) = two(i)?;
    let Operand::Reg(s) = src else {
        return Err(form(i, "the source is a register"));
    };
    let w = operand_width(i, &[dst, src])?;
    e.width(w);
    e.note(*s);
    e.op(&[0x0f, 0xb0 + u8::from(w != Width::W8)]);
    e.modrm_pair(i, rnum(*s), rm_of(i, dst)?)?;
    e.finish(i)
}

fn xadd(i: &Insn, mut e: Emit) -> Result<Encoded, AsmError> {
    let (dst, src) = two(i)?;
    let Operand::Reg(s) = src else {
        return Err(form(i, "the source is a register"));
    };
    let w = operand_width(i, &[dst, src])?;
    e.width(w);
    e.note(*s);
    e.op(&[0x0f, 0xc0 + u8::from(w != Width::W8)]);
    e.modrm_pair(i, rnum(*s), rm_of(i, dst)?)?;
    e.finish(i)
}

fn int_n(i: &Insn, mut e: Emit) -> Result<Encoded, AsmError> {
    let ops = i.operands();
    let [op] = ops else {
        return Err(form(i, "needs one operand"));
    };
    let v = imm_of(op).ok_or(form(i, "expected an interrupt number"))?;
    if !(0..=0xff).contains(&v) {
        return Err(AsmError::Range {
            what: "interrupt number",
            value: v,
            low: 0,
            high: 0xff,
        });
    }
    // `int 3` stays two bytes and `int3` stays one: they raise the same
    // exception but they are not the same instruction to a debugger, so
    // neither is silently rewritten as the other.
    e.op(&[0xcd]);
    e.imm = Some((v, 1));
    e.finish(i)
}

fn ret(i: &Insn, mut e: Emit) -> Result<Encoded, AsmError> {
    match i.operands() {
        [] => {
            e.op(&[0xc3]);
        }
        [op] => {
            let v = imm_of(op).ok_or(form(i, "expected an immediate"))?;
            if !(0..=0xffff).contains(&v) {
                return Err(AsmError::Range {
                    what: "return pop count",
                    value: v,
                    low: 0,
                    high: 0xffff,
                });
            }
            e.op(&[0xc2]);
            e.imm = Some((v, 2));
        }
        _ => return Err(form(i, "ret takes at most one operand")),
    }
    e.finish(i)
}

fn nop(i: &Insn, mut e: Emit) -> Result<Encoded, AsmError> {
    match i.operands() {
        [] => {
            e.op(&[0x90]);
            e.finish(i)
        }
        [dst] => {
            let w = operand_width(i, &[dst])?;
            if w == Width::W8 {
                return Err(form(i, "the multi-byte nop is 16, 32 or 64 bits"));
            }
            e.width(w);
            e.op(&[0x0f, 0x1f]);
            e.modrm_pair(i, 0, rm_of(i, dst)?)?;
            e.finish(i)
        }
        _ => Err(form(i, "nop takes at most one operand")),
    }
}

// ---------------------------------------------------------------- branching

/// A displacement from the end of an instruction of `len` bytes.
fn rel(i: &Insn, to: Addr, len: i64) -> i64 {
    (to.get().wrapping_sub(i.addr.get()) as i64).wrapping_sub(len)
}

fn branch_range(i: &Insn, to: Addr, low: i64, high: i64) -> AsmError {
    AsmError::BranchRange {
        mnemonic: i.mnemonic.to_string(),
        from: i.addr.get(),
        to: to.get(),
        low,
        high,
    }
}

fn jcc(i: &Insn, mut e: Emit, c: u8) -> Result<Encoded, AsmError> {
    let ops = i.operands();
    let [op] = ops else {
        return Err(form(i, "needs a target"));
    };
    let to = addr_of(op).ok_or(form(i, "a conditional jump takes a direct target"))?;
    let short = rel(i, to, 2);
    if (-0x80..=0x7f).contains(&short) {
        e.op(&[0x70 + c]);
        e.imm = Some((short, 1));
        return e.finish(i);
    }
    let near = rel(i, to, 6);
    if !(-0x8000_0000..=0x7fff_ffff).contains(&near) {
        return Err(branch_range(i, to, -0x8000_0000 + 6, 0x7fff_ffff + 6));
    }
    e.op(&[0x0f, 0x80 + c]);
    e.imm = Some((near, 4));
    e.finish(i)
}

fn jmp_call(i: &Insn, mut e: Emit) -> Result<Encoded, AsmError> {
    let ops = i.operands();
    let [op] = ops else {
        return Err(form(i, "needs a target"));
    };
    let call = i.mnemonic == "call";
    match op {
        Operand::Addr(_) | Operand::Imm(_) | Operand::UImm(_) | Operand::Count(_) => {
            let to = addr_of(op).expect("matched an address-shaped operand");
            if !call {
                let short = rel(i, to, 2);
                if (-0x80..=0x7f).contains(&short) {
                    e.op(&[0xeb]);
                    e.imm = Some((short, 1));
                    return e.finish(i);
                }
            }
            let near = rel(i, to, 5);
            if !(-0x8000_0000..=0x7fff_ffff).contains(&near) {
                return Err(branch_range(i, to, -0x8000_0000 + 5, 0x7fff_ffff + 5));
            }
            e.op(&[if call { 0xe8 } else { 0xe9 }]);
            e.imm = Some((near, 4));
            e.finish(i)
        }
        rm => {
            // An indirect branch is 64-bit by default, so its operand needs no
            // REX.W and cannot be written 32 bits wide.
            let w = operand_width(i, &[rm])?;
            if w != Width::W64 {
                return Err(form(
                    i,
                    "an indirect branch in long mode goes through a 64-bit operand",
                ));
            }
            e.op(&[0xff]);
            e.modrm_pair(i, if call { 2 } else { 4 }, rm_of(i, rm)?)?;
            e.finish(i)
        }
    }
}

// ------------------------------------------------------------------ padding

/// The canonical multi-byte no-ops, indexed by length minus one.
///
/// These are the sequences the Intel optimization manual recommends and the
/// ones every toolchain emits, which matters because a patch that pads with an
/// unusual no-op is a patch a later reader has to stop and decode.
const NOPS: [&[u8]; 9] = [
    &[0x90],
    &[0x66, 0x90],
    &[0x0f, 0x1f, 0x00],
    &[0x0f, 0x1f, 0x40, 0x00],
    &[0x0f, 0x1f, 0x44, 0x00, 0x00],
    &[0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00],
    &[0x0f, 0x1f, 0x80, 0x00, 0x00, 0x00, 0x00],
    &[0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00],
    &[0x66, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00],
];

/// Fill `len` bytes with as few no-ops as possible.
pub fn padding(len: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(len);
    let mut left = len;
    while left > 0 {
        let take = left.min(NOPS.len());
        out.extend_from_slice(NOPS[take - 1]);
        left -= take;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use r12e_arch::insn::Flow;

    fn asm(text: &str) -> Vec<u8> {
        asm_at(text, 0x1000)
    }

    fn asm_at(text: &str, at: u64) -> Vec<u8> {
        crate::assemble(&r12e_core::Arch::X86_64, text, Addr(at))
            .unwrap_or_else(|e| panic!("{text}: {e}"))
            .bytes()
            .to_vec()
    }

    fn refused(text: &str) -> AsmError {
        crate::assemble(&r12e_core::Arch::X86_64, text, Addr(0x1000)).expect_err("should refuse")
    }

    #[test]
    fn the_mnemonic_table_is_sorted_and_unique() {
        for w in MNEMONICS.windows(2) {
            assert!(w[0] < w[1], "{} then {}", w[0], w[1]);
        }
    }

    #[test]
    fn rex_is_computed_from_the_registers() {
        assert_eq!(asm("mov rax, rcx"), [0x48, 0x89, 0xc8]);
        assert_eq!(asm("mov r8, r15"), [0x4d, 0x89, 0xf8]);
        assert_eq!(asm("mov eax, ecx"), [0x89, 0xc8]);
        // spl exists only with REX present, even though no extension bit is.
        assert_eq!(asm("mov spl, al"), [0x40, 0x88, 0xc4]);
        assert_eq!(asm("mov ah, al"), [0x88, 0xc4]);
    }

    #[test]
    fn a_high_byte_register_and_rex_cannot_meet() {
        assert!(matches!(
            refused("mov ah, r8b"),
            AsmError::UnsupportedForm { .. }
        ));
    }

    #[test]
    fn immediates_take_the_shortest_form_that_holds_them() {
        assert_eq!(asm("add rax, 0x1"), [0x48, 0x83, 0xc0, 0x01]);
        assert_eq!(asm("add eax, 0x1234"), [0x05, 0x34, 0x12, 0x00, 0x00]);
        assert_eq!(asm("add ecx, 0x1234"), [0x81, 0xc1, 0x34, 0x12, 0x00, 0x00]);
        assert_eq!(asm("mov eax, 0x1"), [0xb8, 0x01, 0x00, 0x00, 0x00]);
        assert_eq!(
            asm("mov rax, 0x1"),
            [0x48, 0xc7, 0xc0, 0x01, 0x00, 0x00, 0x00]
        );
    }

    #[test]
    fn a_wide_immediate_needs_the_ten_byte_move() {
        assert_eq!(
            asm("movabs rax, 0x1122334455667788"),
            [0x48, 0xb8, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11]
        );
        // A value that does not fit a sign-extended doubleword picks the same
        // form without being asked.
        assert_eq!(asm("mov rax, 0xffffffff")[1], 0xb8);
    }

    #[test]
    fn addressing_modes_build_the_right_sib() {
        assert_eq!(asm("mov eax, dword ptr [rbx]"), [0x8b, 0x03]);
        assert_eq!(asm("mov eax, dword ptr [rsp]"), [0x8b, 0x04, 0x24]);
        assert_eq!(asm("mov eax, dword ptr [rbp]"), [0x8b, 0x45, 0x00]);
        assert_eq!(
            asm("mov eax, dword ptr [rbx + 4*rcx + 0x10]"),
            [0x8b, 0x44, 0x8b, 0x10]
        );
        assert_eq!(
            asm("lea rax, [rip + 0x10]"),
            [0x48, 0x8d, 0x05, 0x10, 0, 0, 0]
        );
        assert_eq!(asm("mov eax, dword ptr [r12]"), [0x41, 0x8b, 0x04, 0x24]);
    }

    #[test]
    fn rsp_cannot_be_an_index() {
        assert!(matches!(
            refused("mov eax, dword ptr [rax + 1*rsp]"),
            AsmError::UnsupportedForm { .. }
        ));
    }

    #[test]
    fn a_short_jump_is_chosen_when_it_reaches() {
        assert_eq!(asm_at("jmp 0x1002", 0x1000), [0xeb, 0x00]);
        assert_eq!(asm_at("jmp 0x2000", 0x1000), [0xe9, 0xfb, 0x0f, 0x00, 0x00]);
        assert_eq!(asm_at("je 0x1002", 0x1000), [0x74, 0x00]);
        assert_eq!(
            asm_at("je 0x2000", 0x1000),
            [0x0f, 0x84, 0xfa, 0x0f, 0x00, 0x00]
        );
        assert_eq!(
            asm_at("call 0x2000", 0x1000),
            [0xe8, 0xfb, 0x0f, 0x00, 0x00]
        );
    }

    #[test]
    fn an_unreachable_branch_names_its_range() {
        let e = crate::assemble(&r12e_core::Arch::X86_64, "call 0x90000000", Addr(0))
            .expect_err("out of range");
        assert!(matches!(e, AsmError::BranchRange { .. }), "{e}");
        // A truncated displacement is the one mistake this must never make.
        assert!(crate::assemble(&r12e_core::Arch::X86_64, "call 0x7ffffffc", Addr(0)).is_ok());
    }

    #[test]
    fn a_memory_operand_with_no_width_is_refused_by_name() {
        assert!(matches!(
            refused("mov [rax], 0x1"),
            AsmError::UnsizedOperand { .. }
        ));
    }

    #[test]
    fn the_shift_count_forms_stay_distinct() {
        // The decoder prints the one-byte shift with no count at all, so the
        // two spellings have to encode differently or the round trip loses.
        assert_eq!(asm("shl eax"), [0xd1, 0xe0]);
        assert_eq!(asm("shl eax, 0x1"), [0xc1, 0xe0, 0x01]);
        assert_eq!(asm("shl eax, cl"), [0xd3, 0xe0]);
        assert_eq!(asm("sar rax, 0x3f"), [0x48, 0xc1, 0xf8, 0x3f]);
    }

    #[test]
    fn the_odds_and_ends_a_patch_needs() {
        assert_eq!(asm("nop"), [0x90]);
        assert_eq!(asm("int3"), [0xcc]);
        assert_eq!(asm("ret"), [0xc3]);
        assert_eq!(asm("ret 0x8"), [0xc2, 0x08, 0x00]);
        assert_eq!(asm("leave"), [0xc9]);
        assert_eq!(asm("endbr64"), [0xf3, 0x0f, 0x1e, 0xfa]);
        assert_eq!(asm("syscall"), [0x0f, 0x05]);
        assert_eq!(asm("push rbp"), [0x55]);
        assert_eq!(asm("push r12"), [0x41, 0x54]);
        assert_eq!(asm("pop rbp"), [0x5d]);
        assert_eq!(asm("sete al"), [0x0f, 0x94, 0xc0]);
        assert_eq!(asm("movzx eax, byte ptr [rdi]"), [0x0f, 0xb6, 0x07]);
        assert_eq!(asm("movsxd rax, ecx"), [0x48, 0x63, 0xc1]);
        assert_eq!(asm("imul eax, ecx, 0x10"), [0x6b, 0xc1, 0x10]);
        assert_eq!(asm("xchg rax, rcx"), [0x48, 0x91]);
        assert_eq!(asm("test eax, eax"), [0x85, 0xc0]);
        assert_eq!(asm("cmp byte ptr [rdi], 0x0"), [0x80, 0x3f, 0x00]);
        assert_eq!(asm("cmp al, 0x1"), [0x3c, 0x01]);
    }

    #[test]
    fn a_prefix_rides_ahead_of_the_instruction() {
        assert_eq!(
            asm("lock\tcmpxchg dword ptr [rdi], esi"),
            [0xf0, 0x0f, 0xb1, 0x37]
        );
        assert_eq!(asm("pause"), [0xf3, 0x90]);
    }

    #[test]
    fn padding_is_made_of_canonical_no_ops() {
        for n in 1..64usize {
            let p = padding(n);
            assert_eq!(p.len(), n, "padding {n}");
            // Every byte of it has to decode as a no-op, or the fall-through
            // path runs into something.
            let mut at = 0usize;
            while at < p.len() {
                let d = r12e_arch::x86::decode(&p[at..], Addr(0x1000 + at as u64))
                    .unwrap_or_else(|| panic!("padding {n} at {at} does not decode"));
                assert_eq!(d.mnemonic, "nop");
                at += d.len as usize;
            }
        }
    }

    #[test]
    fn an_insn_built_by_hand_encodes_without_text() {
        let mut i = Insn::new(Addr(0x1000), 0, "ret", Flow::Return);
        assert_eq!(encode(&i).unwrap().bytes(), [0xc3]);
        i = Insn::new(Addr(0x1000), 0, "push", Flow::Next);
        i.push(Operand::Reg(Reg::gpr(5, Width::W64)));
        assert_eq!(encode(&i).unwrap().bytes(), [0x55]);
    }
}
