//! x86 opcode tables.
//!
//! Operand kinds use the Intel manual's own notation (`Ev`, `Gb`, `Iz`), so an
//! entry can be checked against appendix A line by line. That is the whole
//! reason for the shorthand: a table you cannot diff against the specification
//! is a table nobody can audit.

/// How one operand is encoded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(non_camel_case_types)]
pub enum Op {
    /// Absent.
    None,
    /// ModRM r/m, byte.
    Eb,
    /// ModRM r/m, word.
    Ew,
    /// ModRM r/m, doubleword.
    Ed,
    /// ModRM r/m at the operand size.
    Ev,
    /// ModRM r/m, forced 64-bit.
    Eq,
    /// ModRM reg, byte.
    Gb,
    /// ModRM reg, word.
    Gw,
    /// ModRM reg, doubleword.
    Gd,
    /// ModRM reg at the operand size.
    Gv,
    /// Immediate byte, printed signed. llvm prints every byte immediate of an
    /// integer instruction as a signed number, so `add al, 0x80` reads back as
    /// `add al, -0x80`.
    Ib,
    /// Immediate byte, printed unsigned: a shift count, a port, an interrupt
    /// number, or an SSE selector, none of which is a number line.
    Ibu,
    /// Immediate byte, sign-extended to the operand size.
    Ibs,
    /// Immediate word.
    Iw,
    /// Immediate doubleword.
    Id,
    /// Immediate, word or doubleword, sign-extended to the operand size.
    Iz,
    /// Immediate at the full operand size, so 8 bytes under REX.W.
    Iv,
    /// Relative byte displacement.
    Jb,
    /// Relative word or doubleword displacement.
    Jz,
    /// ModRM, memory only.
    M,
    /// A far pointer in memory.
    Mp,
    /// The accumulator, byte.
    AL,
    /// The accumulator at the operand size.
    EAX,
    /// `cl`, the implicit shift count.
    CL,
    /// `dx`, the implicit port.
    DX,
    /// Register in the low three opcode bits, byte.
    Rb,
    /// Register in the low three opcode bits, at the operand size.
    Rv,
    /// Absolute offset, byte.
    Ob,
    /// Absolute offset at the operand size.
    Ov,
    /// A segment register from ModRM reg.
    Sw,
    /// A segment register named by bits 3 to 5 of the opcode, as the `push`
    /// and `pop` of a segment do. These carry no ModRM byte.
    Sr,
    /// The literal 1.
    One,
    /// ModRM reg as an SSE register.
    Vx,
    /// ModRM r/m as an SSE register or memory.
    Wx,
    /// ModRM r/m as an SSE register only.
    Ux,
    /// A control register.
    Cd,
    /// A debug register.
    Dd,
    /// ModRM reg as an MMX register.
    Pq,
    /// ModRM r/m as an MMX register or memory.
    Qq,
    /// ModRM r/m as an MMX register only.
    Nq,
    /// A far pointer immediate: offset then segment, printed segment first.
    Ap,
    /// ModRM r/m: a word in memory, the operand size in a register. Only the
    /// segment register store at 0x8c encodes this way.
    Ewm,
    /// `xmm0`, the implicit mask of the variable blends.
    XMM0,
    /// ModRM r/m: a byte in memory, the operand size in a register, which is
    /// how the SSE4 byte extract and insert print.
    Ebm,
}

/// One opcode's mnemonic and operands.
#[derive(Debug, Clone, Copy)]
pub struct Entry {
    /// The mnemonic, or empty when the opcode is not allocated here.
    pub m: &'static str,
    /// Operands in Intel order: destination first.
    pub ops: [Op; 3],
    /// Index into [`GROUPS`] when the ModRM reg field selects the instruction.
    pub group: u8,
    /// Bytes a memory `Wx` operand touches, when it is not the full 16. A
    /// scalar `movsd` reads eight bytes and `movss` four, and llvm prints the
    /// difference, so the table has to carry it.
    pub msize: u8,
}

/// No instruction at this opcode.
pub const BAD: Entry = Entry {
    m: "",
    ops: [Op::None, Op::None, Op::None],
    group: 0,
    msize: 0,
};

const fn e(m: &'static str, a: Op, b: Op, c: Op) -> Entry {
    Entry {
        m,
        ops: [a, b, c],
        group: 0,
        msize: 0,
    }
}

/// Like [`e`], with an explicit memory operand size.
const fn es(m: &'static str, a: Op, b: Op, c: Op, msize: u8) -> Entry {
    Entry {
        m,
        ops: [a, b, c],
        group: 0,
        msize,
    }
}

const fn g(n: u8, a: Op, b: Op) -> Entry {
    Entry {
        m: "",
        ops: [a, b, Op::None],
        group: n,
        msize: 0,
    }
}

/// Like [`g`], with an explicit memory operand size.
const fn gs(n: u8, a: Op, b: Op, msize: u8) -> Entry {
    Entry {
        m: "",
        ops: [a, b, Op::None],
        group: n,
        msize,
    }
}

use Op::*;

/// Group numbers, matching the Intel manual's numbering where it has one.
/// Group selector for opcode 0x80.
pub const G_80: u8 = 1;
/// Group selector for opcode 0x81.
pub const G_81: u8 = 2;
/// Group selector for opcode 0x83.
pub const G_83: u8 = 3;
/// Group selector for opcode 0xc0.
pub const G_C0: u8 = 4;
/// Group selector for opcode 0xc1.
pub const G_C1: u8 = 5;
/// Group selector for opcode 0xd0.
pub const G_D0: u8 = 6;
/// Group selector for opcode 0xd1.
pub const G_D1: u8 = 7;
/// Group selector for opcode 0xd2.
pub const G_D2: u8 = 8;
/// Group selector for opcode 0xd3.
pub const G_D3: u8 = 9;
/// Group selector for opcode 0xf6.
pub const G_F6: u8 = 10;
/// Group selector for opcode 0xf7.
pub const G_F7: u8 = 11;
/// Group selector for opcode 0xfe.
pub const G_FE: u8 = 12;
/// Group selector for opcode 0xff.
pub const G_FF: u8 = 13;
/// Group selector for opcode 0xc6.
pub const G_C6: u8 = 14;
/// Group selector for opcode 0xc7.
pub const G_C7: u8 = 15;
/// Group selector for opcode 0x8f.
pub const G_8F: u8 = 16;
/// Group selector for opcode 0x0f00.
pub const G_0F00: u8 = 17;
/// Group selector for opcode 0x0f01.
pub const G_0F01: u8 = 18;
/// Group selector for opcode 0x0fba.
pub const G_0FBA: u8 = 19;
/// Group selector for opcode 0x0fae.
pub const G_0FAE: u8 = 20;
/// Group selector for opcode 0x0fc7.
pub const G_0FC7: u8 = 21;
/// Group selector for `0x0f 0xae` with a register operand, which names the
/// fences rather than the state-save instructions its memory forms do.
pub const G_0FAE_REG: u8 = 22;
/// Group selector for opcode 0x82, the 32-bit-only alias of 0x80.
pub const G_82: u8 = 23;
/// Group selector for `0x0f 0x0d`, the AMD prefetch hints.
pub const G_0F0D: u8 = 24;
/// Group selector for `0x0f 0x18`, the prefetch hints.
pub const G_0F18: u8 = 25;
/// Group selector for `0x0f 0x71`, the word shifts.
pub const G_0F71: u8 = 26;
/// Group selector for `0x0f 0x72`, the doubleword shifts.
pub const G_0F72: u8 = 27;
/// Group selector for `0x0f 0x73`, the quadword shifts.
pub const G_0F73: u8 = 28;

/// The eight instructions a group's ModRM reg field selects between.
pub struct Group(pub [&'static str; 8]);

/// Group tables, indexed by the constants above minus one.
pub const GROUPS: &[Group] = &[
    // 1: 0x80
    Group(["add", "or", "adc", "sbb", "and", "sub", "xor", "cmp"]),
    // 2: 0x81
    Group(["add", "or", "adc", "sbb", "and", "sub", "xor", "cmp"]),
    // 3: 0x83
    Group(["add", "or", "adc", "sbb", "and", "sub", "xor", "cmp"]),
    // 4: 0xc0
    Group(["rol", "ror", "rcl", "rcr", "shl", "shr", "shl", "sar"]),
    // 5: 0xc1
    Group(["rol", "ror", "rcl", "rcr", "shl", "shr", "shl", "sar"]),
    // 6: 0xd0
    Group(["rol", "ror", "rcl", "rcr", "shl", "shr", "shl", "sar"]),
    // 7: 0xd1
    Group(["rol", "ror", "rcl", "rcr", "shl", "shr", "shl", "sar"]),
    // 8: 0xd2
    Group(["rol", "ror", "rcl", "rcr", "shl", "shr", "shl", "sar"]),
    // 9: 0xd3
    Group(["rol", "ror", "rcl", "rcr", "shl", "shr", "shl", "sar"]),
    // 10: 0xf6
    Group(["test", "test", "not", "neg", "mul", "imul", "div", "idiv"]),
    // 11: 0xf7
    Group(["test", "test", "not", "neg", "mul", "imul", "div", "idiv"]),
    // 12: 0xfe
    Group(["inc", "dec", "", "", "", "", "", ""]),
    // 13: 0xff
    Group(["inc", "dec", "call", "lcall", "jmp", "ljmp", "push", ""]),
    // 14: 0xc6
    Group(["mov", "", "", "", "", "", "", ""]),
    // 15: 0xc7
    Group(["mov", "", "", "", "", "", "", ""]),
    // 16: 0x8f
    Group(["pop", "", "", "", "", "", "", ""]),
    // 17: 0x0f 0x00
    Group(["sldt", "str", "lldt", "ltr", "verr", "verw", "", ""]),
    // 18: 0x0f 0x01
    Group(["sgdt", "sidt", "lgdt", "lidt", "smsw", "", "lmsw", "invlpg"]),
    // 19: 0x0f 0xba
    Group(["", "", "", "", "bt", "bts", "btr", "btc"]),
    // 20: 0x0f 0xae
    Group([
        "fxsave", "fxrstor", "ldmxcsr", "stmxcsr", "xsave", "xrstor", "xsaveopt", "clflush",
    ]),
    // 21: 0x0f 0xc7
    Group(["", "cmpxchg8b", "", "", "", "", "rdrand", "rdseed"]),
    // 22: 0x0f 0xae, register forms
    Group(["", "", "", "", "", "lfence", "mfence", "sfence"]),
    // 23: 0x82
    Group(["add", "or", "adc", "sbb", "and", "sub", "xor", "cmp"]),
    // 24: 0x0f 0x0d
    Group(["prefetch", "prefetchw", "prefetchwt1", "", "", "", "", ""]),
    // 25: 0x0f 0x18
    Group([
        "prefetchnta",
        "prefetcht0",
        "prefetcht1",
        "prefetcht2",
        "",
        "",
        "",
        "",
    ]),
    // 26: 0x0f 0x71
    Group(["", "", "psrlw", "", "psraw", "", "psllw", ""]),
    // 27: 0x0f 0x72
    Group(["", "", "psrld", "", "psrad", "", "pslld", ""]),
    // 28: 0x0f 0x73
    Group(["", "", "psrlq", "psrldq", "", "", "psllq", "pslldq"]),
];

/// The memory operand size a group's slot touches, where it is not the
/// operand size. Zero is a block with no scalar width, which llvm prints with
/// no size hint at all. `None` means the entry's own size applies.
pub fn group_msize(group: u8, sel: usize) -> Option<u8> {
    // `Op::None` is in scope here, so the empty answer needs its full name.
    let row: [i8; 8] = match group {
        // 0x0f 0x00: every slot is a sixteen-bit selector.
        G_0F00 => [2; 8],
        // 0x0f 0x01: the descriptor tables have no scalar width, the machine
        // status word is sixteen bits, and `invlpg` names a byte.
        G_0F01 => [0, 0, 0, 0, 2, 2, 2, 1],
        // 0x0f 0xae: the state blocks have no width, the control and status
        // word are doublewords, and `clflush` names a byte.
        G_0FAE => [0, 0, 4, 4, 0, 0, 0, 1],
        // 0x0f 0xc7: `cmpxchg8b` touches eight bytes.
        G_0FC7 => [-1, 8, -1, -1, -1, -1, -1, -1],
        // The prefetch hints all name a byte.
        G_0F0D | G_0F18 => [1; 8],
        // 0xff /3 and /5 are the far indirect branches, which print no size.
        G_FF => [-1, -1, -1, 0, -1, 0, -1, -1],
        _ => return Option::None,
    };
    match row[sel & 7] {
        -1 => Option::None,
        n => Some(n as u8),
    }
}

/// The same, for a group's register forms. `sldt` and `str` store into a
/// register at the operand size, while everything else in their group names a
/// sixteen-bit selector whatever the operand size is.
pub fn group_msize_reg(group: u8, sel: usize) -> Option<u8> {
    match (group, sel) {
        (G_0F00, 2..=5) => Some(2),
        _ => Option::None,
    }
}

/// Condition names, indexed by the low four bits of a `jcc`, `setcc` or
/// `cmovcc` opcode.
pub const CC: [&str; 16] = [
    "o", "no", "b", "ae", "e", "ne", "be", "a", "s", "ns", "p", "np", "l", "ge", "le", "g",
];

/// Mnemonics for `jcc` with a one-byte displacement, `0x70` to `0x7f`.
pub const JCC: [&str; 16] = [
    "jo", "jno", "jb", "jae", "je", "jne", "jbe", "ja", "js", "jns", "jp", "jnp", "jl", "jge",
    "jle", "jg",
];

/// Mnemonics for `setcc`, `0x0f 0x90` to `0x0f 0x9f`.
pub const SETCC: [&str; 16] = [
    "seto", "setno", "setb", "setae", "sete", "setne", "setbe", "seta", "sets", "setns", "setp",
    "setnp", "setl", "setge", "setle", "setg",
];

/// Mnemonics for `cmovcc`, `0x0f 0x40` to `0x0f 0x4f`.
pub const CMOVCC: [&str; 16] = [
    "cmovo", "cmovno", "cmovb", "cmovae", "cmove", "cmovne", "cmovbe", "cmova", "cmovs", "cmovns",
    "cmovp", "cmovnp", "cmovl", "cmovge", "cmovle", "cmovg",
];

/// The one-byte opcode map.
///
/// Opcodes removed in 64-bit mode (the one-byte `inc`/`dec` block, `pusha`,
/// `arpl`, the BCD instructions) are [`BAD`], because in long mode those bytes
/// are REX prefixes or nothing at all.
pub const ONE_BYTE: [Entry; 256] = {
    let mut t = [BAD; 256];
    // 0x00: the eight arithmetic groups, each six encodings.
    t[0x00] = e("add", Eb, Gb, None);
    t[0x01] = e("add", Ev, Gv, None);
    t[0x02] = e("add", Gb, Eb, None);
    t[0x03] = e("add", Gv, Ev, None);
    t[0x04] = e("add", AL, Ib, None);
    t[0x05] = e("add", EAX, Iz, None);
    t[0x08] = e("or", Eb, Gb, None);
    t[0x09] = e("or", Ev, Gv, None);
    t[0x0a] = e("or", Gb, Eb, None);
    t[0x0b] = e("or", Gv, Ev, None);
    t[0x0c] = e("or", AL, Ib, None);
    t[0x0d] = e("or", EAX, Iz, None);
    t[0x10] = e("adc", Eb, Gb, None);
    t[0x11] = e("adc", Ev, Gv, None);
    t[0x12] = e("adc", Gb, Eb, None);
    t[0x13] = e("adc", Gv, Ev, None);
    t[0x14] = e("adc", AL, Ib, None);
    t[0x15] = e("adc", EAX, Iz, None);
    t[0x18] = e("sbb", Eb, Gb, None);
    t[0x19] = e("sbb", Ev, Gv, None);
    t[0x1a] = e("sbb", Gb, Eb, None);
    t[0x1b] = e("sbb", Gv, Ev, None);
    t[0x1c] = e("sbb", AL, Ib, None);
    t[0x1d] = e("sbb", EAX, Iz, None);
    t[0x20] = e("and", Eb, Gb, None);
    t[0x21] = e("and", Ev, Gv, None);
    t[0x22] = e("and", Gb, Eb, None);
    t[0x23] = e("and", Gv, Ev, None);
    t[0x24] = e("and", AL, Ib, None);
    t[0x25] = e("and", EAX, Iz, None);
    t[0x28] = e("sub", Eb, Gb, None);
    t[0x29] = e("sub", Ev, Gv, None);
    t[0x2a] = e("sub", Gb, Eb, None);
    t[0x2b] = e("sub", Gv, Ev, None);
    t[0x2c] = e("sub", AL, Ib, None);
    t[0x2d] = e("sub", EAX, Iz, None);
    t[0x30] = e("xor", Eb, Gb, None);
    t[0x31] = e("xor", Ev, Gv, None);
    t[0x32] = e("xor", Gb, Eb, None);
    t[0x33] = e("xor", Gv, Ev, None);
    t[0x34] = e("xor", AL, Ib, None);
    t[0x35] = e("xor", EAX, Iz, None);
    t[0x38] = e("cmp", Eb, Gb, None);
    t[0x39] = e("cmp", Ev, Gv, None);
    t[0x3a] = e("cmp", Gb, Eb, None);
    t[0x3b] = e("cmp", Gv, Ev, None);
    t[0x3c] = e("cmp", AL, Ib, None);
    t[0x3d] = e("cmp", EAX, Iz, None);

    // 0x50: push and pop of the opcode-embedded register.
    let mut i = 0;
    while i < 8 {
        t[0x50 + i] = e("push", Rv, None, None);
        t[0x58 + i] = e("pop", Rv, None, None);
        i += 1;
    }

    t[0x63] = e("movsxd", Gv, Ed, None);
    t[0x68] = e("push", Iz, None, None);
    t[0x69] = e("imul", Gv, Ev, Iz);
    t[0x6a] = e("push", Ibs, None, None);
    t[0x6b] = e("imul", Gv, Ev, Ibs);
    t[0x6c] = e("insb", None, None, None);
    t[0x6d] = e("insd", None, None, None);
    t[0x6e] = e("outsb", None, None, None);
    t[0x6f] = e("outsd", None, None, None);

    // 0x70: the short conditional jumps.
    let mut i = 0;
    while i < 16 {
        t[0x70 + i] = e(JCC[i], Jb, None, None);
        i += 1;
    }

    t[0x80] = g(G_80, Eb, Ib);
    t[0x81] = g(G_81, Ev, Iz);
    t[0x83] = g(G_83, Ev, Ibs);
    t[0x84] = e("test", Eb, Gb, None);
    t[0x85] = e("test", Ev, Gv, None);
    t[0x86] = e("xchg", Eb, Gb, None);
    t[0x87] = e("xchg", Ev, Gv, None);
    t[0x88] = e("mov", Eb, Gb, None);
    t[0x89] = e("mov", Ev, Gv, None);
    t[0x8a] = e("mov", Gb, Eb, None);
    t[0x8b] = e("mov", Gv, Ev, None);
    t[0x8c] = e("mov", Ewm, Sw, None);
    t[0x8d] = e("lea", Gv, M, None);
    t[0x8e] = e("mov", Sw, Ewm, None);
    t[0x8f] = g(G_8F, Ev, None);

    t[0x90] = e("nop", None, None, None);
    let mut i = 1;
    while i < 8 {
        t[0x90 + i] = e("xchg", EAX, Rv, None);
        i += 1;
    }
    t[0x98] = e("cwde", None, None, None);
    t[0x99] = e("cdq", None, None, None);
    t[0x9b] = e("wait", None, None, None);
    t[0x9c] = e("pushf", None, None, None);
    t[0x9d] = e("popf", None, None, None);
    t[0x9e] = e("sahf", None, None, None);
    t[0x9f] = e("lahf", None, None, None);

    t[0xa0] = e("mov", AL, Ob, None);
    t[0xa1] = e("mov", EAX, Ov, None);
    t[0xa2] = e("mov", Ob, AL, None);
    t[0xa3] = e("mov", Ov, EAX, None);
    t[0xa4] = e("movsb", None, None, None);
    t[0xa5] = e("movsd", None, None, None);
    t[0xa6] = e("cmpsb", None, None, None);
    t[0xa7] = e("cmpsd", None, None, None);
    t[0xa8] = e("test", AL, Ib, None);
    t[0xa9] = e("test", EAX, Iz, None);
    t[0xaa] = e("stosb", None, None, None);
    t[0xab] = e("stosd", None, None, None);
    t[0xac] = e("lodsb", None, None, None);
    t[0xad] = e("lodsd", None, None, None);
    t[0xae] = e("scasb", None, None, None);
    t[0xaf] = e("scasd", None, None, None);

    let mut i = 0;
    while i < 8 {
        t[0xb0 + i] = e("mov", Rb, Ib, None);
        t[0xb8 + i] = e("mov", Rv, Iv, None);
        i += 1;
    }

    t[0xc0] = g(G_C0, Eb, Ibu);
    t[0xc1] = g(G_C1, Ev, Ibu);
    t[0xc2] = e("ret", Iw, None, None);
    t[0xc3] = e("ret", None, None, None);
    t[0xc6] = g(G_C6, Eb, Ib);
    t[0xc7] = g(G_C7, Ev, Iz);
    t[0xc8] = e("enter", Iw, Ib, None);
    t[0xc9] = e("leave", None, None, None);
    t[0xca] = e("lret", Iw, None, None);
    t[0xcb] = e("lret", None, None, None);
    t[0xcc] = e("int3", None, None, None);
    t[0xcd] = e("int", Ibu, None, None);
    t[0xcf] = e("iret", None, None, None);

    // The shift-by-one forms print with no count, as both objdumps do: the
    // opcode itself is the count.
    t[0xd0] = g(G_D0, Eb, None);
    t[0xd1] = g(G_D1, Ev, None);
    t[0xd2] = g(G_D2, Eb, CL);
    t[0xd3] = g(G_D3, Ev, CL);
    t[0xd7] = e("xlatb", None, None, None);

    t[0xe0] = e("loopne", Jb, None, None);
    t[0xe1] = e("loope", Jb, None, None);
    t[0xe2] = e("loop", Jb, None, None);
    t[0xe3] = e("jrcxz", Jb, None, None);
    t[0xe4] = e("in", AL, Ibu, None);
    t[0xe5] = e("in", EAX, Ibu, None);
    t[0xe6] = e("out", Ibu, AL, None);
    t[0xe7] = e("out", Ibu, EAX, None);
    t[0xe8] = e("call", Jz, None, None);
    t[0xe9] = e("jmp", Jz, None, None);
    t[0xeb] = e("jmp", Jb, None, None);
    t[0xec] = e("in", AL, DX, None);
    t[0xed] = e("in", EAX, DX, None);
    t[0xee] = e("out", DX, AL, None);
    t[0xef] = e("out", DX, EAX, None);

    t[0xf4] = e("hlt", None, None, None);
    t[0xf5] = e("cmc", None, None, None);
    t[0xf6] = g(G_F6, Eb, None);
    t[0xf7] = g(G_F7, Ev, None);
    t[0xf8] = e("clc", None, None, None);
    t[0xf9] = e("stc", None, None, None);
    t[0xfa] = e("cli", None, None, None);
    t[0xfb] = e("sti", None, None, None);
    t[0xfc] = e("cld", None, None, None);
    t[0xfd] = e("std", None, None, None);
    t[0xfe] = g(G_FE, Eb, None);
    t[0xff] = g(G_FF, Ev, None);
    t
};

/// The one-byte map as 32-bit mode sees it.
///
/// Same table, minus the encodings long mode reassigned and plus the ones it
/// dropped. This is the whole difference that matters at the first byte: 0x40
/// to 0x4f are `inc` and `dec` here rather than REX, and a decoder that gets
/// that wrong desynchronizes on the most common byte in the map.
pub const ONE_BYTE_32: [Entry; 256] = {
    let mut t = ONE_BYTE;

    // The segment push and pop pairs, which long mode dropped.
    t[0x06] = e("push", Sr, None, None);
    t[0x07] = e("pop", Sr, None, None);
    t[0x0e] = e("push", Sr, None, None);
    t[0x16] = e("push", Sr, None, None);
    t[0x17] = e("pop", Sr, None, None);
    t[0x1e] = e("push", Sr, None, None);
    t[0x1f] = e("pop", Sr, None, None);

    // The decimal adjust instructions.
    t[0x27] = e("daa", None, None, None);
    t[0x2f] = e("das", None, None, None);
    t[0x37] = e("aaa", None, None, None);
    t[0x3f] = e("aas", None, None, None);

    // 0x40 to 0x4f: inc and dec of a register, not a REX prefix.
    let mut i = 0;
    while i < 8 {
        t[0x40 + i] = e("inc", Rv, None, None);
        t[0x48 + i] = e("dec", Rv, None, None);
        i += 1;
    }

    t[0x60] = e("pushal", None, None, None);
    t[0x61] = e("popal", None, None, None);
    t[0x62] = e("bound", Gv, M, None);
    // 0x63 is `arpl`, not `movsxd`, and it is a word operation at any size.
    t[0x63] = e("arpl", Ew, Gw, None);

    // 0x82 duplicates 0x80. Long mode reclaimed it; here it is a real alias.
    t[0x82] = g(G_82, Eb, Ib);

    t[0x9a] = e("lcall", Ap, None, None);

    t[0xc4] = e("les", Gv, Mp, None);
    t[0xc5] = e("lds", Gv, Mp, None);
    t[0xce] = e("into", None, None, None);
    t[0xd4] = e("aam", Ib, None, None);
    t[0xd5] = e("aad", Ib, None, None);
    t[0xd6] = e("salc", None, None, None);
    t[0xea] = e("ljmp", Ap, None, None);
    t
};

/// The two-byte map, for opcodes with no mandatory prefix.
pub const TWO_BYTE: [Entry; 256] = {
    let mut t = [BAD; 256];
    t[0x00] = g(G_0F00, Ev, None);
    t[0x01] = g(G_0F01, M, None);
    t[0x05] = e("syscall", None, None, None);
    t[0x06] = e("clts", None, None, None);
    t[0x07] = e("sysret", None, None, None);
    t[0x02] = e("lar", Gv, Ew, None);
    t[0x03] = e("lsl", Gv, Ew, None);
    t[0x0b] = e("ud2", None, None, None);
    t[0x0d] = g(G_0F0D, M, None);
    t[0x10] = e("movups", Vx, Wx, None);
    t[0x11] = e("movups", Wx, Vx, None);
    t[0x12] = es("movlps", Vx, Wx, None, 8);
    t[0x13] = es("movlps", Wx, Vx, None, 8);
    t[0x14] = e("unpcklps", Vx, Wx, None);
    t[0x15] = e("unpckhps", Vx, Wx, None);
    t[0x16] = es("movhps", Vx, Wx, None, 8);
    t[0x17] = es("movhps", Wx, Vx, None, 8);
    t[0x18] = g(G_0F18, M, None);
    t[0x1f] = e("nop", Ev, None, None);
    t[0x20] = e("mov", Eq, Cd, None);
    t[0x21] = e("mov", Eq, Dd, None);
    t[0x22] = e("mov", Cd, Eq, None);
    t[0x23] = e("mov", Dd, Eq, None);
    t[0x28] = e("movaps", Vx, Wx, None);
    t[0x29] = e("movaps", Wx, Vx, None);
    t[0x2a] = e("cvtpi2ps", Vx, Qq, None);
    t[0x2c] = es("cvttps2pi", Pq, Wx, None, 8);
    t[0x2d] = es("cvtps2pi", Pq, Wx, None, 8);
    t[0x2e] = es("ucomiss", Vx, Wx, None, 4);
    t[0x2f] = es("comiss", Vx, Wx, None, 4);
    t[0x31] = e("rdtsc", None, None, None);
    t[0x34] = e("sysenter", None, None, None);
    t[0x35] = e("sysexit", None, None, None);

    let mut i = 0;
    while i < 16 {
        t[0x40 + i] = e(CMOVCC[i], Gv, Ev, None);
        t[0x80 + i] = e(JCC[i], Jz, None, None);
        t[0x90 + i] = e(SETCC[i], Eb, None, None);
        i += 1;
    }

    t[0x51] = e("sqrtps", Vx, Wx, None);
    t[0xc2] = e("cmpps", Vx, Wx, Ibu);
    t[0xc6] = e("shufps", Vx, Wx, Ibu);
    t[0x54] = e("andps", Vx, Wx, None);
    t[0x55] = e("andnps", Vx, Wx, None);
    t[0x56] = e("orps", Vx, Wx, None);
    t[0x57] = e("xorps", Vx, Wx, None);
    t[0x58] = e("addps", Vx, Wx, None);
    t[0x59] = e("mulps", Vx, Wx, None);
    t[0x5a] = es("cvtps2pd", Vx, Wx, None, 8);
    t[0x5b] = e("cvtdq2ps", Vx, Wx, None);
    t[0x5c] = e("subps", Vx, Wx, None);
    t[0x5d] = e("minps", Vx, Wx, None);
    t[0x5e] = e("divps", Vx, Wx, None);
    t[0x5f] = e("maxps", Vx, Wx, None);

    t[0x6e] = e("movd", Pq, Ev, None);
    t[0x6f] = e("movq", Pq, Qq, None);
    t[0x7e] = e("movd", Ev, Pq, None);
    t[0x7f] = e("movq", Qq, Pq, None);

    t[0xa0] = e("push", Sr, None, None);
    t[0xa1] = e("pop", Sr, None, None);
    t[0xa2] = e("cpuid", None, None, None);
    t[0xa8] = e("push", Sr, None, None);
    t[0xa9] = e("pop", Sr, None, None);
    t[0xa3] = e("bt", Ev, Gv, None);
    t[0xa4] = e("shld", Ev, Gv, Ibu);
    t[0xa5] = e("shld", Ev, Gv, CL);
    t[0xab] = e("bts", Ev, Gv, None);
    t[0xac] = e("shrd", Ev, Gv, Ibu);
    t[0xad] = e("shrd", Ev, Gv, CL);
    t[0xae] = g(G_0FAE, M, None);
    t[0xaf] = e("imul", Gv, Ev, None);
    t[0xb0] = e("cmpxchg", Eb, Gb, None);
    t[0xb1] = e("cmpxchg", Ev, Gv, None);
    t[0xb2] = e("lss", Gv, Mp, None);
    t[0xb3] = e("btr", Ev, Gv, None);
    t[0xb4] = e("lfs", Gv, Mp, None);
    t[0xb5] = e("lgs", Gv, Mp, None);
    t[0xb6] = e("movzx", Gv, Eb, None);
    t[0xb7] = e("movzx", Gv, Ew, None);
    t[0xba] = g(G_0FBA, Ev, Ibu);
    t[0xb9] = e("ud1", Gv, Ev, None);
    t[0xbb] = e("btc", Ev, Gv, None);
    t[0xbc] = e("bsf", Gv, Ev, None);
    t[0xbd] = e("bsr", Gv, Ev, None);
    t[0xbe] = e("movsx", Gv, Eb, None);
    t[0xbf] = e("movsx", Gv, Ew, None);
    t[0xc0] = e("xadd", Eb, Gb, None);
    t[0xc1] = e("xadd", Ev, Gv, None);
    t[0xc3] = e("movnti", Ed, Gd, None);
    t[0xc7] = gs(G_0FC7, M, None, 8);

    let mut i = 0;
    while i < 8 {
        t[0xc8 + i] = e("bswap", Rv, None, None);
        i += 1;
    }

    // The MMX register file, which has no mandatory prefix: the same opcodes
    // with 0x66 are the SSE2 forms in [`TWO_BYTE_66`]. A compiler stopped
    // emitting these long ago and a disassembler still meets them.
    t[0x0e] = e("femms", None, None, None);
    t[0x08] = e("invd", None, None, None);
    t[0x09] = e("wbinvd", None, None, None);
    t[0x30] = e("wrmsr", None, None, None);
    t[0x32] = e("rdmsr", None, None, None);
    t[0x33] = e("rdpmc", None, None, None);
    t[0x2b] = e("movntps", Wx, Vx, None);
    t[0x50] = e("movmskps", Gd, Ux, None);
    t[0x52] = e("rsqrtps", Vx, Wx, None);
    t[0x53] = e("rcpps", Vx, Wx, None);
    t[0x60] = es("punpcklbw", Pq, Qq, None, 4);
    t[0x61] = es("punpcklwd", Pq, Qq, None, 4);
    t[0x62] = es("punpckldq", Pq, Qq, None, 4);
    t[0x63] = es("packsswb", Pq, Qq, None, 8);
    t[0x64] = es("pcmpgtb", Pq, Qq, None, 8);
    t[0x65] = es("pcmpgtw", Pq, Qq, None, 8);
    t[0x66] = es("pcmpgtd", Pq, Qq, None, 8);
    t[0x67] = es("packuswb", Pq, Qq, None, 8);
    t[0x68] = es("punpckhbw", Pq, Qq, None, 8);
    t[0x69] = es("punpckhwd", Pq, Qq, None, 8);
    t[0x6a] = es("punpckhdq", Pq, Qq, None, 8);
    t[0x6b] = es("packssdw", Pq, Qq, None, 8);
    t[0x70] = es("pshufw", Pq, Qq, Ibu, 8);
    t[0x71] = g(G_0F71, Nq, Ibu);
    t[0x72] = g(G_0F72, Nq, Ibu);
    t[0x73] = g(G_0F73, Nq, Ibu);
    t[0x74] = es("pcmpeqb", Pq, Qq, None, 8);
    t[0x75] = es("pcmpeqw", Pq, Qq, None, 8);
    t[0x76] = es("pcmpeqd", Pq, Qq, None, 8);
    t[0x77] = e("emms", None, None, None);
    t[0xc4] = e("pinsrw", Pq, Ewm, Ibu);
    t[0xc5] = e("pextrw", Gd, Nq, Ibu);
    t[0xd1] = es("psrlw", Pq, Qq, None, 8);
    t[0xd2] = es("psrld", Pq, Qq, None, 8);
    t[0xd3] = es("psrlq", Pq, Qq, None, 8);
    t[0xd4] = es("paddq", Pq, Qq, None, 8);
    t[0xd5] = es("pmullw", Pq, Qq, None, 8);
    t[0xd7] = e("pmovmskb", Gd, Nq, None);
    t[0xd8] = es("psubusb", Pq, Qq, None, 8);
    t[0xd9] = es("psubusw", Pq, Qq, None, 8);
    t[0xda] = es("pminub", Pq, Qq, None, 8);
    t[0xdb] = es("pand", Pq, Qq, None, 8);
    t[0xdc] = es("paddusb", Pq, Qq, None, 8);
    t[0xdd] = es("paddusw", Pq, Qq, None, 8);
    t[0xde] = es("pmaxub", Pq, Qq, None, 8);
    t[0xdf] = es("pandn", Pq, Qq, None, 8);
    t[0xe0] = es("pavgb", Pq, Qq, None, 8);
    t[0xe1] = es("psraw", Pq, Qq, None, 8);
    t[0xe2] = es("psrad", Pq, Qq, None, 8);
    t[0xe3] = es("pavgw", Pq, Qq, None, 8);
    t[0xe4] = es("pmulhuw", Pq, Qq, None, 8);
    t[0xe5] = es("pmulhw", Pq, Qq, None, 8);
    t[0xe7] = es("movntq", Qq, Pq, None, 8);
    t[0xe8] = es("psubsb", Pq, Qq, None, 8);
    t[0xe9] = es("psubsw", Pq, Qq, None, 8);
    t[0xea] = es("pminsw", Pq, Qq, None, 8);
    t[0xeb] = es("por", Pq, Qq, None, 8);
    t[0xec] = es("paddsb", Pq, Qq, None, 8);
    t[0xed] = es("paddsw", Pq, Qq, None, 8);
    t[0xee] = es("pmaxsw", Pq, Qq, None, 8);
    t[0xef] = es("pxor", Pq, Qq, None, 8);
    t[0xf1] = es("psllw", Pq, Qq, None, 8);
    t[0xf2] = es("pslld", Pq, Qq, None, 8);
    t[0xf3] = es("psllq", Pq, Qq, None, 8);
    t[0xf4] = es("pmuludq", Pq, Qq, None, 8);
    t[0xf5] = es("pmaddwd", Pq, Qq, None, 8);
    t[0xf6] = es("psadbw", Pq, Qq, None, 8);
    t[0xf7] = e("maskmovq", Pq, Nq, None);
    t[0xf8] = es("psubb", Pq, Qq, None, 8);
    t[0xf9] = es("psubw", Pq, Qq, None, 8);
    t[0xfa] = es("psubd", Pq, Qq, None, 8);
    t[0xfb] = es("psubq", Pq, Qq, None, 8);
    t[0xfc] = es("paddb", Pq, Qq, None, 8);
    t[0xfd] = es("paddw", Pq, Qq, None, 8);
    t[0xfe] = es("paddd", Pq, Qq, None, 8);
    t
};

/// Two-byte opcodes selected by a mandatory `0x66` prefix.
pub const TWO_BYTE_66: [Entry; 256] = {
    let mut t = [BAD; 256];
    t[0x10] = e("movupd", Vx, Wx, None);
    t[0x11] = e("movupd", Wx, Vx, None);
    t[0x12] = es("movlpd", Vx, Wx, None, 8);
    t[0x13] = es("movlpd", Wx, Vx, None, 8);
    t[0x14] = e("unpcklpd", Vx, Wx, None);
    t[0x15] = e("unpckhpd", Vx, Wx, None);
    t[0x16] = es("movhpd", Vx, Wx, None, 8);
    t[0x17] = es("movhpd", Wx, Vx, None, 8);
    t[0x28] = e("movapd", Vx, Wx, None);
    t[0x29] = e("movapd", Wx, Vx, None);
    t[0x2e] = es("ucomisd", Vx, Wx, None, 8);
    t[0x2f] = es("comisd", Vx, Wx, None, 8);
    t[0x51] = e("sqrtpd", Vx, Wx, None);
    t[0x54] = e("andpd", Vx, Wx, None);
    t[0x55] = e("andnpd", Vx, Wx, None);
    t[0x56] = e("orpd", Vx, Wx, None);
    t[0x57] = e("xorpd", Vx, Wx, None);
    t[0x58] = e("addpd", Vx, Wx, None);
    t[0x59] = e("mulpd", Vx, Wx, None);
    t[0x5a] = e("cvtpd2ps", Vx, Wx, None);
    t[0x5b] = e("cvtps2dq", Vx, Wx, None);
    t[0x5c] = e("subpd", Vx, Wx, None);
    t[0x5d] = e("minpd", Vx, Wx, None);
    t[0x5e] = e("divpd", Vx, Wx, None);
    t[0x5f] = e("maxpd", Vx, Wx, None);
    t[0x60] = e("punpcklbw", Vx, Wx, None);
    t[0x61] = e("punpcklwd", Vx, Wx, None);
    t[0x62] = e("punpckldq", Vx, Wx, None);
    t[0x63] = e("packsswb", Vx, Wx, None);
    t[0x64] = e("pcmpgtb", Vx, Wx, None);
    t[0x65] = e("pcmpgtw", Vx, Wx, None);
    t[0x66] = e("pcmpgtd", Vx, Wx, None);
    t[0x67] = e("packuswb", Vx, Wx, None);
    t[0x68] = e("punpckhbw", Vx, Wx, None);
    t[0x69] = e("punpckhwd", Vx, Wx, None);
    t[0x6a] = e("punpckhdq", Vx, Wx, None);
    t[0x6b] = e("packssdw", Vx, Wx, None);
    t[0x6c] = e("punpcklqdq", Vx, Wx, None);
    t[0x6d] = e("punpckhqdq", Vx, Wx, None);
    t[0x6e] = e("movd", Vx, Ev, None);
    t[0x6f] = e("movdqa", Vx, Wx, None);
    t[0x70] = e("pshufd", Vx, Wx, Ibu);
    t[0x74] = e("pcmpeqb", Vx, Wx, None);
    t[0xc2] = e("cmppd", Vx, Wx, Ibu);
    t[0xc5] = e("pextrw", Gd, Ux, Ibu);
    t[0xc6] = e("shufpd", Vx, Wx, Ibu);
    t[0x2a] = es("cvtpi2pd", Vx, Qq, None, 8);
    t[0x2c] = e("cvttpd2pi", Pq, Wx, None);
    t[0x2d] = e("cvtpd2pi", Pq, Wx, None);
    t[0x7c] = e("haddpd", Vx, Wx, None);
    t[0x7d] = e("hsubpd", Vx, Wx, None);
    t[0xd0] = e("addsubpd", Vx, Wx, None);
    t[0xe6] = e("cvttpd2dq", Vx, Wx, None);
    t[0x75] = e("pcmpeqw", Vx, Wx, None);
    t[0x76] = e("pcmpeqd", Vx, Wx, None);
    t[0x7e] = e("movd", Ev, Vx, None);
    t[0x7f] = e("movdqa", Wx, Vx, None);
    t[0x2b] = e("movntpd", Wx, Vx, None);
    t[0x50] = e("movmskpd", Gd, Ux, None);
    t[0x71] = g(G_0F71, Ux, Ibu);
    t[0x72] = g(G_0F72, Ux, Ibu);
    t[0x73] = g(G_0F73, Ux, Ibu);
    t[0xc4] = e("pinsrw", Vx, Ewm, Ibu);
    t[0xd1] = e("psrlw", Vx, Wx, None);
    t[0xd2] = e("psrld", Vx, Wx, None);
    t[0xd3] = e("psrlq", Vx, Wx, None);
    t[0xe1] = e("psraw", Vx, Wx, None);
    t[0xe2] = e("psrad", Vx, Wx, None);
    t[0xe4] = e("pmulhuw", Vx, Wx, None);
    t[0xe5] = e("pmulhw", Vx, Wx, None);
    t[0xe7] = e("movntdq", Wx, Vx, None);
    t[0xf1] = e("psllw", Vx, Wx, None);
    t[0xf2] = e("pslld", Vx, Wx, None);
    t[0xf3] = e("psllq", Vx, Wx, None);
    t[0xf7] = e("maskmovdqu", Vx, Ux, None);
    t[0xd4] = e("paddq", Vx, Wx, None);
    t[0xd5] = e("pmullw", Vx, Wx, None);
    t[0xd6] = es("movq", Wx, Vx, None, 8);
    t[0xd7] = e("pmovmskb", Gd, Ux, None);
    t[0xd8] = e("psubusb", Vx, Wx, None);
    t[0xd9] = e("psubusw", Vx, Wx, None);
    t[0xda] = e("pminub", Vx, Wx, None);
    t[0xdb] = e("pand", Vx, Wx, None);
    t[0xdc] = e("paddusb", Vx, Wx, None);
    t[0xdd] = e("paddusw", Vx, Wx, None);
    t[0xde] = e("pmaxub", Vx, Wx, None);
    t[0xdf] = e("pandn", Vx, Wx, None);
    t[0xe0] = e("pavgb", Vx, Wx, None);
    t[0xe3] = e("pavgw", Vx, Wx, None);
    t[0xe8] = e("psubsb", Vx, Wx, None);
    t[0xe9] = e("psubsw", Vx, Wx, None);
    t[0xea] = e("pminsw", Vx, Wx, None);
    t[0xeb] = e("por", Vx, Wx, None);
    t[0xec] = e("paddsb", Vx, Wx, None);
    t[0xed] = e("paddsw", Vx, Wx, None);
    t[0xee] = e("pmaxsw", Vx, Wx, None);
    t[0xef] = e("pxor", Vx, Wx, None);
    t[0xf4] = e("pmuludq", Vx, Wx, None);
    t[0xf5] = e("pmaddwd", Vx, Wx, None);
    t[0xf6] = e("psadbw", Vx, Wx, None);
    t[0xf8] = e("psubb", Vx, Wx, None);
    t[0xf9] = e("psubw", Vx, Wx, None);
    t[0xfa] = e("psubd", Vx, Wx, None);
    t[0xfb] = e("psubq", Vx, Wx, None);
    t[0xfc] = e("paddb", Vx, Wx, None);
    t[0xfd] = e("paddw", Vx, Wx, None);
    t[0xfe] = e("paddd", Vx, Wx, None);
    t
};

/// Two-byte opcodes selected by a mandatory `0xf3` prefix.
pub const TWO_BYTE_F3: [Entry; 256] = {
    let mut t = [BAD; 256];
    t[0x10] = es("movss", Vx, Wx, None, 4);
    t[0x11] = es("movss", Wx, Vx, None, 4);
    t[0x2a] = e("cvtsi2ss", Vx, Ev, None);
    t[0x2c] = es("cvttss2si", Gv, Wx, None, 4);
    t[0x2d] = es("cvtss2si", Gv, Wx, None, 4);
    t[0x51] = es("sqrtss", Vx, Wx, None, 4);
    t[0x58] = es("addss", Vx, Wx, None, 4);
    t[0x59] = es("mulss", Vx, Wx, None, 4);
    t[0x5a] = es("cvtss2sd", Vx, Wx, None, 4);
    t[0x5b] = e("cvttps2dq", Vx, Wx, None);
    t[0x5c] = es("subss", Vx, Wx, None, 4);
    t[0x5d] = es("minss", Vx, Wx, None, 4);
    t[0x5e] = es("divss", Vx, Wx, None, 4);
    t[0x5f] = es("maxss", Vx, Wx, None, 4);
    t[0x6f] = e("movdqu", Vx, Wx, None);
    t[0xc2] = es("cmpss", Vx, Wx, Ibu, 4);
    t[0x70] = e("pshufhw", Vx, Wx, Ibu);
    t[0x7e] = es("movq", Vx, Wx, None, 8);
    t[0x7f] = e("movdqu", Wx, Vx, None);
    t[0xb8] = e("popcnt", Gv, Ev, None);
    t[0xbc] = e("tzcnt", Gv, Ev, None);
    t[0xbd] = e("lzcnt", Gv, Ev, None);
    t[0xe6] = es("cvtdq2pd", Vx, Wx, None, 8);
    t[0x09] = e("wbnoinvd", None, None, None);
    t[0x12] = e("movsldup", Vx, Wx, None);
    t[0x16] = e("movshdup", Vx, Wx, None);
    t[0x2b] = es("movntss", Wx, Vx, None, 4);
    t[0x52] = es("rsqrtss", Vx, Wx, None, 4);
    t[0x53] = es("rcpss", Vx, Wx, None, 4);
    t
};

/// Two-byte opcodes selected by a mandatory `0xf2` prefix.
pub const TWO_BYTE_F2: [Entry; 256] = {
    let mut t = [BAD; 256];
    t[0x10] = es("movsd", Vx, Wx, None, 8);
    t[0x11] = es("movsd", Wx, Vx, None, 8);
    t[0x12] = es("movddup", Vx, Wx, None, 8);
    t[0x2a] = e("cvtsi2sd", Vx, Ev, None);
    t[0x2c] = es("cvttsd2si", Gv, Wx, None, 8);
    t[0x2d] = es("cvtsd2si", Gv, Wx, None, 8);
    t[0x51] = es("sqrtsd", Vx, Wx, None, 8);
    t[0x58] = es("addsd", Vx, Wx, None, 8);
    t[0x59] = es("mulsd", Vx, Wx, None, 8);
    t[0x5a] = es("cvtsd2ss", Vx, Wx, None, 8);
    t[0x5c] = es("subsd", Vx, Wx, None, 8);
    t[0x5d] = es("minsd", Vx, Wx, None, 8);
    t[0x5e] = es("divsd", Vx, Wx, None, 8);
    t[0x5f] = es("maxsd", Vx, Wx, None, 8);
    t[0x70] = e("pshuflw", Vx, Wx, Ibu);
    t[0xc2] = es("cmpsd", Vx, Wx, Ibu, 8);
    t[0xe6] = e("cvtpd2dq", Vx, Wx, None);
    t[0x2b] = es("movntsd", Wx, Vx, None, 8);
    t[0x7c] = e("haddps", Vx, Wx, None);
    t[0x7d] = e("hsubps", Vx, Wx, None);
    t[0xd0] = e("addsubps", Vx, Wx, None);
    t[0xf0] = e("lddqu", Vx, Wx, None);
    t
};

/// The `0x0f 0x38` map with a mandatory `0x66`, which is where SSSE3 and SSE4
/// put the instructions compilers reach for.
pub const THREE_BYTE_38_66: [Entry; 256] = {
    let mut t = [BAD; 256];
    t[0x00] = e("pshufb", Vx, Wx, None);
    t[0x01] = e("phaddw", Vx, Wx, None);
    t[0x02] = e("phaddd", Vx, Wx, None);
    t[0x04] = e("pmaddubsw", Vx, Wx, None);
    t[0x05] = e("phsubw", Vx, Wx, None);
    t[0x06] = e("phsubd", Vx, Wx, None);
    t[0x08] = e("psignb", Vx, Wx, None);
    t[0x09] = e("psignw", Vx, Wx, None);
    t[0x0a] = e("psignd", Vx, Wx, None);
    t[0x0b] = e("pmulhrsw", Vx, Wx, None);
    t[0x10] = e("pblendvb", Vx, Wx, XMM0);
    t[0x14] = e("blendvps", Vx, Wx, XMM0);
    t[0x15] = e("blendvpd", Vx, Wx, XMM0);
    t[0x17] = e("ptest", Vx, Wx, None);
    t[0x1c] = e("pabsb", Vx, Wx, None);
    t[0x1d] = e("pabsw", Vx, Wx, None);
    t[0x1e] = e("pabsd", Vx, Wx, None);
    t[0x20] = es("pmovsxbw", Vx, Wx, None, 8);
    t[0x21] = es("pmovsxbd", Vx, Wx, None, 4);
    t[0x23] = es("pmovsxwd", Vx, Wx, None, 8);
    t[0x25] = es("pmovsxdq", Vx, Wx, None, 8);
    t[0x28] = e("pmuldq", Vx, Wx, None);
    t[0x29] = e("pcmpeqq", Vx, Wx, None);
    t[0x2b] = e("packusdw", Vx, Wx, None);
    t[0x30] = es("pmovzxbw", Vx, Wx, None, 8);
    t[0x31] = es("pmovzxbd", Vx, Wx, None, 4);
    t[0x33] = es("pmovzxwd", Vx, Wx, None, 8);
    t[0x35] = es("pmovzxdq", Vx, Wx, None, 8);
    t[0x37] = e("pcmpgtq", Vx, Wx, None);
    t[0x38] = e("pminsb", Vx, Wx, None);
    t[0x39] = e("pminsd", Vx, Wx, None);
    t[0x3a] = e("pminuw", Vx, Wx, None);
    t[0x3b] = e("pminud", Vx, Wx, None);
    t[0x3c] = e("pmaxsb", Vx, Wx, None);
    t[0x3d] = e("pmaxsd", Vx, Wx, None);
    t[0x3e] = e("pmaxuw", Vx, Wx, None);
    t[0x3f] = e("pmaxud", Vx, Wx, None);
    t[0x40] = e("pmulld", Vx, Wx, None);
    t[0x41] = e("phminposuw", Vx, Wx, None);
    t
};

/// The `0x0f 0x38` map with no prefix, which is the MMX half of SSSE3.
pub const THREE_BYTE_38: [Entry; 256] = {
    let mut t = [BAD; 256];
    t[0x00] = es("pshufb", Pq, Qq, None, 8);
    t[0x01] = es("phaddw", Pq, Qq, None, 8);
    t[0x02] = es("phaddd", Pq, Qq, None, 8);
    t[0x03] = es("phaddsw", Pq, Qq, None, 8);
    t[0x04] = es("pmaddubsw", Pq, Qq, None, 8);
    t[0x05] = es("phsubw", Pq, Qq, None, 8);
    t[0x06] = es("phsubd", Pq, Qq, None, 8);
    t[0x07] = es("phsubsw", Pq, Qq, None, 8);
    t[0x08] = es("psignb", Pq, Qq, None, 8);
    t[0x09] = es("psignw", Pq, Qq, None, 8);
    t[0x0a] = es("psignd", Pq, Qq, None, 8);
    t[0x0b] = es("pmulhrsw", Pq, Qq, None, 8);
    t[0x1c] = es("pabsb", Pq, Qq, None, 8);
    t[0x1d] = es("pabsw", Pq, Qq, None, 8);
    t[0x1e] = es("pabsd", Pq, Qq, None, 8);
    t
};

/// The `0x0f 0x3a` map with no prefix, which holds one MMX instruction.
pub const THREE_BYTE_3A: [Entry; 256] = {
    let mut t = [BAD; 256];
    t[0x0f] = es("palignr", Pq, Qq, Ibu, 8);
    t
};

/// The `0x0f 0x3a` map with a mandatory `0x66`.
pub const THREE_BYTE_3A_66: [Entry; 256] = {
    let mut t = [BAD; 256];
    t[0x0b] = es("roundsd", Vx, Wx, Ibu, 8);
    t[0x0a] = es("roundss", Vx, Wx, Ibu, 4);
    t[0x08] = e("roundps", Vx, Wx, Ibu);
    t[0x09] = e("roundpd", Vx, Wx, Ibu);
    t[0x0e] = e("pblendw", Vx, Wx, Ibu);
    t[0x0f] = e("palignr", Vx, Wx, Ibu);
    t[0x14] = e("pextrb", Ebm, Vx, Ibu);
    t[0x15] = e("pextrw", Ewm, Vx, Ibu);
    t[0x16] = e("pextrd", Ev, Vx, Ibu);
    t[0x17] = es("extractps", Ed, Vx, Ibu, 4);
    t[0x20] = e("pinsrb", Vx, Ebm, Ibu);
    t[0x21] = es("insertps", Vx, Wx, Ibu, 4);
    t[0x22] = e("pinsrd", Vx, Ev, Ibu);
    t[0x60] = e("pcmpestrm", Vx, Wx, Ibu);
    t[0x61] = e("pcmpestri", Vx, Wx, Ibu);
    t[0x62] = e("pcmpistrm", Vx, Wx, Ibu);
    t[0x63] = e("pcmpistri", Vx, Wx, Ibu);
    t
};

/// The comparison predicate that the immediate of `cmpps` and friends selects.
pub const CMP_PRED: [&str; 8] = ["eq", "lt", "le", "unord", "neq", "nlt", "nle", "ord"];

/// The memory forms of the x87 escapes, indexed by opcode minus 0xd8 and then
/// by the ModRM reg field, as the mnemonic and the size in bytes it touches.
/// A size of zero is the environment and state blocks, which llvm prints with
/// no size hint because they have no scalar width.
pub const X87_MEM: [[(&str, u8); 8]; 8] = [
    // 0xd8: single precision arithmetic.
    [
        ("fadd", 4),
        ("fmul", 4),
        ("fcom", 4),
        ("fcomp", 4),
        ("fsub", 4),
        ("fsubr", 4),
        ("fdiv", 4),
        ("fdivr", 4),
    ],
    // 0xd9: single precision load and store, and the control word.
    [
        ("fld", 4),
        ("", 0),
        ("fst", 4),
        ("fstp", 4),
        ("fldenv", 0),
        ("fldcw", 2),
        ("fnstenv", 0),
        ("fnstcw", 2),
    ],
    // 0xda: doubleword integer arithmetic.
    [
        ("fiadd", 4),
        ("fimul", 4),
        ("ficom", 4),
        ("ficomp", 4),
        ("fisub", 4),
        ("fisubr", 4),
        ("fidiv", 4),
        ("fidivr", 4),
    ],
    // 0xdb: doubleword integer transfers, and the 80-bit load and store.
    [
        ("fild", 4),
        ("fisttp", 4),
        ("fist", 4),
        ("fistp", 4),
        ("", 0),
        ("fld", 10),
        ("", 0),
        ("fstp", 10),
    ],
    // 0xdc: double precision arithmetic.
    [
        ("fadd", 8),
        ("fmul", 8),
        ("fcom", 8),
        ("fcomp", 8),
        ("fsub", 8),
        ("fsubr", 8),
        ("fdiv", 8),
        ("fdivr", 8),
    ],
    // 0xdd: double precision transfers, and the whole machine state.
    [
        ("fld", 8),
        ("fisttp", 8),
        ("fst", 8),
        ("fstp", 8),
        ("frstor", 0),
        ("", 0),
        ("fnsave", 0),
        ("fnstsw", 2),
    ],
    // 0xde: word integer arithmetic.
    [
        ("fiadd", 2),
        ("fimul", 2),
        ("ficom", 2),
        ("ficomp", 2),
        ("fisub", 2),
        ("fisubr", 2),
        ("fidiv", 2),
        ("fidivr", 2),
    ],
    // 0xdf: word integer transfers, the packed decimal pair, and int64.
    [
        ("fild", 2),
        ("fisttp", 2),
        ("fist", 2),
        ("fistp", 2),
        ("fbld", 10),
        ("fild", 8),
        ("fbstp", 10),
        ("fistp", 8),
    ],
];

/// `0xd9` with a ModRM byte of 0xe0 or above: no operands, and no pattern
/// either, so this is a plain list indexed by the low five bits.
pub const X87_D9_E0: [&str; 32] = [
    "fchs", "fabs", "", "", "ftst", "fxam", "", "", "fld1", "fldl2t", "fldl2e", "fldpi", "fldlg2",
    "fldln2", "fldz", "", "f2xm1", "fyl2x", "fptan", "fpatan", "fxtract", "fprem1", "fdecstp",
    "fincstp", "fprem", "fyl2xp1", "fsqrt", "fsincos", "frndint", "fscale", "fsin", "fcos",
];

/// `0xd8` register forms, by ModRM reg. `fcom` and `fcomp` take one operand;
/// the rest take `st` and a stack register.
pub const X87_D8_REG: [&str; 8] = [
    "fadd", "fmul", "fcom", "fcomp", "fsub", "fsubr", "fdiv", "fdivr",
];

/// `0xdc` register forms, by ModRM reg. The subtract and divide pairs are
/// swapped against the memory forms, which is the architecture's own quirk.
pub const X87_DC_REG: [&str; 8] = ["fadd", "fmul", "", "", "fsubr", "fsub", "fdivr", "fdiv"];

/// `0xdd` register forms, by ModRM reg. Each takes one stack register.
pub const X87_DD_REG: [&str; 8] = ["ffree", "", "fst", "fstp", "fucom", "fucomp", "", ""];

/// `0xde` register forms, by ModRM reg, with the same swap as `0xdc`.
pub const X87_DE_REG: [&str; 8] = [
    "faddp", "fmulp", "", "", "fsubrp", "fsubp", "fdivrp", "fdivp",
];

/// The conditional moves at `0xda` and `0xdb`, by the ModRM reg field.
pub const X87_FCMOV: [&str; 4] = ["b", "e", "be", "u"];
