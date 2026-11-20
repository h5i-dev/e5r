//! The nocompiler instruction set, decoded from 32-bit words.
//!
//! This is a second, independent implementation of `lean/NoCompiler/Isa.lean`'s
//! `decode`. Nothing a proof relies on comes from here: the Lean exporter
//! writes the raw words, and each `instr_<addr>` lemma it emits is checked by
//! the Lean kernel evaluating the Lean decoder. The two decoders, and
//! llvm-mc, are compared by `tests/decode.rs`.

use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Reg(pub u8);

pub const ZERO: Reg = Reg(0);
pub const RA: Reg = Reg(1);
pub const SP: Reg = Reg(2);
pub const GP: Reg = Reg(3);
pub const TP: Reg = Reg(4);
pub const T1: Reg = Reg(6);

const ABI: [&str; 32] = [
    "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1", "a0", "a1", "a2", "a3", "a4",
    "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4",
    "t5", "t6",
];

impl fmt::Display for Reg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(ABI[self.0 as usize])
    }
}

macro_rules! ops {
    ($name:ident { $($v:ident = $s:literal),* $(,)? }) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum $name { $($v),* }
        impl $name {
            /// The assembler mnemonic.
            pub fn mnemonic(self) -> &'static str { match self { $($name::$v => $s),* } }
            /// The constructor name in `lean/NoCompiler/Isa.lean`.
            pub fn lean(self) -> &'static str {
                match self { $($name::$v => lean_name(stringify!($v))),* }
            }
        }
    };
}

/// `Sh1adduw` -> `sh1adduw`: the Lean constructors are the lowercased variants.
fn lean_name(v: &'static str) -> &'static str {
    // A fixed table so the result is 'static without allocation.
    match v {
        "Beq" => "beq",
        "Bne" => "bne",
        "Blt" => "blt",
        "Bge" => "bge",
        "Bltu" => "bltu",
        "Bgeu" => "bgeu",
        "Lb" => "lb",
        "Lh" => "lh",
        "Lw" => "lw",
        "Ld" => "ld",
        "Lbu" => "lbu",
        "Lhu" => "lhu",
        "Lwu" => "lwu",
        "Sb" => "sb",
        "Sh" => "sh",
        "Sw" => "sw",
        "Sd" => "sd",
        "Addi" => "addi",
        "Slti" => "slti",
        "Sltiu" => "sltiu",
        "Xori" => "xori",
        "Ori" => "ori",
        "Andi" => "andi",
        "Slli" => "slli",
        "Srli" => "srli",
        "Srai" => "srai",
        "Rori" => "rori",
        "Slliuw" => "slliuw",
        "Slliw" => "slliw",
        "Srliw" => "srliw",
        "Sraiw" => "sraiw",
        "Roriw" => "roriw",
        "Add" => "add",
        "Sub" => "sub",
        "Sll" => "sll",
        "Slt" => "slt",
        "Sltu" => "sltu",
        "Xor" => "xor",
        "Srl" => "srl",
        "Sra" => "sra",
        "Or" => "or",
        "And" => "and",
        "Mul" => "mul",
        "Mulh" => "mulh",
        "Mulhsu" => "mulhsu",
        "Mulhu" => "mulhu",
        "Div" => "div",
        "Divu" => "divu",
        "Rem" => "rem",
        "Remu" => "remu",
        "Sh1add" => "sh1add",
        "Sh2add" => "sh2add",
        "Sh3add" => "sh3add",
        "Andn" => "andn",
        "Orn" => "orn",
        "Xnor" => "xnor",
        "Max" => "max",
        "Maxu" => "maxu",
        "Min" => "min",
        "Minu" => "minu",
        "Rol" => "rol",
        "Ror" => "ror",
        "Addw" => "addw",
        "Subw" => "subw",
        "Sllw" => "sllw",
        "Srlw" => "srlw",
        "Sraw" => "sraw",
        "Mulw" => "mulw",
        "Divw" => "divw",
        "Divuw" => "divuw",
        "Remw" => "remw",
        "Remuw" => "remuw",
        "Adduw" => "adduw",
        "Sh1adduw" => "sh1adduw",
        "Sh2adduw" => "sh2adduw",
        "Sh3adduw" => "sh3adduw",
        "Rolw" => "rolw",
        "Rorw" => "rorw",
        "Clz" => "clz",
        "Ctz" => "ctz",
        "Cpop" => "cpop",
        "Clzw" => "clzw",
        "Ctzw" => "ctzw",
        "Cpopw" => "cpopw",
        "Sextb" => "sextb",
        "Sexth" => "sexth",
        "Zexth" => "zexth",
        "Rev8" => "rev8",
        "Orcb" => "orcb",
        _ => unreachable!("every variant is listed"),
    }
}

ops!(BrOp { Beq = "beq", Bne = "bne", Blt = "blt", Bge = "bge", Bltu = "bltu", Bgeu = "bgeu" });
ops!(LdOp { Lb = "lb", Lh = "lh", Lw = "lw", Ld = "ld", Lbu = "lbu", Lhu = "lhu", Lwu = "lwu" });
ops!(StOp { Sb = "sb", Sh = "sh", Sw = "sw", Sd = "sd" });
ops!(IOp { Addi = "addi", Slti = "slti", Sltiu = "sltiu", Xori = "xori", Ori = "ori", Andi = "andi" });
ops!(ShOp { Slli = "slli", Srli = "srli", Srai = "srai", Rori = "rori", Slliuw = "slli.uw" });
ops!(ShWOp { Slliw = "slliw", Srliw = "srliw", Sraiw = "sraiw", Roriw = "roriw" });
ops!(ROp {
    Add = "add", Sub = "sub", Sll = "sll", Slt = "slt", Sltu = "sltu", Xor = "xor", Srl = "srl",
    Sra = "sra", Or = "or", And = "and", Mul = "mul", Mulh = "mulh", Mulhsu = "mulhsu",
    Mulhu = "mulhu", Div = "div", Divu = "divu", Rem = "rem", Remu = "remu", Sh1add = "sh1add",
    Sh2add = "sh2add", Sh3add = "sh3add", Andn = "andn", Orn = "orn", Xnor = "xnor", Max = "max",
    Maxu = "maxu", Min = "min", Minu = "minu", Rol = "rol", Ror = "ror",
});
ops!(RWOp {
    Addw = "addw", Subw = "subw", Sllw = "sllw", Srlw = "srlw", Sraw = "sraw", Mulw = "mulw",
    Divw = "divw", Divuw = "divuw", Remw = "remw", Remuw = "remuw", Adduw = "add.uw",
    Sh1adduw = "sh1add.uw", Sh2adduw = "sh2add.uw", Sh3adduw = "sh3add.uw", Rolw = "rolw",
    Rorw = "rorw",
});
ops!(UOp {
    Clz = "clz", Ctz = "ctz", Cpop = "cpop", Clzw = "clzw", Ctzw = "ctzw", Cpopw = "cpopw",
    Sextb = "sext.b", Sexth = "sext.h", Zexth = "zext.h", Rev8 = "rev8", Orcb = "orc.b",
});

impl LdOp {
    pub fn width(self) -> u64 {
        match self {
            LdOp::Lb | LdOp::Lbu => 1,
            LdOp::Lh | LdOp::Lhu => 2,
            LdOp::Lw | LdOp::Lwu => 4,
            LdOp::Ld => 8,
        }
    }
}

impl StOp {
    pub fn width(self) -> u64 {
        match self {
            StOp::Sb => 1,
            StOp::Sh => 2,
            StOp::Sw => 4,
            StOp::Sd => 8,
        }
    }
}

/// Immediates are stored as they appear in the encoding: `bits` wide,
/// unsigned. `signed()` gives the sign-extended value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Imm {
    pub value: u32,
    pub bits: u8,
}

impl Imm {
    pub fn signed(self) -> i64 {
        let v = self.value as i64;
        if v & (1 << (self.bits - 1)) != 0 {
            v - (1 << self.bits)
        } else {
            v
        }
    }
    /// The Lean literal, e.g. `0x018#13`.
    pub fn lean(self) -> String {
        format!(
            "0x{:0w$x}#{}",
            self.value,
            self.bits,
            w = (self.bits as usize).div_ceil(4)
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Instr {
    Lui(Reg, Imm),
    Auipc(Reg, Imm),
    Jal(Reg, Imm),
    Jalr(Reg, Reg, Imm),
    Branch(BrOp, Reg, Reg, Imm),
    Load(LdOp, Reg, Reg, Imm),
    Store(StOp, Reg, Reg, Imm),
    IOp(IOp, Reg, Reg, Imm),
    Addiw(Reg, Reg, Imm),
    Shift(ShOp, Reg, Reg, Imm),
    ShiftW(ShWOp, Reg, Reg, Imm),
    ROp(ROp, Reg, Reg, Reg),
    RWOp(RWOp, Reg, Reg, Reg),
    UOp(UOp, Reg, Reg),
    Ecall,
}

fn bits(w: u32, lo: u32, len: u32) -> u32 {
    (w >> lo) & ((1u32 << len) - 1)
}

fn reg(w: u32, lo: u32) -> Reg {
    Reg(bits(w, lo, 5) as u8)
}

fn imm(value: u32, bits: u8) -> Imm {
    Imm { value, bits }
}

fn imm_i(w: u32) -> Imm {
    imm(bits(w, 20, 12), 12)
}
fn imm_s(w: u32) -> Imm {
    imm(bits(w, 7, 5) | bits(w, 25, 7) << 5, 12)
}
fn imm_b(w: u32) -> Imm {
    imm(
        bits(w, 8, 4) << 1 | bits(w, 25, 6) << 5 | bits(w, 7, 1) << 11 | bits(w, 31, 1) << 12,
        13,
    )
}
fn imm_u(w: u32) -> Imm {
    imm(bits(w, 12, 20), 20)
}
fn imm_j(w: u32) -> Imm {
    imm(
        bits(w, 21, 10) << 1 | bits(w, 20, 1) << 11 | bits(w, 12, 8) << 12 | bits(w, 31, 1) << 20,
        21,
    )
}

fn decode_r(f7: u32, f3: u32) -> Option<ROp> {
    use ROp::*;
    Some(match (f7, f3) {
        (0x00, 0) => Add,
        (0x20, 0) => Sub,
        (0x00, 1) => Sll,
        (0x00, 2) => Slt,
        (0x00, 3) => Sltu,
        (0x00, 4) => Xor,
        (0x00, 5) => Srl,
        (0x20, 5) => Sra,
        (0x00, 6) => Or,
        (0x00, 7) => And,
        (0x01, 0) => Mul,
        (0x01, 1) => Mulh,
        (0x01, 2) => Mulhsu,
        (0x01, 3) => Mulhu,
        (0x01, 4) => Div,
        (0x01, 5) => Divu,
        (0x01, 6) => Rem,
        (0x01, 7) => Remu,
        (0x10, 2) => Sh1add,
        (0x10, 4) => Sh2add,
        (0x10, 6) => Sh3add,
        (0x20, 7) => Andn,
        (0x20, 6) => Orn,
        (0x20, 4) => Xnor,
        (0x05, 6) => Max,
        (0x05, 7) => Maxu,
        (0x05, 4) => Min,
        (0x05, 5) => Minu,
        (0x30, 1) => Rol,
        (0x30, 5) => Ror,
        _ => return None,
    })
}

fn decode_rw(f7: u32, f3: u32) -> Option<RWOp> {
    use RWOp::*;
    Some(match (f7, f3) {
        (0x00, 0) => Addw,
        (0x20, 0) => Subw,
        (0x00, 1) => Sllw,
        (0x00, 5) => Srlw,
        (0x20, 5) => Sraw,
        (0x01, 0) => Mulw,
        (0x01, 4) => Divw,
        (0x01, 5) => Divuw,
        (0x01, 6) => Remw,
        (0x01, 7) => Remuw,
        (0x04, 0) => Adduw,
        (0x10, 2) => Sh1adduw,
        (0x10, 4) => Sh2adduw,
        (0x10, 6) => Sh3adduw,
        (0x30, 1) => Rolw,
        (0x30, 5) => Rorw,
        _ => return None,
    })
}

/// Decode one instruction word; `None` for anything outside the profile.
pub fn decode(w: u32) -> Option<Instr> {
    let opc = bits(w, 0, 7);
    let rd = reg(w, 7);
    let f3 = bits(w, 12, 3);
    let rs1 = reg(w, 15);
    let rs2 = reg(w, 20);
    let f7 = bits(w, 25, 7);
    let imm12 = bits(w, 20, 12);
    Some(match opc {
        0x37 => Instr::Lui(rd, imm_u(w)),
        0x17 => Instr::Auipc(rd, imm_u(w)),
        0x6f => Instr::Jal(rd, imm_j(w)),
        0x67 if f3 == 0 => Instr::Jalr(rd, rs1, imm_i(w)),
        0x63 => {
            let op = match f3 {
                0 => BrOp::Beq,
                1 => BrOp::Bne,
                4 => BrOp::Blt,
                5 => BrOp::Bge,
                6 => BrOp::Bltu,
                7 => BrOp::Bgeu,
                _ => return None,
            };
            Instr::Branch(op, rs1, rs2, imm_b(w))
        }
        0x03 => {
            let op = match f3 {
                0 => LdOp::Lb,
                1 => LdOp::Lh,
                2 => LdOp::Lw,
                3 => LdOp::Ld,
                4 => LdOp::Lbu,
                5 => LdOp::Lhu,
                6 => LdOp::Lwu,
                _ => return None,
            };
            Instr::Load(op, rd, rs1, imm_i(w))
        }
        0x23 => {
            let op = match f3 {
                0 => StOp::Sb,
                1 => StOp::Sh,
                2 => StOp::Sw,
                3 => StOp::Sd,
                _ => return None,
            };
            Instr::Store(op, rs1, rs2, imm_s(w))
        }
        0x13 => {
            let sh = imm(bits(w, 20, 6), 6);
            let top6 = bits(w, 26, 6);
            match f3 {
                0 => Instr::IOp(IOp::Addi, rd, rs1, imm_i(w)),
                2 => Instr::IOp(IOp::Slti, rd, rs1, imm_i(w)),
                3 => Instr::IOp(IOp::Sltiu, rd, rs1, imm_i(w)),
                4 => Instr::IOp(IOp::Xori, rd, rs1, imm_i(w)),
                6 => Instr::IOp(IOp::Ori, rd, rs1, imm_i(w)),
                7 => Instr::IOp(IOp::Andi, rd, rs1, imm_i(w)),
                1 => match (top6, imm12) {
                    (0x00, _) => Instr::Shift(ShOp::Slli, rd, rs1, sh),
                    (_, 0x600) => Instr::UOp(UOp::Clz, rd, rs1),
                    (_, 0x601) => Instr::UOp(UOp::Ctz, rd, rs1),
                    (_, 0x602) => Instr::UOp(UOp::Cpop, rd, rs1),
                    (_, 0x604) => Instr::UOp(UOp::Sextb, rd, rs1),
                    (_, 0x605) => Instr::UOp(UOp::Sexth, rd, rs1),
                    _ => return None,
                },
                5 => match (top6, imm12) {
                    (0x00, _) => Instr::Shift(ShOp::Srli, rd, rs1, sh),
                    (0x10, _) => Instr::Shift(ShOp::Srai, rd, rs1, sh),
                    (0x18, _) => Instr::Shift(ShOp::Rori, rd, rs1, sh),
                    (_, 0x6b8) => Instr::UOp(UOp::Rev8, rd, rs1),
                    (_, 0x287) => Instr::UOp(UOp::Orcb, rd, rs1),
                    _ => return None,
                },
                _ => return None,
            }
        }
        0x1b => {
            let sh = imm(bits(w, 20, 5), 5);
            match f3 {
                0 => Instr::Addiw(rd, rs1, imm_i(w)),
                1 => {
                    if f7 == 0x00 {
                        Instr::ShiftW(ShWOp::Slliw, rd, rs1, sh)
                    } else if bits(w, 26, 6) == 0x02 {
                        Instr::Shift(ShOp::Slliuw, rd, rs1, imm(bits(w, 20, 6), 6))
                    } else {
                        match imm12 {
                            0x600 => Instr::UOp(UOp::Clzw, rd, rs1),
                            0x601 => Instr::UOp(UOp::Ctzw, rd, rs1),
                            0x602 => Instr::UOp(UOp::Cpopw, rd, rs1),
                            _ => return None,
                        }
                    }
                }
                5 => match f7 {
                    0x00 => Instr::ShiftW(ShWOp::Srliw, rd, rs1, sh),
                    0x20 => Instr::ShiftW(ShWOp::Sraiw, rd, rs1, sh),
                    0x30 => Instr::ShiftW(ShWOp::Roriw, rd, rs1, sh),
                    _ => return None,
                },
                _ => return None,
            }
        }
        0x33 => Instr::ROp(decode_r(f7, f3)?, rd, rs1, rs2),
        0x3b => {
            if f7 == 0x04 && f3 == 4 && bits(w, 20, 5) == 0 {
                Instr::UOp(UOp::Zexth, rd, rs1)
            } else {
                Instr::RWOp(decode_rw(f7, f3)?, rd, rs1, rs2)
            }
        }
        0x73 if w == 0x0000_0073 => Instr::Ecall,
        _ => return None,
    })
}

impl Instr {
    /// The register this instruction writes, if any (x0 counts as none).
    pub fn dest(&self) -> Option<Reg> {
        let rd = match *self {
            Instr::Lui(rd, _) | Instr::Auipc(rd, _) | Instr::Jal(rd, _) | Instr::Jalr(rd, _, _) => {
                rd
            }
            Instr::Load(_, rd, _, _)
            | Instr::IOp(_, rd, _, _)
            | Instr::Addiw(rd, _, _)
            | Instr::Shift(_, rd, _, _)
            | Instr::ShiftW(_, rd, _, _)
            | Instr::ROp(_, rd, _, _)
            | Instr::RWOp(_, rd, _, _)
            | Instr::UOp(_, rd, _) => rd,
            // ECALL writes a0 (the result), which is never sp, gp, tp or ra.
            Instr::Ecall => Reg(10),
            Instr::Branch(..) | Instr::Store(..) => return None,
        };
        (rd != ZERO).then_some(rd)
    }

    /// The registers this instruction reads (x0 included when named).
    pub fn srcs(&self) -> Vec<Reg> {
        match *self {
            Instr::Lui(..) | Instr::Auipc(..) | Instr::Jal(..) | Instr::Ecall => vec![],
            Instr::Jalr(_, rs1, _)
            | Instr::Load(_, _, rs1, _)
            | Instr::IOp(_, _, rs1, _)
            | Instr::Addiw(_, rs1, _)
            | Instr::Shift(_, _, rs1, _)
            | Instr::ShiftW(_, _, rs1, _)
            | Instr::UOp(_, _, rs1) => vec![rs1],
            Instr::Branch(_, a, b, _) | Instr::Store(_, a, b, _) => vec![a, b],
            Instr::ROp(_, _, a, b) | Instr::RWOp(_, _, a, b) => vec![a, b],
        }
    }

    /// The term `lean/NoCompiler/Isa.lean` writes for this instruction.
    pub fn lean(&self) -> String {
        match *self {
            Instr::Lui(rd, i) => format!(".lui {} {}", rd.0, i.lean()),
            Instr::Auipc(rd, i) => format!(".auipc {} {}", rd.0, i.lean()),
            Instr::Jal(rd, i) => format!(".jal {} {}", rd.0, i.lean()),
            Instr::Jalr(rd, rs1, i) => format!(".jalr {} {} {}", rd.0, rs1.0, i.lean()),
            Instr::Branch(op, a, b, i) => {
                format!(".branch .{} {} {} {}", op.lean(), a.0, b.0, i.lean())
            }
            Instr::Load(op, rd, rs1, i) => {
                format!(".load .{} {} {} {}", op.lean(), rd.0, rs1.0, i.lean())
            }
            Instr::Store(op, a, b, i) => {
                format!(".store .{} {} {} {}", op.lean(), a.0, b.0, i.lean())
            }
            Instr::IOp(op, rd, rs1, i) => {
                format!(".iop .{} {} {} {}", op.lean(), rd.0, rs1.0, i.lean())
            }
            Instr::Addiw(rd, rs1, i) => format!(".addiw {} {} {}", rd.0, rs1.0, i.lean()),
            Instr::Shift(op, rd, rs1, i) => {
                format!(".shift .{} {} {} {}", op.lean(), rd.0, rs1.0, i.lean())
            }
            Instr::ShiftW(op, rd, rs1, i) => {
                format!(".shiftw .{} {} {} {}", op.lean(), rd.0, rs1.0, i.lean())
            }
            Instr::ROp(op, rd, a, b) => format!(".rop .{} {} {} {}", op.lean(), rd.0, a.0, b.0),
            Instr::RWOp(op, rd, a, b) => format!(".rwop .{} {} {} {}", op.lean(), rd.0, a.0, b.0),
            Instr::UOp(op, rd, rs1) => format!(".uop .{} {} {}", op.lean(), rd.0, rs1.0),
            Instr::Ecall => ".ecall".into(),
        }
    }

    /// Assembly in llvm-objdump's `-M no-aliases` syntax, with branch and jump
    /// targets as absolute addresses (given the instruction's address).
    pub fn asm(&self, pc: u64) -> String {
        self.fmt_asm(|i| format!("0x{:x}", pc.wrapping_add(i.signed() as u64)))
    }

    /// The same, with branch and jump offsets as signed decimals: what
    /// `llvm-mc --disassemble -M no-aliases` prints.
    pub fn asm_rel(&self) -> String {
        self.fmt_asm(|i| i.signed().to_string())
    }

    fn fmt_asm(&self, tgt: impl Fn(Imm) -> String) -> String {
        match *self {
            Instr::Lui(rd, i) => format!("lui {rd}, {}", i.value),
            Instr::Auipc(rd, i) => format!("auipc {rd}, {}", i.value),
            Instr::Jal(rd, i) => format!("jal {rd}, {}", tgt(i)),
            Instr::Jalr(rd, rs1, i) => format!("jalr {rd}, {}({rs1})", i.signed()),
            Instr::Branch(op, a, b, i) => format!("{} {a}, {b}, {}", op.mnemonic(), tgt(i)),
            Instr::Load(op, rd, rs1, i) => format!("{} {rd}, {}({rs1})", op.mnemonic(), i.signed()),
            Instr::Store(op, a, b, i) => format!("{} {b}, {}({a})", op.mnemonic(), i.signed()),
            Instr::IOp(op, rd, rs1, i) => format!("{} {rd}, {rs1}, {}", op.mnemonic(), i.signed()),
            Instr::Addiw(rd, rs1, i) => format!("addiw {rd}, {rs1}, {}", i.signed()),
            Instr::Shift(op, rd, rs1, i) => format!("{} {rd}, {rs1}, {}", op.mnemonic(), i.value),
            Instr::ShiftW(op, rd, rs1, i) => format!("{} {rd}, {rs1}, {}", op.mnemonic(), i.value),
            Instr::ROp(op, rd, a, b) => format!("{} {rd}, {a}, {b}", op.mnemonic()),
            Instr::RWOp(op, rd, a, b) => format!("{} {rd}, {a}, {b}", op.mnemonic()),
            Instr::UOp(op, rd, rs1) => format!("{} {rd}, {rs1}", op.mnemonic()),
            Instr::Ecall => "ecall".into(),
        }
    }
}
