/-
nocompiler instruction set: the RV64IM + Zba + Zbb subset the profile admits
(docs/isa/profile.md, section 2), as an abstract syntax with a decoder from
the 32-bit instruction word and an encoder back.

The decoder is part of the trusted base: it is what turns the bytes of a
binary into the instructions a proof talks about. It is checked against
llvm-objdump and against the Rust decoder (crates/nocompiler) by the
differential tests, and `decode_encode` below proves the two directions of
this file agree.

Not in the profile, so `decode` returns `none` for them and a proof can never
step over one: the C extension (16-bit encodings), CSR instructions, FENCE,
FENCE.I, EBREAK, the A, F, D and V extensions, and every reserved encoding.
-/
namespace NoCompiler

abbrev Word := BitVec 64
abbrev Byte := BitVec 8

/-- An integer register index, x0 to x31. -/
abbrev Reg := Fin 32

namespace Reg
abbrev zero : Reg := 0
abbrev ra : Reg := 1
abbrev sp : Reg := 2
abbrev gp : Reg := 3
abbrev tp : Reg := 4
abbrev t0 : Reg := 5
abbrev t1 : Reg := 6
abbrev t2 : Reg := 7
abbrev s0 : Reg := 8
abbrev s1 : Reg := 9
abbrev a0 : Reg := 10
abbrev a1 : Reg := 11
abbrev a2 : Reg := 12
abbrev a3 : Reg := 13
abbrev a4 : Reg := 14
abbrev a5 : Reg := 15
abbrev a6 : Reg := 16
abbrev a7 : Reg := 17
abbrev t3 : Reg := 28
end Reg

inductive BrOp | beq | bne | blt | bge | bltu | bgeu
  deriving DecidableEq, Repr

inductive LdOp | lb | lh | lw | ld | lbu | lhu | lwu
  deriving DecidableEq, Repr

inductive StOp | sb | sh | sw | sd
  deriving DecidableEq, Repr

/-- Register-immediate operations with a 12-bit immediate. -/
inductive IOp | addi | slti | sltiu | xori | ori | andi
  deriving DecidableEq, Repr

/-- Shifts and rotates by a 6-bit immediate (RV64), plus Zba `slli.uw`. -/
inductive ShOp | slli | srli | srai | rori | slliuw
  deriving DecidableEq, Repr

/-- 32-bit shifts and rotates by a 5-bit immediate. -/
inductive ShWOp | slliw | srliw | sraiw | roriw
  deriving DecidableEq, Repr

/-- Register-register operations on 64 bits: base, M, Zba and Zbb. -/
inductive ROp
  | add | sub | sll | slt | sltu | xor | srl | sra | or | and
  | mul | mulh | mulhsu | mulhu | div | divu | rem | remu
  | sh1add | sh2add | sh3add
  | andn | orn | xnor | max | maxu | min | minu | rol | ror
  deriving DecidableEq, Repr

/-- Register-register operations on the low 32 bits, sign-extended result
    (except the Zba `.uw` forms, which zero-extend their first operand). -/
inductive RWOp
  | addw | subw | sllw | srlw | sraw
  | mulw | divw | divuw | remw | remuw
  | adduw | sh1adduw | sh2adduw | sh3adduw
  | rolw | rorw
  deriving DecidableEq, Repr

/-- One-operand Zbb operations. -/
inductive UOp
  | clz | ctz | cpop | clzw | ctzw | cpopw
  | sextb | sexth | zexth | rev8 | orcb
  deriving DecidableEq, Repr

inductive Instr
  | lui (rd : Reg) (imm : BitVec 20)
  | auipc (rd : Reg) (imm : BitVec 20)
  | jal (rd : Reg) (off : BitVec 21)
  | jalr (rd rs1 : Reg) (off : BitVec 12)
  | branch (op : BrOp) (rs1 rs2 : Reg) (off : BitVec 13)
  | load (op : LdOp) (rd rs1 : Reg) (off : BitVec 12)
  | store (op : StOp) (rs1 rs2 : Reg) (off : BitVec 12)
  | iop (op : IOp) (rd rs1 : Reg) (imm : BitVec 12)
  | addiw (rd rs1 : Reg) (imm : BitVec 12)
  | shift (op : ShOp) (rd rs1 : Reg) (shamt : BitVec 6)
  | shiftw (op : ShWOp) (rd rs1 : Reg) (shamt : BitVec 5)
  | rop (op : ROp) (rd rs1 rs2 : Reg)
  | rwop (op : RWOp) (rd rs1 rs2 : Reg)
  | uop (op : UOp) (rd rs1 : Reg)
  | ecall
  deriving DecidableEq, Repr

/-! ## Decoding -/

/-- Bits `lo .. lo+len-1` of an instruction word, as a natural number. -/
@[inline] def bits (w : BitVec 32) (lo len : Nat) : Nat := (w.toNat >>> lo) % 2 ^ len

@[inline] def regAt (w : BitVec 32) (lo : Nat) : Reg := ⟨bits w lo 5, Nat.mod_lt _ (by decide)⟩

def immI (w : BitVec 32) : BitVec 12 := BitVec.ofNat 12 (bits w 20 12)
def immS (w : BitVec 32) : BitVec 12 := BitVec.ofNat 12 (bits w 7 5 + bits w 25 7 * 32)
def immB (w : BitVec 32) : BitVec 13 :=
  BitVec.ofNat 13 (bits w 8 4 * 2 + bits w 25 6 * 32 + bits w 7 1 * 2048 + bits w 31 1 * 4096)
def immU (w : BitVec 32) : BitVec 20 := BitVec.ofNat 20 (bits w 12 20)
def immJ (w : BitVec 32) : BitVec 21 :=
  BitVec.ofNat 21 (bits w 21 10 * 2 + bits w 20 1 * 2048 + bits w 12 8 * 4096 + bits w 31 1 * 1048576)

def decodeR (f7 f3 : Nat) : Option ROp :=
  match f7, f3 with
  | 0x00, 0 => some .add  | 0x20, 0 => some .sub
  | 0x00, 1 => some .sll  | 0x00, 2 => some .slt
  | 0x00, 3 => some .sltu | 0x00, 4 => some .xor
  | 0x00, 5 => some .srl  | 0x20, 5 => some .sra
  | 0x00, 6 => some .or   | 0x00, 7 => some .and
  | 0x01, 0 => some .mul  | 0x01, 1 => some .mulh
  | 0x01, 2 => some .mulhsu | 0x01, 3 => some .mulhu
  | 0x01, 4 => some .div  | 0x01, 5 => some .divu
  | 0x01, 6 => some .rem  | 0x01, 7 => some .remu
  | 0x10, 2 => some .sh1add | 0x10, 4 => some .sh2add | 0x10, 6 => some .sh3add
  | 0x20, 7 => some .andn | 0x20, 6 => some .orn | 0x20, 4 => some .xnor
  | 0x05, 6 => some .max  | 0x05, 7 => some .maxu
  | 0x05, 4 => some .min  | 0x05, 5 => some .minu
  | 0x30, 1 => some .rol  | 0x30, 5 => some .ror
  | _, _ => none

def decodeRW (f7 f3 : Nat) : Option RWOp :=
  match f7, f3 with
  | 0x00, 0 => some .addw | 0x20, 0 => some .subw
  | 0x00, 1 => some .sllw | 0x00, 5 => some .srlw | 0x20, 5 => some .sraw
  | 0x01, 0 => some .mulw | 0x01, 4 => some .divw | 0x01, 5 => some .divuw
  | 0x01, 6 => some .remw | 0x01, 7 => some .remuw
  | 0x04, 0 => some .adduw
  | 0x10, 2 => some .sh1adduw | 0x10, 4 => some .sh2adduw | 0x10, 6 => some .sh3adduw
  | 0x30, 1 => some .rolw | 0x30, 5 => some .rorw
  | _, _ => none

def decode (w : BitVec 32) : Option Instr :=
  let opc := bits w 0 7
  let rd := regAt w 7
  let f3 := bits w 12 3
  let rs1 := regAt w 15
  let rs2 := regAt w 20
  let f7 := bits w 25 7
  let imm12 := bits w 20 12
  match opc with
  | 0x37 => some (.lui rd (immU w))
  | 0x17 => some (.auipc rd (immU w))
  | 0x6f => some (.jal rd (immJ w))
  | 0x67 => if f3 = 0 then some (.jalr rd rs1 (immI w)) else none
  | 0x63 =>
    match f3 with
    | 0 => some (.branch .beq rs1 rs2 (immB w))
    | 1 => some (.branch .bne rs1 rs2 (immB w))
    | 4 => some (.branch .blt rs1 rs2 (immB w))
    | 5 => some (.branch .bge rs1 rs2 (immB w))
    | 6 => some (.branch .bltu rs1 rs2 (immB w))
    | 7 => some (.branch .bgeu rs1 rs2 (immB w))
    | _ => none
  | 0x03 =>
    match f3 with
    | 0 => some (.load .lb rd rs1 (immI w))
    | 1 => some (.load .lh rd rs1 (immI w))
    | 2 => some (.load .lw rd rs1 (immI w))
    | 3 => some (.load .ld rd rs1 (immI w))
    | 4 => some (.load .lbu rd rs1 (immI w))
    | 5 => some (.load .lhu rd rs1 (immI w))
    | 6 => some (.load .lwu rd rs1 (immI w))
    | _ => none
  | 0x23 =>
    match f3 with
    | 0 => some (.store .sb rs1 rs2 (immS w))
    | 1 => some (.store .sh rs1 rs2 (immS w))
    | 2 => some (.store .sw rs1 rs2 (immS w))
    | 3 => some (.store .sd rs1 rs2 (immS w))
    | _ => none
  | 0x13 =>
    let sh := BitVec.ofNat 6 (bits w 20 6)
    let top6 := bits w 26 6
    match f3 with
    | 0 => some (.iop .addi rd rs1 (immI w))
    | 2 => some (.iop .slti rd rs1 (immI w))
    | 3 => some (.iop .sltiu rd rs1 (immI w))
    | 4 => some (.iop .xori rd rs1 (immI w))
    | 6 => some (.iop .ori rd rs1 (immI w))
    | 7 => some (.iop .andi rd rs1 (immI w))
    | 1 =>
      if top6 = 0x00 then some (.shift .slli rd rs1 sh)
      else if imm12 = 0x600 then some (.uop .clz rd rs1)
      else if imm12 = 0x601 then some (.uop .ctz rd rs1)
      else if imm12 = 0x602 then some (.uop .cpop rd rs1)
      else if imm12 = 0x604 then some (.uop .sextb rd rs1)
      else if imm12 = 0x605 then some (.uop .sexth rd rs1)
      else none
    | 5 =>
      if top6 = 0x00 then some (.shift .srli rd rs1 sh)
      else if top6 = 0x10 then some (.shift .srai rd rs1 sh)
      else if top6 = 0x18 then some (.shift .rori rd rs1 sh)
      else if imm12 = 0x6b8 then some (.uop .rev8 rd rs1)
      else if imm12 = 0x287 then some (.uop .orcb rd rs1)
      else none
    | _ => none
  | 0x1b =>
    let sh := BitVec.ofNat 5 (bits w 20 5)
    match f3 with
    | 0 => some (.addiw rd rs1 (immI w))
    | 1 =>
      if f7 = 0x00 then some (.shiftw .slliw rd rs1 sh)
      else if bits w 26 6 = 0x02 then some (.shift .slliuw rd rs1 (BitVec.ofNat 6 (bits w 20 6)))
      else if imm12 = 0x600 then some (.uop .clzw rd rs1)
      else if imm12 = 0x601 then some (.uop .ctzw rd rs1)
      else if imm12 = 0x602 then some (.uop .cpopw rd rs1)
      else none
    | 5 =>
      if f7 = 0x00 then some (.shiftw .srliw rd rs1 sh)
      else if f7 = 0x20 then some (.shiftw .sraiw rd rs1 sh)
      else if f7 = 0x30 then some (.shiftw .roriw rd rs1 sh)
      else none
    | _ => none
  | 0x33 => (decodeR f7 f3).map fun op => .rop op rd rs1 rs2
  | 0x3b =>
    if f7 = 0x04 ∧ f3 = 4 ∧ bits w 20 5 = 0 then some (.uop .zexth rd rs1)
    else (decodeRW f7 f3).map fun op => .rwop op rd rs1 rs2
  | 0x73 => if w = 0x00000073#32 then some .ecall else none
  | _ => none

/-! ## Encoding

Used by the tests and by `decode_encode`, never by a proof about a binary:
the proofs decode the bytes the binary actually contains. -/

def rTy (f7 : Nat) (rs2 rs1 : Reg) (f3 : Nat) (rd : Reg) (opc : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (opc + rd.val * 2^7 + f3 * 2^12 + rs1.val * 2^15 + rs2.val * 2^20 + f7 * 2^25)

def iTy (imm : Nat) (rs1 : Reg) (f3 : Nat) (rd : Reg) (opc : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (opc + rd.val * 2^7 + f3 * 2^12 + rs1.val * 2^15 + imm * 2^20)

def encR (op : ROp) : Nat × Nat :=
  match op with
  | .add => (0x00, 0) | .sub => (0x20, 0) | .sll => (0x00, 1) | .slt => (0x00, 2)
  | .sltu => (0x00, 3) | .xor => (0x00, 4) | .srl => (0x00, 5) | .sra => (0x20, 5)
  | .or => (0x00, 6) | .and => (0x00, 7)
  | .mul => (0x01, 0) | .mulh => (0x01, 1) | .mulhsu => (0x01, 2) | .mulhu => (0x01, 3)
  | .div => (0x01, 4) | .divu => (0x01, 5) | .rem => (0x01, 6) | .remu => (0x01, 7)
  | .sh1add => (0x10, 2) | .sh2add => (0x10, 4) | .sh3add => (0x10, 6)
  | .andn => (0x20, 7) | .orn => (0x20, 6) | .xnor => (0x20, 4)
  | .max => (0x05, 6) | .maxu => (0x05, 7) | .min => (0x05, 4) | .minu => (0x05, 5)
  | .rol => (0x30, 1) | .ror => (0x30, 5)

def encRW (op : RWOp) : Nat × Nat :=
  match op with
  | .addw => (0x00, 0) | .subw => (0x20, 0) | .sllw => (0x00, 1) | .srlw => (0x00, 5)
  | .sraw => (0x20, 5) | .mulw => (0x01, 0) | .divw => (0x01, 4) | .divuw => (0x01, 5)
  | .remw => (0x01, 6) | .remuw => (0x01, 7) | .adduw => (0x04, 0)
  | .sh1adduw => (0x10, 2) | .sh2adduw => (0x10, 4) | .sh3adduw => (0x10, 6)
  | .rolw => (0x30, 1) | .rorw => (0x30, 5)

def encode : Instr → BitVec 32
  | .lui rd imm => BitVec.ofNat 32 (0x37 + rd.val * 2^7 + imm.toNat * 2^12)
  | .auipc rd imm => BitVec.ofNat 32 (0x17 + rd.val * 2^7 + imm.toNat * 2^12)
  | .jal rd off =>
    let o := off.toNat
    BitVec.ofNat 32 (0x6f + rd.val * 2^7 + (o >>> 12) % 2^8 * 2^12 + (o >>> 11) % 2 * 2^20 +
      (o >>> 1) % 2^10 * 2^21 + (o >>> 20) % 2 * 2^31)
  | .jalr rd rs1 off => iTy off.toNat rs1 0 rd 0x67
  | .branch op rs1 rs2 off =>
    let f3 := match op with
      | .beq => 0 | .bne => 1 | .blt => 4 | .bge => 5 | .bltu => 6 | .bgeu => 7
    let o := off.toNat
    BitVec.ofNat 32 (0x63 + (o >>> 11) % 2 * 2^7 + (o >>> 1) % 2^4 * 2^8 + f3 * 2^12 +
      rs1.val * 2^15 + rs2.val * 2^20 + (o >>> 5) % 2^6 * 2^25 + (o >>> 12) % 2 * 2^31)
  | .load op rd rs1 off =>
    let f3 := match op with
      | .lb => 0 | .lh => 1 | .lw => 2 | .ld => 3 | .lbu => 4 | .lhu => 5 | .lwu => 6
    iTy off.toNat rs1 f3 rd 0x03
  | .store op rs1 rs2 off =>
    let f3 := match op with | .sb => 0 | .sh => 1 | .sw => 2 | .sd => 3
    let o := off.toNat
    BitVec.ofNat 32 (0x23 + o % 2^5 * 2^7 + f3 * 2^12 + rs1.val * 2^15 + rs2.val * 2^20 +
      (o >>> 5) * 2^25)
  | .iop op rd rs1 imm =>
    let f3 := match op with
      | .addi => 0 | .slti => 2 | .sltiu => 3 | .xori => 4 | .ori => 6 | .andi => 7
    iTy imm.toNat rs1 f3 rd 0x13
  | .addiw rd rs1 imm => iTy imm.toNat rs1 0 rd 0x1b
  | .shift op rd rs1 sh =>
    match op with
    | .slli => iTy sh.toNat rs1 1 rd 0x13
    | .srli => iTy sh.toNat rs1 5 rd 0x13
    | .srai => iTy (0x400 + sh.toNat) rs1 5 rd 0x13
    | .rori => iTy (0x600 + sh.toNat) rs1 5 rd 0x13
    | .slliuw => iTy (0x080 + sh.toNat) rs1 1 rd 0x1b
  | .shiftw op rd rs1 sh =>
    match op with
    | .slliw => iTy sh.toNat rs1 1 rd 0x1b
    | .srliw => iTy sh.toNat rs1 5 rd 0x1b
    | .sraiw => iTy (0x400 + sh.toNat) rs1 5 rd 0x1b
    | .roriw => iTy (0x600 + sh.toNat) rs1 5 rd 0x1b
  | .rop op rd rs1 rs2 => let (f7, f3) := encR op; rTy f7 rs2 rs1 f3 rd 0x33
  | .rwop op rd rs1 rs2 => let (f7, f3) := encRW op; rTy f7 rs2 rs1 f3 rd 0x3b
  | .uop op rd rs1 =>
    match op with
    | .clz => iTy 0x600 rs1 1 rd 0x13
    | .ctz => iTy 0x601 rs1 1 rd 0x13
    | .cpop => iTy 0x602 rs1 1 rd 0x13
    | .sextb => iTy 0x604 rs1 1 rd 0x13
    | .sexth => iTy 0x605 rs1 1 rd 0x13
    | .rev8 => iTy 0x6b8 rs1 5 rd 0x13
    | .orcb => iTy 0x287 rs1 5 rd 0x13
    | .clzw => iTy 0x600 rs1 1 rd 0x1b
    | .ctzw => iTy 0x601 rs1 1 rd 0x1b
    | .cpopw => iTy 0x602 rs1 1 rd 0x1b
    | .zexth => rTy 0x04 0 rs1 4 rd 0x3b
  | .ecall => 0x00000073#32

end NoCompiler
