/-
  Print the model's decoding of encodings, one per input line, in the
  canonical form review/decode_sweep.py compares with binutils objdump.

  Original review code, Apache-2.0. Input lines: `16 <hex>` or `32 <hex>`.
  Output: `none`, or the instruction's fields (registers as numbers,
  immediates as 32-bit hex).
-/
import Theories.Platform
open E5R

namespace DecodeSweep

def hexNat (s : String) : Option Nat :=
  s.foldl (fun acc c => acc.bind fun n =>
    if '0' ≤ c ∧ c ≤ '9' then some (n * 16 + (c.toNat - '0'.toNat))
    else if 'a' ≤ c ∧ c ≤ 'f' then some (n * 16 + (c.toNat - 'a'.toNat + 10)) else none) (some 0)

def h (w : Word) : String := String.mk (Nat.toDigits 16 w.toNat)
def r (x : Reg) : String := toString x.val

def alu : AluOp → String
  | .add => "add" | .sub => "sub" | .sll => "sll" | .slt => "slt" | .sltu => "sltu"
  | .xor => "xor" | .srl => "srl" | .sra => "sra" | .or => "or" | .and => "and"

def mul : MulOp → String
  | .mul => "mul" | .mulh => "mulh" | .mulhsu => "mulhsu" | .mulhu => "mulhu"
  | .div => "div" | .divu => "divu" | .rem => "rem" | .remu => "remu"

def amo : AmoOp → String
  | .swap => "swap" | .add => "add" | .xor => "xor" | .and => "and" | .or => "or"
  | .min => "min" | .max => "max" | .minu => "minu" | .maxu => "maxu"

def br : BrCond → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .ge => "ge" | .ltu => "ltu" | .geu => "geu"

def wd : Width → String
  | .b => "b" | .h => "h" | .w => "w"

def fmt : Instr → String
  | .lui rd i => s!"lui {r rd} {h i}"
  | .auipc rd i => s!"auipc {r rd} {h i}"
  | .jal rd o => s!"jal {r rd} {h o}"
  | .jalr rd rs1 o => s!"jalr {r rd} {r rs1} {h o}"
  | .branch c a b o => s!"branch {br c} {r a} {r b} {h o}"
  | .load w s rd rs1 o => s!"load {wd w} {s} {r rd} {r rs1} {h o}"
  | .store w rs1 rs2 o => s!"store {wd w} {r rs1} {r rs2} {h o}"
  | .opimm op rd rs1 i => s!"opimm {alu op} {r rd} {r rs1} {h i}"
  | .op op rd rs1 rs2 => s!"op {alu op} {r rd} {r rs1} {r rs2}"
  | .muldiv op rd rs1 rs2 => s!"muldiv {mul op} {r rd} {r rs1} {r rs2}"
  | .lr rd rs1 => s!"lr {r rd} {r rs1}"
  | .sc rd rs1 rs2 => s!"sc {r rd} {r rs1} {r rs2}"
  | .amo op rd rs1 rs2 => s!"amo {amo op} {r rd} {r rs1} {r rs2}"
  | .fence => "fence"
  | .fencei => "fencei"
  | .csr op rd src a =>
    let o := match op with | .rw => "rw" | .rs => "rs" | .rc => "rc"
    let s := match src with | .reg x => s!"r{r x}" | .imm v => s!"i{h v}"
    s!"csr {o} {r rd} {s} {String.mk (Nat.toDigits 16 a)}"
  | .ecall => "ecall"
  | .ebreak => "ebreak"
  | .mret => "mret"
  | .wfi => "wfi"

end DecodeSweep

open DecodeSweep in
def main (args : List String) : IO UInt32 := do
  let lines ← IO.FS.lines args[0]!
  let out ← IO.FS.Handle.mk args[1]! .write
  for l in lines do
    match (l.splitOn " ") with
    | [len, x] =>
      let some v := hexNat x | IO.eprintln s!"bad line {l}"; return 2
      let w := BitVec.ofNat 32 v
      let d := if len == "16" then decode16 w else decode32 w
      out.putStrLn (match d with | some i => fmt i | none => "none")
    | _ => IO.eprintln s!"bad line {l}"; return 2
  return 0
