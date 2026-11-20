/-
  Disassembler for audit notes (a program, not part of any proof): the model's own fetchDecode on the
  runner-generated packed image. Usage (verification/rv32, after the RAM-image job built Projects/rmk/Elf):
    LEAN_PATH=. lean --run rmk-audit/Dis.lean A..B ...   (decimal addresses)
  Original e5r code, Apache-2.0.
-/
import Theories.Logic
import Theories.RamElf
import Projects.rmk.Elf
open E5R
def img : List Segment := (RamElf.imageOf 0x80000000 0x1000000 E5R.Rmk.Image.elf).ro
def clean (s : String) : String :=
  ((s.replace "E5R." "").replace "Instr." "").replace "\n" " " |>.splitOn " " |>.filter (· ≠ "") |> " ".intercalate
def dis (a b : Nat) : IO Unit := do
  let mut pc := a
  while pc < b do
    match fetchDecode img (BitVec.ofNat 32 pc) with
    | some (i, len) => IO.println s!"{String.ofList (Nat.toDigits 16 pc)}: {clean (reprStr i)}"; pc := pc + len.toNat
    | none => IO.println s!"{String.ofList (Nat.toDigits 16 pc)}: ??"; pc := pc + 2
def main (args : List String) : IO Unit := do
  for r in args do
    match r.splitOn ".." with
    | [a, b] => IO.println s!"== {r}"; dis (String.toNat! a) (String.toNat! b)
    | _ => IO.eprintln s!"range a..b in decimal: {r}"
