/-
  Generator (a program, not part of any proof): print the instruction facts of
  `cobs::dec::decode_in_place` (0x8001e006) and
  `cobs::dec::decode_in_place_report` (0x8001e02e..0x8001e148) in the pinned RMK
  image, as decoded by the model's own `fetchDecode` on the checker's reader
  applied to the runner-generated packed file. Every printed fact is then checked
  by the kernel in CobsFetch.lean; this program is only trusted to propose them.

  Original e5r code, Apache-2.0.
-/
import Theories.Logic
import Theories.RamElf
import Projects.rmk.Elf
open E5R

def img : List Segment := (RamElf.imageOf 0x80000000 0x1000000 E5R.Rmk.Image.elf).ro

def clean (s : String) : String :=
  ((s.replace "E5R." "").replace "\n" " ").splitOn " " |>.filter (· ≠ "") |> " ".intercalate

def main : IO Unit := do
  let mut pc : Nat := 0x8001e006
  while pc < 0x8001e148 do
    match fetch img (BitVec.ofNat 32 pc), fetchDecode img (BitVec.ofNat 32 pc) with
    | some (bits, _), some (i, len) =>
      IO.println s!"theorem f{(Nat.toDigits 16 pc).asString} : fetchDecode img 0x{(Nat.toDigits 16 pc).asString} = some ({clean (reprStr i)}, {len.toNat}) :=\n  fetchDecode_of _ (by decide) (by decide) (bits := {bits.toNat}) (by decide +kernel) (by decide +kernel)"
      pc := pc + len.toNat
    | _, _ => IO.eprintln s!"no instruction at {pc}"; return
