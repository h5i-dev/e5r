/-
  Fetch-fact generator (a program, not part of any proof): for every instruction in the given ranges,
  print `theorem fXXXXXXXX : fetchDecode img 0x… = some (instr, len) := fetchDecode_of …` in the form of
  Projects/rmk/Uart/SendFetch.lean. The kernel checks every printed fact against the packed ELF.
    LEAN_PATH=. lean --run rmk-audit/FactGen.lean A..B ...   (decimal addresses, from verification/rv32)
  Original e5r code, Apache-2.0.
-/
import Projects.rmk.Fetch
open E5R E5R.Rmk
def hex8 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n); "".pushn '0' (8 - s.length) ++ s
def hexN (n : Nat) : String := String.ofList (Nat.toDigits 16 n)
def clean (s : String) : String :=
  (s.replace "\n" " ").splitOn " " |>.filter (· ≠ "") |> " ".intercalate
def gen (a b : Nat) : IO Unit := do
  let mut pc := a
  while pc < b do
    match fetchT textByte (BitVec.ofNat 32 pc), fetchDecode img (BitVec.ofNat 32 pc) with
    | some (bits, _), some (i, len) =>
      IO.println s!"theorem f{hex8 pc} : fetchDecode img 0x{hex8 pc} = some ({clean (reprStr i)}, 0x{hex8 len.toNat}#32) :=\n  fetchDecode_of _ (by decide) (by decide) (bits := 0x{hexN bits.toNat}) (by decide +kernel) (by decide +kernel)\n"
      pc := pc + len.toNat
    | _, _ => IO.eprintln s!"no decode at {hex8 pc}"; pc := pc + 2
def main (args : List String) : IO Unit := do
  for r in args do
    match r.splitOn ".." with
    | [a, b] => gen (String.toNat! a) (String.toNat! b)
    | _ => IO.eprintln s!"range a..b in decimal: {r}"
