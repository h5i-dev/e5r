/-
  Minimal reproducers for the review findings that are about the model
  against the specification (QEMU cannot show them; see independent-review.md).

  Original review code, Apache-2.0. Each check prints PASS when the model
  behaves as the specification requires and FAIL otherwise; the exit code is
  the number of FAILs. Run: `lake env lean --run review/Repro.lean`.
-/
import Theories.Board.Hifive1Revb
open E5R

namespace Repro

def B : Board := Hifive1Revb.board
def base : Nat := 0x20010000

/-- An image holding one 32-bit instruction at `base`. -/
def img1 (w : Nat) : List Segment :=
  [{ base := base, bytes := [w % 256, w / 256 % 256, w / 65536 % 256, w / 16777216 % 256], exec := true }]

def core (regs : List (Nat × Word)) (resv : Bool) : Core :=
  { pc := BitVec.ofNat 32 base, x := fun r => (regs.lookup r.val).getD 0, mie_ := false, mpie := false,
    mpp := 3, mieReg := 0, mtvec := 0, mepc := 0, mcause := 0, mscratch := 0, resv := resv }

/-- `sc.w x13, x12, (x11)` -/
def scW : Nat := 3 <<< 27 ||| 12 <<< 20 ||| 11 <<< 15 ||| 2 <<< 12 ||| 13 <<< 7 ||| 0x2f

def faults : Result → Bool
  | .fault _ => true
  | .ok .. => false

def describe : Result → String
  | .fault f => s!"fault {repr f}"
  | .ok c _ evs => s!"ok, x13 = {(c.get 13).toHex}, {evs.length} events"

/-- Zalrsc (Unprivileged ISA 20240411, "A" 2.1): "If the address is not
    naturally aligned, an address-misaligned exception or an access-fault
    exception will be generated." The sentence does not depend on whether the
    SC would succeed, so every environment answer must fault. -/
def checks : List (String × Result) :=
  let m (a : Word) (resv : Bool) : Machine := ⟨core [(11, a), (12, 0x55)] resv, fun _ => 0⟩
  [ ("misaligned SC, no reservation", stepInstr B (img1 scW) (m 0x80000102 false) (fun _ => 0)),
    ("misaligned SC, reservation, env says fail", stepInstr B (img1 scW) (m 0x80000102 true) (fun _ => 0)),
    ("misaligned SC, reservation, env says succeed", stepInstr B (img1 scW) (m 0x80000102 true) (fun _ => 1)),
    ("SC to an unmapped address, no reservation", stepInstr B (img1 scW) (m 0x40000000 false) (fun _ => 0)),
    ("SC to a device register, no reservation", stepInstr B (img1 scW) (m 0x10015024 false) (fun _ => 0)) ]

end Repro

def main : IO UInt32 := do
  let mut fails : UInt32 := 0
  for (name, r) in Repro.checks do
    let ok := Repro.faults r
    IO.println s!"{if ok then "PASS" else "FAIL"} {name}: {Repro.describe r}"
    if !ok then fails := fails + 1
  -- Control: an aligned SC in RAM without a reservation is an ordinary failing SC.
  let ctl := stepInstr Repro.B (Repro.img1 Repro.scW)
    ⟨Repro.core [(11, 0x80000100), (12, 0x55)] false, fun _ => 0⟩ (fun _ => 0)
  match ctl with
  | .ok c _ [] =>
    if c.get 13 = 1 then IO.println "PASS control: aligned SC without reservation writes rd = 1"
    else
      IO.println "FAIL control: rd is not 1"
      fails := fails + 1
  | r =>
    IO.println s!"FAIL control: {Repro.describe r}"
    fails := fails + 1
  return fails
