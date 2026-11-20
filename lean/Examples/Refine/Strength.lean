import Examples.Sum
import NoCompiler.RefineRel

/-
Relational cut points, test case (docs/isa/refine.md): A sums an array by
index, B by pointer (strength reduction in the loop).

    A                                  B
    1000 li   a2, 0                    2000 li   a2, 0
    1004 li   a3, 0                    2004 slli t0, a1, 3
    1008 beq  a3, a1, 1024  <- head    2008 add  t0, a0, t0
    100c slli t0, a3, 3                200c beq  a0, t0, 2020   <- head
    1010 add  t0, a0, t0               2010 ld   t1, 0(a0)
    1014 ld   t1, 0(t0)                2014 add  a2, a2, t1
    1018 add  a2, a2, t1               2018 addi a0, a0, 8
    101c addi a3, a3, 1                201c j    200c
    1020 j    1008                     2020 mv   a0, a2
    1024 mv   a0, a2                   2024 ret
    1028 ret
-/
namespace Examples.Refine.Strength
open NoCompiler

def cA : Code := ⟨0x1000#64, #[0x00000613#32, 0x00000693#32, 0x00b68e63#32, 0x00369293#32,
  0x005502b3#32, 0x0002b303#32, 0x00660633#32, 0x00168693#32, 0xfe9ff06f#32, 0x00060513#32,
  0x00008067#32]⟩
def DA : Dom := [(0x1000#64, 44)]
def cB : Code := ⟨0x2000#64, #[0x00000613#32, 0x00359293#32, 0x005502b3#32, 0x00550a63#32,
  0x00053303#32, 0x00660633#32, 0x00850513#32, 0xff1ff06f#32, 0x00060513#32, 0x00008067#32]⟩
def DB : Dom := [(0x2000#64, 40)]

@[nocompiler_image] theorem a00 : cA.instr 0x1000#64 = some (.iop .addi 12 0 0) := by decide
@[nocompiler_image] theorem a04 : cA.instr 0x1004#64 = some (.iop .addi 13 0 0) := by decide
@[nocompiler_image] theorem a08 : cA.instr 0x1008#64 = some (.branch .beq 13 11 0x1c) := by decide
@[nocompiler_image] theorem a0c : cA.instr 0x100c#64 = some (.shift .slli 5 13 3) := by decide
@[nocompiler_image] theorem a10 : cA.instr 0x1010#64 = some (.rop .add 5 10 5) := by decide
@[nocompiler_image] theorem a14 : cA.instr 0x1014#64 = some (.load .ld 6 5 0) := by decide
@[nocompiler_image] theorem a18 : cA.instr 0x1018#64 = some (.rop .add 12 12 6) := by decide
@[nocompiler_image] theorem a1c : cA.instr 0x101c#64 = some (.iop .addi 13 13 1) := by decide
@[nocompiler_image] theorem a20 : cA.instr 0x1020#64 = some (.jal 0 0x1fffe8) := by decide
@[nocompiler_image] theorem a24 : cA.instr 0x1024#64 = some (.iop .addi 10 12 0) := by decide
@[nocompiler_image] theorem a28 : cA.instr 0x1028#64 = some (.jalr 0 1 0) := by decide

@[nocompiler_image] theorem b00 : cB.instr 0x2000#64 = some (.iop .addi 12 0 0) := by decide
@[nocompiler_image] theorem b04 : cB.instr 0x2004#64 = some (.shift .slli 5 11 3) := by decide
@[nocompiler_image] theorem b08 : cB.instr 0x2008#64 = some (.rop .add 5 10 5) := by decide
@[nocompiler_image] theorem b0c : cB.instr 0x200c#64 = some (.branch .beq 10 5 0x14) := by decide
@[nocompiler_image] theorem b10 : cB.instr 0x2010#64 = some (.load .ld 6 10 0) := by decide
@[nocompiler_image] theorem b14 : cB.instr 0x2014#64 = some (.rop .add 12 12 6) := by decide
@[nocompiler_image] theorem b18 : cB.instr 0x2018#64 = some (.iop .addi 10 10 8) := by decide
@[nocompiler_image] theorem b1c : cB.instr 0x201c#64 = some (.jal 0 0x1ffff0) := by decide
@[nocompiler_image] theorem b20 : cB.instr 0x2020#64 = some (.iop .addi 10 12 0) := by decide
@[nocompiler_image] theorem b24 : cB.instr 0x2024#64 = some (.jalr 0 1 0) := by decide

/-- Live at the head: ra, the preserved registers, a1 (n) and a2 (the sum). -/
abbrev L1 : List Reg := [1, 2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 11, 12]
abbrev Lall : List Reg := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
  23, 24, 25, 26, 27, 28, 29, 30, 31]

/-- The relational invariant at the heads. -/
def inv1 (s0 sa sb : State) : Prop :=
  sb.reg 10 = s0.reg 10 + sa.reg 13 <<< 3 ∧ sb.reg 5 = s0.reg 10 + s0.reg 11 <<< 3 ∧
  sa.reg 10 = s0.reg 10 ∧ sa.reg 11 = s0.reg 11 ∧ (sa.reg 13).toNat ≤ (s0.reg 11).toNat ∧
  (s0.reg 11).toNat * 8 < 2 ^ 64

def c0 : Cut := ⟨0x2000#64, 0x1000#64, Lall, fun _ _ _ => True⟩
def c1 : Cut := ⟨0x200c#64, 0x1008#64, L1, inv1⟩
def cuts : List Cut := [c0, c1]

theorem move1 (P : Perm) (s0 sa sb : State) (hpb : sb.pc = 0x200c#64) (hpa : sa.pc = 0x1008#64)
    (hx : sa.exit = none) (hra : sa.reg 1 = s0.reg 1) (hag : Agree L1 sa sb) (hinv : inv1 s0 sa sb)
    (hA : Exec cA P DA (fun _ => True) sa) :
    Reach cB P DB (fun tb => ∃ ta, RunPlus cA P DA sa ta ∧ CutRel cuts s0 ta tb) sb := by
  obtain ⟨h10, h5, ha10, ha11, hle, hbd⟩ := hinv
  cases hrA : runUntilAP cA DA (Cut.stopA cuts) P 16 sa with
  | none =>
    exfalso
    unfold DA Cut.stopA cuts c0 c1 at hrA
    rw [← State.setPc_self sa, hpa] at hrA
    rel_eval hrA
    all_goals trace_state
    all_goals sorry
  | some r =>
    sorry

end Examples.Refine.Strength
