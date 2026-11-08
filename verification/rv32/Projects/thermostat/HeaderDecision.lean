import Projects.thermostat.HeaderCode
import Projects.thermostat.Literal
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HeaderDecision
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (a b : BitVec 8)
    (hp : c.pc = 0x8000272a#32) (h6 : c.get 6 = BitVec.ofNat 32 a.toNat) (h7 : c.get 7 = BitVec.ofNat 32 b.toNat) :
    DetStep B img ⟨c,ram⟩ ⟨c.goto (if a = b then 0x8000272e#32 else 0x800026e2#32),ram⟩ := by
  refine detStep_of (by rw [hp];decide) (by rw [hp];exact hd2147493674) fun o => ?_
  rw [exec_branch,h6,h7]
  have ht : taken .ne (BitVec.ofNat 32 a.toNat) (BitVec.ofNat 32 b.toNat) = decide (a ≠ b) := by
    change decide (BitVec.ofNat 32 a.toNat ≠ BitVec.ofNat 32 b.toNat) = _
    simp only [ne_eq,Literal.byte_injective]
  rw [ht]
  by_cases he : a = b
  · simp only [he,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false]
    change Result.ok (c.goto (c.pc+4#32)) ram [] = _;rw [hp];rfl
  · simp only [he,ne_eq,not_false_eq_true,decide_true,ite_true,ite_false]
    rw [hp]
    change interp B img o (jump c (0x8000272a#32+0xffffffb8#32)) ram 0 [] = _
    rw [show 0x8000272a#32+0xffffffb8#32 = 0x800026e2#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
end E5R.Thermostat.HeaderDecision
