-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.LetterBranch
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.LetterBranch
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (expected actual : BitVec 8) (site : Site expected)
    (hp : c.pc = site.pc) (h12 : c.get 12 = BitVec.ofNat 32 actual.toNat) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = (if actual = expected then site.pass else site.fail) ∧
      (∀ r : Reg, r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 13 (BitVec.ofNat 32 expected.toNat) (site.pc+4#32)
  let d := c1.goto (if actual = expected then site.pass else site.fail)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];exact site.aligned) (by rw [hp];exact site.constant) fun o => ?_
    rw [exec_opimm,Core.get_zero]
    simp only [alu]
    rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of site.branch_aligned site.branch fun o => ?_
    have hv12 : c1.get 12 = BitVec.ofNat 32 actual.toNat := by simp [c1,Core.wr_get_ne,h12]
    have hv13 : c1.get 13 = BitVec.ofNat 32 expected.toNat := by simp [c1,Core.wr_get]
    rw [exec_branch,hv12,hv13]
    have ht : taken .ne (BitVec.ofNat 32 actual.toNat) (BitVec.ofNat 32 expected.toNat) = decide (actual ≠ expected) := by
      change decide (BitVec.ofNat 32 actual.toNat ≠ BitVec.ofNat 32 expected.toNat) = _
      simp only [ne_eq,Literal.byte_injective]
    rw [ht]
    by_cases he : actual = expected
    · simp only [d,ite_eq_left he,he,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false]
      change interp B img o (.done (c1.goto ((site.pc+4#32)+4#32))) ram 0 [] = _
      rw [site.to_pass];rfl
    · simp only [d,ite_eq_right he,he,ne_eq,not_false_eq_true,decide_true,ite_true]
      change interp B img o (jump c1 ((site.pc+4#32)+site.offset)) ram 0 [] = _
      rw [site.to_fail,jump_ok _ _ site.fail_aligned];rfl
  refine ⟨d,.step s0 (.single s1),rfl,?_,by rfl⟩
  intro r hr;simp [d,c1,Core.wr_get_ne,hr]

end E5R.Thermostat.LetterBranch
