-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.LenBranch
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.LenBranch
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (n k : Nat)
    (hn : n < 2^32) (hk : k < 2^32) (site : Site k)
    (hp : c.pc = site.pc) (h11 : c.get 11 = BitVec.ofNat 32 n) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = (if n = k then yes site else no site) ∧
      (∀ r : Reg, r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (BitVec.ofNat 32 k) (site.pc+2#32)
  let d := c1.goto (if n = k then yes site else no site)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];exact site.aligned) (by rw [hp];exact site.constant) fun o => ?_
    rw [exec_opimm,Core.get_zero]
    simp only [alu]
    rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of site.branch_aligned site.branch fun o => ?_
    have hv11 : c1.get 11 = BitVec.ofNat 32 n := by simp [c1,Core.wr_get_ne,h11]
    have hv12 : c1.get 12 = BitVec.ofNat 32 k := by simp [c1,Core.wr_get]
    rw [exec_branch,hv11,hv12]
    cases heq : site.equal with
    | true =>
      simp only [heq,ite_true]
      rw [Usize.eq n k hn hk]
      by_cases he : n = k
      · simp only [d,yes,no,heq,ite_true,decide_eq_true he,ite_eq_left he]
        change interp B img o (jump c1 ((site.pc+2#32)+site.offset)) ram 0 [] = _
        rw [site.to_target,jump_ok _ _ site.target_aligned];rfl
      · simp only [d,yes,no,heq,ite_true,decide_eq_false he,Bool.false_eq_true,ite_false,ite_eq_right he]
        change interp B img o (.done (c1.goto ((site.pc+2#32)+4#32))) ram 0 [] = _
        rw [site.to_fall];rfl
    | false =>
      simp only [heq,Bool.false_eq_true,ite_false]
      rw [Usize.ne n k hn hk]
      by_cases he : n = k
      · simp only [d,yes,no,heq,Bool.false_eq_true,ite_false,ite_eq_left he,he,ne_eq,not_true_eq_false,decide_false]
        change interp B img o (.done (c1.goto ((site.pc+2#32)+4#32))) ram 0 [] = _
        rw [site.to_fall];rfl
      · simp only [d,yes,no,heq,Bool.false_eq_true,ite_false,ite_eq_right he,he,ne_eq,not_false_eq_true,decide_true,ite_true]
        change interp B img o (jump c1 ((site.pc+2#32)+site.offset)) ram 0 [] = _
        rw [site.to_target,jump_ok _ _ site.target_aligned];rfl
  refine ⟨d,.step s0 (.single s1),rfl,?_,by rfl⟩
  intro r hr;simp [d,c1,Core.wr_get_ne,hr]

end E5R.Thermostat.LenBranch
