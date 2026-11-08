import Projects.thermostat.MainCloseCode
import Projects.thermostat.QuietBranch
import Projects.thermostat.MainCloseScanFinishMath
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseNextToken
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (n : Nat)
    (bound : n<2^32) (hp : c.pc=0x800025d8#32) (h10 : c.get 10=base) (h14 : c.get 14=BitVec.ofNat 32 n) :
    ∃ k d, k≤4 ∧ Quiet.Steps B img k ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if n=0 then 0x80002474#32 else 0x80002584#32) ∧
      (n≠0 → d.get 22=base ∧ d.get 15=base+BitVec.ofNat 32 n) ∧
      (∀ r : Reg, r≠15 → r≠22 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,sa,pa,ar,ac⟩ := QuietBranch.contract B img c ram 0x800025d8#32 4#32 0xfffffe9c#32 .eq 14 0 (decide (n=0))
    hp (by decide) (by decide) re2147493336 (by rw [h14,Core.get_zero];exact MainCloseScanFinishMath.zeroTest n bound)
  by_cases empty : n=0
  · refine ⟨1,a,by omega,sa,?_,?_,fun r _ _ => ar r,ac⟩
    · simpa [empty] using pa
    · simp only [empty,ne_eq,not_true_eq_false,false_implies]
  · have pa' : a.pc=0x800025dc#32 := by simpa [empty] using pa
    let b := a.wr 15 (base+BitVec.ofNat 32 n) 0x800025e0#32
    let e := b.wr 22 base 0x800025e2#32
    let d := e.goto 0x80002584#32
    have a10 : a.get 10=base := (ar 10).trans h10
    have a14 : a.get 14=BitVec.ofNat 32 n := (ar 14).trans h14
    have sb : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
      refine Quiet.step_of (by rw [pa'];decide) (by rw [pa'];exact re2147493340) fun o => ?_
      change Observed.interp B img o (exec a _ _) ram 0 [] [] = ⟨.ok b ram [],[]⟩
      rw [exec_op,a10,a14,pa'];rfl
    have se : Quiet.Step B img ⟨b,ram⟩ ⟨e,ram⟩ := by
      refine Quiet.step_of (by change (0x800025e0#32).getLsbD 0=false;decide) re2147493344 fun o => ?_
      change Observed.interp B img o (exec b _ _) ram 0 [] [] = ⟨.ok e ram [],[]⟩
      have b10 : b.get 10=base := by simp [b,Core.wr_get,a10]
      rw [exec_op,Core.get_zero,b10]
      simp only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add];rfl
    have sd : Quiet.Step B img ⟨e,ram⟩ ⟨d,ram⟩ := by
      refine Quiet.step_of (by change (0x800025e2#32).getLsbD 0=false;decide) re2147493346 fun o => ?_
      change Observed.interp B img o (exec e _ _) ram 0 [] [] = ⟨.ok d ram [],[]⟩
      rw [exec_jal,Core.set_zero]
      change Observed.interp B img o (jump e (0x800025e2#32+0xffffffa2#32)) ram 0 [] [] = _
      rw [show 0x800025e2#32+0xffffffa2#32=0x80002584#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    refine ⟨4,d,by omega,sa.trans (.step sb (.step se (.single sd))),?_,?_,?_,(Core.sameCsr_goto e _).trans ((Core.sameCsr_wr b _ _ _).trans ((Core.sameCsr_wr a _ _ _).trans ac))⟩
    · simp only [d,Core.goto_pc,empty,ite_false]
    · intro _
      constructor <;> simp [d,e,b,Core.wr_get]
    · intro r n15 n22
      exact (by simp only [d,e,b,Core.goto_get,Core.wr_get_ne _ _ _ _ _ n22,Core.wr_get_ne _ _ _ _ _ n15] : d.get r=a.get r).trans (ar r)
end E5R.Thermostat.MainCloseNextToken
