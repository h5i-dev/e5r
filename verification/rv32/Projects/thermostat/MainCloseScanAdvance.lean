import Projects.thermostat.MainCloseCode
import Projects.thermostat.QuietBranch
import Projects.thermostat.Bytes
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseScanAdvance
open E5R E5R.Thermostat

/-- Actual index increment, next pointer and end comparison. Offset bounds
    establish injectivity even when a modular pointer addition wraps. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (i finish : Nat)
    (inside : i<finish) (bound : finish<2^32) (hp : c.pc=0x80002592#32)
    (h22 : c.get 22=base) (h23 : c.get 23=BitVec.ofNat 32 i) (h15 : c.get 15=base+BitVec.ofNat 32 finish) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if i+1=finish then 0x8000259c#32 else 0x80002586#32) ∧
      d.get 10=base+BitVec.ofNat 32 (i+1) ∧ d.get 23=BitVec.ofNat 32 (i+1) ∧
      (∀ r : Reg, r≠10 → r≠23 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 23 (BitVec.ofNat 32 (i+1)) 0x80002594#32
  let b := a.wr 10 (base+BitVec.ofNat 32 (i+1)) 0x80002598#32
  have sa : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147493266) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok a ram [],[]⟩
    rw [exec_opimm,h23,hp]
    change Observed.interp B img o (Eff.done (c.wr 23 (BitVec.ofNat 32 i+1#32) 0x80002594#32)) ram 0 [] [] = _
    rw [←BitVec.ofNat_add];rfl
  have a22 : a.get 22=base := by simp [a,Core.wr_get,h22]
  have a23 : a.get 23=BitVec.ofNat 32 (i+1) := by simp [a,Core.wr_get]
  have sb : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine Quiet.step_of (by change (0x80002594#32).getLsbD 0=false;decide) re2147493268 fun o => ?_
    change Observed.interp B img o (exec a _ _) ram 0 [] [] = ⟨.ok b ram [],[]⟩
    rw [exec_op,a22,a23];rfl
  have b10 : b.get 10=base+BitVec.ofNat 32 (i+1) := by simp [b,Core.wr_get]
  have b15 : b.get 15=base+BitVec.ofNat 32 finish := by simp [b,a,Core.wr_get,h15]
  have tested : taken .ne (base+BitVec.ofNat 32 (i+1)) (base+BitVec.ofNat 32 finish)=decide (i+1≠finish) := by
    change decide (base+BitVec.ofNat 32 (i+1)≠base+BitVec.ofNat 32 finish)=_
    by_cases same : i+1=finish
    · simp only [same,ne_eq,not_true_eq_false,decide_false]
    · have apart := Bytes.offset_ne base (i+1) finish (by omega) bound same
      simp only [ne_eq,apart,same,not_false_eq_true,decide_true]
  obtain ⟨d,sd,pd,dr,dc⟩ := QuietBranch.contract B img b ram 0x80002598#32 4#32 0xffffffee#32 .ne 10 15
    (decide (i+1≠finish)) rfl (by decide) (by decide) re2147493272 (by rw [b10,b15];exact tested)
  refine ⟨d,(Quiet.Steps.single sa).trans ((Quiet.Steps.single sb).trans sd),?_,(dr 10).trans b10,?_,?_,dc.trans ((Core.sameCsr_wr a _ _ _).trans (Core.sameCsr_wr c _ _ _))⟩
  · by_cases same : i+1=finish <;> simpa [same] using pd
  · exact (dr 23).trans (by simp [b,a,Core.wr_get])
  · intro r n10 n23
    exact (dr r).trans (by simp only [b,a,Core.wr_get_ne _ _ _ _ _ n10,Core.wr_get_ne _ _ _ _ _ n23])
end E5R.Thermostat.MainCloseScanAdvance
