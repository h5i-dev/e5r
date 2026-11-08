import Projects.thermostat.HttpParseCode
import Projects.thermostat.Quiet
namespace E5R.Thermostat.HeadTargetGuard
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (m j : Word) (bad : Bool)
    (hp : c.pc=0x80002dc0#32) (h17 : c.get 17=m) (h9 : c.get 9=j)
    (ht : taken .geu (m+1#32) j=bad) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if bad then 0x80002efc#32 else 0x80002dc8#32) ∧ d.get 29=m+1#32 ∧
      (∀ r : Reg, r≠29 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 29 (m+1#32) 0x80002dc4#32
  let d := a.goto (if bad then 0x80002efc#32 else 0x80002dc8#32)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495360) fun o => ?_
    rw [exec_opimm,h17,hp];rfl
  have t1 : Quiet.Step B img ⟨a,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by change (0x80002dc4#32).getLsbD 0=false;decide) hh2147495364 fun o => ?_
    have v29 : a.get 29=m+1#32 := by simp [a,Core.wr_get]
    have v9 : a.get 9=j := by simp [a,Core.wr_get_ne,h9]
    rw [exec_branch,v29,v9,ht]
    cases bad with
    | false => rfl
    | true =>
      simp only [ite_true]
      change Observed.interp B img o (jump a (0x80002dc4#32+0x138#32)) ram 0 [] [] = _
      rw [show 0x80002dc4#32+0x138#32=0x80002efc#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  exact ⟨d,.step t0 (.single t1),rfl,by simp [d,a,Core.wr_get],fun r hr => by simp [d,a,Core.wr_get_ne,hr],rfl⟩
end E5R.Thermostat.HeadTargetGuard
