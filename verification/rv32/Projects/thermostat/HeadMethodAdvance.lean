import Projects.thermostat.HttpParseCode
import Projects.thermostat.Quiet
namespace E5R.Thermostat.HeadMethodAdvance
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (index last : Word) (atEnd : Bool)
    (hp : c.pc=0x80002cf4#32) (h17 : c.get 17=index) (h9 : c.get 9=last)
    (ht : taken .eq last (index+1#32)=atEnd) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if atEnd then 0x80002efc#32 else 0x80002cfa#32) ∧ d.get 17=index+1#32 ∧
      (∀ r : Reg, r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 17 (index+1#32) 0x80002cf6#32
  let d := a.goto (if atEnd then 0x80002efc#32 else 0x80002cfa#32)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495156) fun o => ?_
    rw [exec_opimm,h17,hp]
    rfl
  have t1 : Quiet.Step B img ⟨a,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by change (0x80002cf6#32).getLsbD 0=false;decide) hh2147495158 fun o => ?_
    have v9 : a.get 9=last := by simp [a,Core.wr_get_ne,h9]
    have v17 : a.get 17=index+1#32 := by simp [a,Core.wr_get]
    rw [exec_branch,v9,v17,ht]
    cases atEnd with
    | false => rfl
    | true =>
      simp only [ite_true]
      change Observed.interp B img o (jump a (0x80002cf6#32+0x206#32)) ram 0 [] []=_
      rw [show 0x80002cf6#32+0x206#32=0x80002efc#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  exact ⟨d,.step t0 (.single t1),rfl,by simp [d,a,Core.wr_get],fun r hr => by simp [d,a,Core.wr_get_ne,hr],rfl⟩
end E5R.Thermostat.HeadMethodAdvance
