import Projects.thermostat.HttpParseCode
import Projects.thermostat.Quiet
namespace E5R.Thermostat.HeadMethodEntry
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (index : Word) (empty : Bool)
    (hp : c.pc=0x80002cba#32) (h9 : c.get 9=index) (ht : taken .eq index (0 : Word)=empty) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if empty then 0x80002efc#32 else 0x80002cc2#32) ∧ d.get 15=400#32 ∧
      (∀ r : Reg, r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 15 400#32 0x80002cbe#32
  let d := a.goto (if empty then 0x80002efc#32 else 0x80002cc2#32)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495098) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp]
    rfl
  have t1 : Quiet.Step B img ⟨a,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by change (0x80002cbe#32).getLsbD 0=false;decide) hh2147495102 fun o => ?_
    have v9 : a.get 9=index := by simp [a,Core.wr_get_ne,h9]
    rw [exec_branch,v9,Core.get_zero,ht]
    cases empty with
    | false => rfl
    | true =>
      simp only [ite_true]
      change Observed.interp B img o (jump a (0x80002cbe#32+0x23e#32)) ram 0 [] []=_
      rw [show 0x80002cbe#32+0x23e#32=0x80002efc#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  exact ⟨d,.step t0 (.single t1),rfl,by simp [d,a,Core.wr_get],fun r hr => by simp [d,a,Core.wr_get_ne,hr],rfl⟩
end E5R.Thermostat.HeadMethodEntry
