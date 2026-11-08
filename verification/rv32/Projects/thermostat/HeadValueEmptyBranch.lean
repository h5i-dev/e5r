import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
namespace E5R.Thermostat.HeadValueEmptyBranch
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (a b : Word) (test : Bool)
    (hp : c.pc=0x8000306c#32) (h15 : c.get 15=a) (h26 : c.get 26=b) (ht : taken .geu a b=test) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=(if test then 0x800030c0#32 else 0x80003070#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto (if test then 0x800030c0#32 else 0x80003070#32)
  have step : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496044) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok d ram [],[]⟩
    rw [exec_branch,h15,h26,ht,hp]
    cases test with
    | false => rfl
    | true =>
      change Observed.interp B img o (jump c (0x8000306c#32+0x54#32)) ram 0 [] [] = _
      rw [show 0x8000306c#32+0x54#32=0x800030c0#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  exact ⟨d,.single step,rfl,fun _ => rfl,by rfl⟩
end E5R.Thermostat.HeadValueEmptyBranch
