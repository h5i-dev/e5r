import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
namespace E5R.Thermostat.HeadClNumberAdvanceBranch
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (a b : Word) (test : Bool)
    (hp : c.pc=0x8000325c#32) (haReg : c.get 11=a) (hbReg : c.get 0=b) (ht : taken .ne a b=test) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=(if test then 0x80003206#32 else 0x8000325e#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto (if test then 0x80003206#32 else 0x8000325e#32)
  have step : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496540) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok d ram [],[]⟩
    rw [exec_branch,haReg,hbReg,ht,hp]
    cases test with
    | false => rfl
    | true =>
      change Observed.interp B img o (jump c (0x8000325c#32+0xffffffaa#32)) ram 0 [] [] = _
      rw [show 0x8000325c#32+0xffffffaa#32=0x80003206#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  exact ⟨d,.single step,rfl,fun _ => rfl,by rfl⟩
end E5R.Thermostat.HeadClNumberAdvanceBranch
