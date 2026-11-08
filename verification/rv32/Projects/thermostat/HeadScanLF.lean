import Projects.thermostat.HttpParseCode00
import Projects.thermostat.HeadByteFacts
import Projects.thermostat.Quiet
namespace E5R.Thermostat.HeadScanLF
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (b : BitVec 8)
    (hp : c.pc=0x80002c98#32) (h6 : c.get 6=BitVec.ofNat 32 b.toNat) (hcmp : c.get 15=10#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if b.toNat=10 then 0x80002d5a#32 else 0x80002c9c#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto (if b.toNat=10 then 0x80002d5a#32 else 0x80002c9c#32)
  have step : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495064) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] []=⟨.ok d ram [],[]⟩
    rw [exec_branch,h6,hcmp,HeadByteFacts.lf,hp]
    by_cases he : b.toNat=10
    · simp only [d,he,decide_true,ite_true]
      rw [show 0x80002c98#32+0xc2#32=0x80002d5a#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
    · simp only [d,he,decide_false,ite_false]
      rfl
  exact ⟨d,.single step,rfl,fun _ => rfl,rfl⟩
end E5R.Thermostat.HeadScanLF
