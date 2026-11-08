import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
namespace E5R.Thermostat.HeadHeaderNextBranch
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (a b : Word) (test : Bool)
    (hp : c.pc=0x800033e6#32) (h24 : c.get 24=a) (h10 : c.get 10=b) (ht : taken .ltu a b=test) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=(if test then 0x80002f58#32 else 0x800033ea#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto (if test then 0x80002f58#32 else 0x800033ea#32)
  have step : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496934) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok d ram [],[]⟩
    rw [exec_branch,h24,h10,ht,hp]
    cases test with
    | false => rfl
    | true =>
      change Observed.interp B img o (jump c (0x800033e6#32+0xfffffb72#32)) ram 0 [] [] = _
      rw [show 0x800033e6#32+0xfffffb72#32=0x80002f58#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  exact ⟨d,.single step,rfl,fun _ => rfl,by rfl⟩
end E5R.Thermostat.HeadHeaderNextBranch
