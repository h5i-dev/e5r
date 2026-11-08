import Projects.thermostat.MemcpyCode
import Projects.thermostat.QuietRam
namespace E5R.Thermostat.HeadRamWordBranch
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (a b : Word) (test : Bool)
    (hp : c.pc=0x8000521e#32) (h14 : c.get 14=a) (h13 : c.get 13=b) (ht : taken .ltu a b=test) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=(if test then 0x80005212#32 else 0x80005222#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto (if test then 0x80005212#32 else 0x80005222#32)
  have step : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact cp2147504670) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok d ram [],[]⟩
    rw [exec_branch,h14,h13,ht,hp]
    cases test with
    | false => rfl
    | true =>
      change Observed.interp B img o (jump c (0x8000521e#32+0xfffffff4#32)) ram 0 [] [] = _
      rw [show 0x8000521e#32+0xfffffff4#32=0x80005212#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  exact ⟨d,.single step,rfl,fun _ => rfl,by rfl⟩
end E5R.Thermostat.HeadRamWordBranch
