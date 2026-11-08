import Projects.thermostat.MainHeaderCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainHeaderResultSubtract
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (tag : Word) (h10 : c.get 10=tag)
    (hp : c.pc=0x80000a4c#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000a4e#32 ∧
      d.get 10=tag+0xfffffffd#32 ∧ (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (tag+0xfffffffd#32) 0x80000a4e#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact mh2147486284) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h10];first | rfl | (rw [hp];rfl)
  refine ⟨c1,.single t0,rfl,?_ ,?_ ,by rfl⟩
  · simp [c1,Core.wr_get_ne,Core.wr_get,h10]
  · intro reg h10;simp [c1,Core.wr_get_ne,Core.wr_get,h10,h10]
end E5R.Thermostat.MainHeaderResultSubtract
