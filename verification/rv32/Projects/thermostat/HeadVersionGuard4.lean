import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadVersionGuard4
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (offset : Word) (h30 : c.get 30=offset) (ht : taken .eq offset 0xfffffffc#32=false)
    (hp : c.pc=0x80002e56#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002e5c#32 ∧
      d.get 10=0xfffffffc#32 ∧ (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (0xfffffffc#32) 0x80002e58#32
  let c2 := c1.goto 0x80002e5c#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495510) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002e58#32).getLsbD 0=false;decide) hh2147495512 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v30 : c1.get 30=offset := by simp [c1,Core.wr_get_ne,Core.wr_get,h30]
    have v10 : c1.get 10=0xfffffffc#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h30]
    rw [exec_branch,v30,v10,ht];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h30]
  · intro reg h10;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h30,h10]
end E5R.Thermostat.HeadVersionGuard4
