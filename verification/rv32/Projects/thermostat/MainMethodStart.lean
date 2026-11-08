import Projects.thermostat.MainMethodDecodeCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainMethodStart
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (rx start finish : Word)
(h21 : c.get 21=rx) (h7 : c.get 7=start) (h11 : c.get 11=finish)
    (hp : c.pc=0x80000d58#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000d64#32 ∧
      d.get 16=finish-start ∧ d.get 15=rx+start ∧ d.get 14=6#32 ∧ d.get 6=4#32 ∧ (∀ r : Reg, r≠16 → r≠15 → r≠14 → r≠6 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 16 (finish-start) 0x80000d5c#32
  let c2 := c1.wr 15 (rx+start) 0x80000d60#32
  let c3 := c2.wr 14 (6#32) 0x80000d62#32
  let c4 := c3.wr 6 (4#32) 0x80000d64#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147487064) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v11 : c.get 11=finish := by simp [Core.wr_get_ne,Core.wr_get,h21,h7,h11]
    have v7 : c.get 7=start := by simp [Core.wr_get_ne,Core.wr_get,h21,h7,h11]
    rw [exec_op,v11,v7];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000d5c#32).getLsbD 0=false;decide) re2147487068 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v21 : c1.get 21=rx := by simp [c1,Core.wr_get_ne,Core.wr_get,h21,h7,h11]
    have v7 : c1.get 7=start := by simp [c1,Core.wr_get_ne,Core.wr_get,h21,h7,h11]
    rw [exec_op,v21,v7];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000d60#32).getLsbD 0=false;decide) re2147487072 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];rfl
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000d62#32).getLsbD 0=false;decide) re2147487074 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];rfl
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h21,h7,h11]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h21,h7,h11]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h21,h7,h11]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h21,h7,h11]
  · intro reg h16 h15 h14 h6;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h21,h7,h11,h16,h15,h14,h6]
end E5R.Thermostat.MainMethodStart
