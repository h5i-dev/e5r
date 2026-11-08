import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadTeWidthRaw
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (start vs span : Word) (h24 : c.get 24=start) (h15 : c.get 15=vs) (h21 : c.get 21=span)
    (hp : c.pc=0x800032d0#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800032d8#32 ∧
      d.get 10=((start-vs)+span)+0xfffffff9#32 ∧ (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (start-vs) 0x800032d4#32
  let c2 := c1.wr 10 ((start-vs)+span) 0x800032d6#32
  let c3 := c2.wr 10 (((start-vs)+span)+0xfffffff9#32) 0x800032d8#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496656) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_op,h24,h15];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800032d4#32).getLsbD 0=false;decide) hh2147496660 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v10 : c1.get 10=start-vs := by simp [c1,Core.wr_get_ne,Core.wr_get,h24,h15,h21]
    have v21 : c1.get 21=span := by simp [c1,Core.wr_get_ne,Core.wr_get,h24,h15,h21]
    rw [exec_op,v10,v21];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800032d6#32).getLsbD 0=false;decide) hh2147496662 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v10 : c2.get 10=(start-vs)+span := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h24,h15,h21]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h24,h15,h21]
  · intro reg h10;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h24,h15,h21,h10]
end E5R.Thermostat.HeadTeWidthRaw
