import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadTeVersionRaw
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (inverse te : Word) (h18 : c.get 18=inverse) (h23 : c.get 23=te)
    (hp : c.pc=0x800032b4#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800032ba#32 ∧
      d.get 10=alu .and (alu .or inverse te) 1#32 ∧ (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (alu .or inverse te) 0x800032b8#32
  let c2 := c1.wr 10 (alu .and (alu .or inverse te) 1#32) 0x800032ba#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496628) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_op,h18,h23];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800032b8#32).getLsbD 0=false;decide) hh2147496632 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v10 : c1.get 10=alu .or inverse te := by simp [c1,Core.wr_get_ne,Core.wr_get,h18,h23]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h18,h23]
  · intro reg h10;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h18,h23,h10]
end E5R.Thermostat.HeadTeVersionRaw
