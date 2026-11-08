import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadClCarryRaw
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (low product high upper : Word) (h14 : c.get 14=low) (h29 : c.get 29=product) (h13 : c.get 13=high) (h12 : c.get 12=upper)
    (hp : c.pc=0x8000323c#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003244#32 ∧
      d.get 29=alu .sltu low product ∧ d.get 13=alu .add (alu .add high (alu .sltu low product)) upper ∧ (∀ r : Reg, r≠29 → r≠13 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 29 (alu .sltu low product) 0x80003240#32
  let c2 := c1.wr 13 (alu .add high (alu .sltu low product)) 0x80003242#32
  let c3 := c2.wr 13 (alu .add (alu .add high (alu .sltu low product)) upper) 0x80003244#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496508) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_op,h14,h29];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003240#32).getLsbD 0=false;decide) hh2147496512 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v13 : c1.get 13=high := by simp [c1,Core.wr_get_ne,Core.wr_get,h14,h29,h13,h12]
    have v29 : c1.get 29=alu .sltu low product := by simp [c1,Core.wr_get_ne,Core.wr_get,h14,h29,h13,h12]
    rw [exec_op,v13,v29];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80003242#32).getLsbD 0=false;decide) hh2147496514 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v13 : c2.get 13=alu .add high (alu .sltu low product) := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h14,h29,h13,h12]
    have v12 : c2.get 12=upper := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h14,h29,h13,h12]
    rw [exec_op,v13,v12];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h29,h13,h12]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h29,h13,h12]
  · intro reg h29 h13;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h29,h13,h12,h29,h13]
end E5R.Thermostat.HeadClCarryRaw
