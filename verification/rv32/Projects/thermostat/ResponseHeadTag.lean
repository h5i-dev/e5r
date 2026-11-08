import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseHeadTag
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (tag len : Word) (h10 : c.get 10=tag) (h11 : c.get 11=len)
    (hp : c.pc=0x800040f8#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80004100#32 ∧
      d.get 17=tag ∧ d.get 5=len ∧ (∀ r : Reg, r≠17 → r≠5 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 17 (tag) 0x800040fa#32
  let c2 := c1.wr 5 (len) 0x800040fc#32
  let c3 := c2.goto 0x80004100#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147500280) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v10 : c.get 10=tag := by simp [Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_op,Core.get_zero,v10,(show alu .add (0 : Word) (tag)=tag from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800040fa#32).getLsbD 0=false;decide) rh2147500282 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v11 : c1.get 11=len := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_op,Core.get_zero,v11,(show alu .add (0 : Word) (len)=len from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800040fc#32).getLsbD 0=false;decide) rh2147500284 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c2 (0x800040fc#32+4#32)) ram 0 [] [] = _
    rw [show 0x800040fc#32+4#32=0x80004100#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · intro reg h17 h5;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h17,h5]
end E5R.Thermostat.ResponseHeadTag
