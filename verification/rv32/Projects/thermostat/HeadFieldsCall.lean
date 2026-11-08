import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadFieldsCall
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (h2 : c.get 2=sp)
    (hp : c.pc=0x80002f0e#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80005638#32 ∧
      d.get 10=sp+56#32 ∧ d.get 12=271#32 ∧ d.get 11=0#32 ∧ d.get 1=0x80002f1e#32 ∧ (∀ r : Reg, r≠10 → r≠12 → r≠11 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (sp+56#32) 0x80002f10#32
  let c2 := c1.wr 12 (271#32) 0x80002f14#32
  let c3 := c2.wr 11 (0#32) 0x80002f16#32
  let c4 := c3.wr 1 (0x80004f16#32) 0x80002f1a#32
  let c5 := c4.wr 1 (0x80002f1e#32) 0x80005638#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495694) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h2];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f10#32).getLsbD 0=false;decide) hh2147495696 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f14#32).getLsbD 0=false;decide) hh2147495700 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f16#32).getLsbD 0=false;decide) hh2147495702 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_auipc]
    change Observed.interp B img o (.done (c3.wr 1 (0x80002f16#32+0x2000#32) (c3.pc+4#32))) ram 0 [] [] = _
    rw [show 0x80002f16#32+0x2000#32=0x80004f16#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f1a#32).getLsbD 0=false;decide) hh2147495706 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v1 : c4.get 1=0x80004f16#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c4.set 1 (c4.pc+4#32)) ((0x80004f16#32+1826#32) &&& ~~~1)) ram 0 [] [] = _
    rw [show (0x80004f16#32+1826#32) &&& ~~~1=0x80005638#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c5,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · intro reg h10 h12 h11 h1;simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h12,h11,h1]
end E5R.Thermostat.HeadFieldsCall
