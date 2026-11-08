import Projects.thermostat.ApplySetupCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ApplyCallSetupQuiet
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  
    (hp : c.pc=0x800006da#32) :
    Quiet.Steps B img 5 ⟨c,ram⟩ ⟨ApplyCall.setup c,ram⟩ := by
  let c1 := c.wr 10 (c.get 2+24#32) 0x800006dc#32
  let c2 := c1.wr 12 (c.get 2+14#32) 0x800006e0#32
  let c3 := c2.wr 11 (c.get 20) 0x800006e2#32
  let c4 := c3.wr 1 (0x800016e2#32) 0x800006e6#32
  let c5 := c4.wr 1 (0x800006ea#32) 0x80001e38#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact t2147485402) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800006dc#32).getLsbD 0=false;decide) t2147485404 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v2 : c1.get 2=c.get 2 := by simp [c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800006e0#32).getLsbD 0=false;decide) t2147485408 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v20 : c2.get 20=c.get 20 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_op,Core.get_zero,v20,show alu .add (0 : Word) (c.get 20)=c.get 20 from BitVec.zero_add _];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800006e2#32).getLsbD 0=false;decide) t2147485410 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_auipc,show c3.pc=0x800006e2#32 by rfl,show 0x800006e2#32+4096#32=0x800016e2#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800006e6#32).getLsbD 0=false;decide) t2147485414 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v1 : c4.get 1=0x800016e2#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c4.set 1 0x800006ea#32) ((0x800016e2#32+1878#32) &&& ~~~1)) ram 0 [] [] = _
    rw [show (0x800016e2#32+1878#32) &&& ~~~1=0x80001e38#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  change Quiet.Steps B img 5 ⟨c,ram⟩ ⟨c5,ram⟩
  exact .step t0 (.step t1 (.step t2 (.step t3 (.single t4))))
end E5R.Thermostat.ApplyCallSetupQuiet
