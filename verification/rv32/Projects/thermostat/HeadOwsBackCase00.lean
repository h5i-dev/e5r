import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadOwsBackCase00
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (v : Word) (h13 : c.get 13=v)
(hb0 : taken .eq (v) (alu .add ((0 : Word)) (9#32))=false)
(hb1 : taken .eq (v) (alu .add ((0 : Word)) (32#32))=false)
    (hp : c.pc=0x800030e2#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800030fa#32 ∧
      d.get 12=alu .add ((0 : Word)) (32#32) ∧ (∀ r : Reg, r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (alu .add ((0 : Word)) (9#32)) 0x800030e4#32
  let c2 := c1.goto 0x800030e8#32
  let c3 := c2.wr 12 (alu .add ((0 : Word)) (32#32)) 0x800030ec#32
  let c4 := c3.goto 0x800030f0#32
  let c5 := c4.goto 0x800030fa#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496162) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800030e4#32).getLsbD 0=false;decide) hh2147496164 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v13 : c1.get 13=v := by simp [c1,Core.wr_get_ne,Core.wr_get,h13]
    have v12 : c1.get 12=alu .add ((0 : Word)) (9#32) := by simp [c1,Core.wr_get_ne,Core.wr_get,h13]
    rw [exec_branch,v13,v12,hb0]
    rfl
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800030e8#32).getLsbD 0=false;decide) hh2147496168 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800030ec#32).getLsbD 0=false;decide) hh2147496172 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v13 : c3.get 13=v := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
    have v12 : c3.get 12=alu .add ((0 : Word)) (32#32) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
    rw [exec_branch,v13,v12,hb1]
    rfl
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800030f0#32).getLsbD 0=false;decide) hh2147496176 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    rw [exec_jal,Core.set_zero]
    change Observed.interp B img o (jump c4 (0x800030f0#32+0xa#32)) ram 0 [] []=_
    rw [show 0x800030f0#32+0xa#32=0x800030fa#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c5,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
  · intro reg h12;simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h12]
end E5R.Thermostat.HeadOwsBackCase00
