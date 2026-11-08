import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadDoneClTag
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp flag : Word) (h2 : c.get 2=sp) (h325 : ramRead ram (sp+325#32) .b=flag) (stack : Memory.Block B sp 327)
    (hp : c.pc=0x80003472#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003486#32 ∧
      d.get 10=extend .b false flag ∧ d.get 20=alu .and (extend .b false flag) 1#32 ∧ (∀ r : Reg, r≠10 → r≠20 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (extend .b false flag) 0x80003476#32
  let c2 := c1.wr 20 (alu .and (extend .b false flag) 1#32) 0x8000347a#32
  let c3 := c2.goto 0x80003486#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147497074) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v2 : c.get 2=sp := by simp [Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by change _%1=0;omega) (Memory.block_access stack (off := 325) (by decide) (by decide)),h325];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003476#32).getLsbD 0=false;decide) hh2147497078 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v10 : c1.get 10=extend .b false flag := by simp [c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000347a#32).getLsbD 0=false;decide) hh2147497082 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_jal,Core.set_zero]
    change Observed.interp B img o (jump c2 (0x8000347a#32+12#32)) ram 0 [] []=_
    rw [show 0x8000347a#32+12#32=0x80003486#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · intro reg h10 h20;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h20]
end E5R.Thermostat.HeadDoneClTag
