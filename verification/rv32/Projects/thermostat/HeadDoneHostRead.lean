import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadDoneHostRead
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp inverse host : Word) (h2 : c.get 2=sp) (h18 : c.get 18=inverse) (h324 : ramRead ram (sp+324#32) .b=host) (stack : Memory.Block B sp 327)
    (hp : c.pc=0x80003456#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003460#32 ∧
      d.get 10=alu .and (alu .or inverse (extend .b false host)) 1#32 ∧ (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (extend .b false host) 0x8000345a#32
  let c2 := c1.wr 10 (alu .or inverse (extend .b false host)) 0x8000345e#32
  let c3 := c2.wr 10 (alu .and (alu .or inverse (extend .b false host)) 1#32) 0x80003460#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147497046) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v2 : c.get 2=sp := by simp [Core.wr_get_ne,Core.wr_get,h2,h18]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by change _%1=0;omega) (Memory.block_access stack (off := 324) (by decide) (by decide)),h324];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000345a#32).getLsbD 0=false;decide) hh2147497050 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v10 : c1.get 10=extend .b false host := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h18]
    have v18 : c1.get 18=inverse := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h18]
    rw [exec_op,v18,v10];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000345e#32).getLsbD 0=false;decide) hh2147497054 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v10 : c2.get 10=alu .or inverse (extend .b false host) := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h18]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h18]
  · intro reg h10;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h18,h10]
end E5R.Thermostat.HeadDoneHostRead
