import Projects.thermostat.MainHeadCopyCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainBodyHeadLoad
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (fp len tag : Word) :=
  ramWrite (ram) (fp+444#32) (len) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fp len tag : Word) (h8 : c.get 8=fp) (h408 : ramRead ram (fp+408#32) .w=len) (h116 : ramRead ram (fp+116#32) .w=tag) (object : Memory.Block B fp 448) (aligned : fp.toNat%4=0)
    (hp : c.pc=0x80000c14#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,memory ram fp len tag⟩ ∧ d.pc=0x80000c1e#32 ∧
      d.get 20=len ∧ d.get 9=tag ∧ (∀ r : Reg, r≠20 → r≠9 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 20 (len) 0x80000c18#32
  let c2 := c1.wr 9 (tag) 0x80000c1a#32
  let r1 := ramWrite ram (fp+444#32) (len) .w
  let c3 := c2.goto 0x80000c1e#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hc2147486740) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=fp := by simp [Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 102 aligned) (Memory.block_access object (off := 408) (by decide) (by decide)),h408];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000c18#32).getLsbD 0=false;decide) hc2147486744 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=fp := by simp [c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 29 aligned) (Memory.block_access object (off := 116) (by decide) (by decide)),h116];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,r1⟩ := by
    refine Quiet.step_of (by change (0x80000c1a#32).getLsbD 0=false;decide) hc2147486746 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 r1 [],[]⟩
    have v8 : c2.get 8=fp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    have v20 : c2.get 20=len := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_store,v8,v20,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 111 aligned) (Memory.block_access object (off := 444) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · intro reg h20 h9;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20,h9]
end E5R.Thermostat.MainBodyHeadLoad
