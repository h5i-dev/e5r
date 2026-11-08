import Projects.thermostat.FrameOffsets
import Projects.thermostat.MainLengthCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainLengthStart
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (fp body len filled : Word) :=
  ramWrite (ram) (fp+452#32) (body+len) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fp body len filled : Word) (h8 : c.get 8=fp) (h20 : c.get 20=len)
(h124 : ramRead ram (fp+124#32) .w=body) (h436 : ramRead ram (fp+436#32) .w=fp+84#32)
(h84 : ramRead ram (fp+84#32) .w=filled) (object : Memory.Block B fp 456) (aligned : fp.toNat%4=0)
    (hp : c.pc=0x80000c26#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,memory ram fp body len filled⟩ ∧ d.pc=0x80000c36#32 ∧
      d.get 25=body+len ∧ d.get 10=filled ∧ (∀ r : Reg, r≠25 → r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 25 (body) 0x80000c2a#32
  let c2 := c1.wr 10 (fp+84#32) 0x80000c2e#32
  let c3 := c2.wr 25 (body+len) 0x80000c30#32
  let r1 := ramWrite ram (fp+452#32) (body+len) .w
  let c4 := c3.goto 0x80000c34#32
  let c5 := c4.wr 10 (filled) 0x80000c36#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact ml2147486758) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=fp := by simp [Core.wr_get_ne,Core.wr_get,h8,h20]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 31 aligned) (Memory.block_access object (off := 124) (by decide) (by decide)),h124];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000c2a#32).getLsbD 0=false;decide) ml2147486762 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=fp := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h20]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 109 aligned) (Memory.block_access object (off := 436) (by decide) (by decide)),h436];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000c2e#32).getLsbD 0=false;decide) ml2147486766 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v25 : c2.get 25=body := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
    have v20 : c2.get 20=len := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
    rw [exec_op,v25,v20];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,r1⟩ := by
    refine Quiet.step_of (by change (0x80000c30#32).getLsbD 0=false;decide) ml2147486768 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 r1 [],[]⟩
    have v8 : c3.get 8=fp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
    have v25 : c3.get 25=body+len := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
    rw [exec_store,v8,v25,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 113 aligned) (Memory.block_access object (off := 452) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r1⟩ ⟨c5,r1⟩ := by
    refine Quiet.step_of (by change (0x80000c34#32).getLsbD 0=false;decide) ml2147486772 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r1 0 [] [] = ⟨.ok c5 r1 [],[]⟩
    have v10 : c4.get 10=fp+84#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
    rw [exec_load,v10,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 21 aligned) (Memory.block_access object (off := 84) (by decide) (by decide))]
    have input : ramRead r1 (fp+84#32) .w=filled := by
      dsimp only [r1]
      rw [FrameOffsets.word ram fp (body+len) 84 452 .w (by decide) (by decide) (by decide)]
      exact h84
    rw [input];first | rfl | (rw [hp];rfl)
  refine ⟨c5,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
  · intro reg h25 h10;simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20,h25,h10]
end E5R.Thermostat.MainLengthStart
