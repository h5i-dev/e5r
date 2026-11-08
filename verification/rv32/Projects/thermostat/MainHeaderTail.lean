import Projects.thermostat.FrameOffsets
import Projects.thermostat.MainHeaderCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainHeaderTail
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (fp filled : Word) :=
  ramWrite (ramWrite (ram) (fp+464#32) (1#32) .b) ((fp+84#32)+0#32) (filled+1#32) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fp filled : Word) (h8 : c.get 8=fp) (h22 : c.get 22=1#32) (h436 : ramRead ram (fp+436#32) .w=fp+84#32)
(h84 : ramRead ram (fp+84#32) .w=filled) (h112 : ramRead ram (fp+112#32) .w=2048#32)
(object : Memory.Block B fp 465) (aligned : fp.toNat%4=0)
    (hp : c.pc=0x80000bb2#32) :
    ∃ d, Quiet.Steps B img 8 ⟨c,ram⟩ ⟨d,memory ram fp filled⟩ ∧ d.pc=0x80000bc8#32 ∧
      d.get 10=fp+84#32 ∧ d.get 11=filled+1#32 ∧ d.get 14=2048#32 ∧ d.get 12=filled+1#32 ∧ (∀ r : Reg, r≠10 → r≠11 → r≠14 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let r1 := ramWrite ram (fp+464#32) (1#32) .b
  let c1 := c.goto 0x80000bb6#32
  let c2 := c1.wr 10 (fp+84#32) 0x80000bba#32
  let c3 := c2.wr 11 (filled) 0x80000bbc#32
  let c4 := c3.wr 11 (filled+1#32) 0x80000bbe#32
  let r2 := ramWrite r1 ((fp+84#32)+0#32) (filled+1#32) .w
  let c5 := c4.goto 0x80000bc0#32
  let c6 := c5.wr 10 (fp+84#32) 0x80000bc4#32
  let c7 := c6.wr 14 (2048#32) 0x80000bc6#32
  let c8 := c7.wr 12 (filled+1#32) 0x80000bc8#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,r1⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact mh2147486642) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 r1 [],[]⟩
    rw [exec_store,h8,h22,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access object (off := 464) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,r1⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x80000bb6#32).getLsbD 0=false;decide) mh2147486646 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) r1 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v8 : c1.get 8=fp := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h22]
    have input : ramRead r1 (fp+436#32) .w=ramRead ram (fp+436#32) .w := by
      dsimp only [r1]
      exact FrameOffsets.word ram fp 1#32 436 464 .b (by decide) (by decide) (by decide)
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 109 aligned)
     (Memory.block_access object (off := 436) (by decide) (by decide)),input,h436];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r1⟩ := by
    refine Quiet.step_of (by change (0x80000bba#32).getLsbD 0=false;decide) mh2147486650 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r1 [],[]⟩
    have v10 : c2.get 10=fp+84#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22]
    have input : ramRead r1 (fp+84#32) .w=ramRead ram (fp+84#32) .w := by
      dsimp only [r1]
      exact FrameOffsets.word ram fp 1#32 84 464 .b (by decide) (by decide) (by decide)
    rw [exec_load,v10,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 21 aligned) (Memory.block_access object (off := 84) (by decide) (by decide)),input,h84];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r1⟩ ⟨c4,r1⟩ := by
    refine Quiet.step_of (by change (0x80000bbc#32).getLsbD 0=false;decide) mh2147486652 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r1 0 [] [] = ⟨.ok c4 r1 [],[]⟩
    have v11 : c3.get 11=filled := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22]
    rw [exec_opimm,v11];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r1⟩ ⟨c5,r2⟩ := by
    refine Quiet.step_of (by change (0x80000bbe#32).getLsbD 0=false;decide) mh2147486654 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r1 0 [] [] = ⟨.ok c5 r2 [],[]⟩
    have v10 : c4.get 10=fp+84#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22]
    have v11 : c4.get 11=filled+1#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22]
    rw [exec_store,v10,v11,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (by simpa only [Width.bytes,BitVec.add_zero] using Memory.word_aligned fp 21 aligned) (by simpa only [Width.bytes,BitVec.add_zero] using Memory.block_access object (off := 84) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r2⟩ ⟨c6,r2⟩ := by
    refine Quiet.step_of (by change (0x80000bc0#32).getLsbD 0=false;decide) mh2147486656 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r2 0 [] [] = ⟨.ok c6 r2 [],[]⟩
    have v8 : c5.get 8=fp := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22]
    have input : ramRead r2 (fp+436#32) .w=ramRead ram (fp+436#32) .w := by
      dsimp only [r2,r1]
      simp only [BitVec.add_zero]
      rw [FrameOffsets.word _ fp (filled+1#32) 436 84 .w (by decide) (by decide) (by decide)]
      exact FrameOffsets.word ram fp 1#32 436 464 .b (by decide) (by decide) (by decide)
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 109 aligned)
     (Memory.block_access object (off := 436) (by decide) (by decide)),input,h436];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r2⟩ ⟨c7,r2⟩ := by
    refine Quiet.step_of (by change (0x80000bc4#32).getLsbD 0=false;decide) mh2147486660 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r2 0 [] [] = ⟨.ok c7 r2 [],[]⟩
    have v8 : c6.get 8=fp := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22]
    have input : ramRead r2 (fp+112#32) .w=ramRead ram (fp+112#32) .w := by
      dsimp only [r2,r1]
      simp only [BitVec.add_zero]
      rw [FrameOffsets.word _ fp (filled+1#32) 112 84 .w (by decide) (by decide) (by decide)]
      exact FrameOffsets.word ram fp 1#32 112 464 .b (by decide) (by decide) (by decide)
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 28 aligned)
     (Memory.block_access object (off := 112) (by decide) (by decide)),input,h112];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r2⟩ ⟨c8,r2⟩ := by
    refine Quiet.step_of (by change (0x80000bc6#32).getLsbD 0=false;decide) mh2147486662 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r2 0 [] [] = ⟨.ok c8 r2 [],[]⟩
    have v10 : c7.get 10=fp+84#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22]
    rw [exec_load,v10,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 21 aligned) (Memory.block_access object (off := 84) (by decide) (by decide))]
    have input : ramRead r2 (fp+84#32) .w=filled+1#32 := by dsimp only [r2];simp only [BitVec.add_zero];exact ramRead_ramWrite_w _ _ _
    rw [input];first | rfl | (rw [hp];rfl)
  refine ⟨c8,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.single t7))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22]
  · intro reg h10 h11 h14 h12;simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22,h10,h11,h14,h12]
end E5R.Thermostat.MainHeaderTail
