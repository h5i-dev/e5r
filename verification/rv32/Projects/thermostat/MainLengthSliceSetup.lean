import Projects.thermostat.MainLengthCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainLengthSliceSetup
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (fp filled buf waker : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ram) (fp+456#32) (waker) .w) (fp+460#32) (buf+filled) .w) (fp+464#32) (2048#32-filled) .w) (fp+468#32) (0#32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fp filled buf waker : Word) (h8 : c.get 8=fp) (h10 : c.get 10=filled) (h11 : c.get 11=2048#32)
(h108 : ramRead ram (fp+108#32) .w=buf) (h440 : ramRead ram (fp+440#32) .w=waker)
(object : Memory.Block B fp 469) (aligned : fp.toNat%4=0)
    (hp : c.pc=0x80000c44#32) :
    ∃ d, Quiet.Steps B img 8 ⟨c,ram⟩ ⟨d,memory ram fp filled buf waker⟩ ∧ d.pc=0x80000c60#32 ∧
      d.get 12=buf+filled ∧ d.get 13=waker ∧ d.get 14=2048#32-filled ∧ (∀ r : Reg, r≠12 → r≠13 → r≠14 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (buf) 0x80000c46#32
  let c2 := c1.wr 13 (waker) 0x80000c4a#32
  let c3 := c2.wr 14 (2048#32-filled) 0x80000c4e#32
  let c4 := c3.wr 12 (buf+filled) 0x80000c50#32
  let r1 := ramWrite ram (fp+456#32) (waker) .w
  let c5 := c4.goto 0x80000c54#32
  let r2 := ramWrite r1 (fp+460#32) (buf+filled) .w
  let c6 := c5.goto 0x80000c58#32
  let r3 := ramWrite r2 (fp+464#32) (2048#32-filled) .w
  let c7 := c6.goto 0x80000c5c#32
  let r4 := ramWrite r3 (fp+468#32) (0#32) .b
  let c8 := c7.goto 0x80000c60#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact ml2147486788) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=fp := by simp [Core.wr_get_ne,Core.wr_get,h8,h10,h11]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 27 aligned) (Memory.block_access object (off := 108) (by decide) (by decide)),h108];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000c46#32).getLsbD 0=false;decide) ml2147486790 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=fp := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 110 aligned) (Memory.block_access object (off := 440) (by decide) (by decide)),h440];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000c4a#32).getLsbD 0=false;decide) ml2147486794 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v11 : c2.get 11=2048#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11]
    have v10 : c2.get 10=filled := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11]
    rw [exec_op,v11,v10];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000c4e#32).getLsbD 0=false;decide) ml2147486798 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v12 : c3.get 12=buf := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11]
    have v10 : c3.get 10=filled := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11]
    rw [exec_op,v12,v10];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,r1⟩ := by
    refine Quiet.step_of (by change (0x80000c50#32).getLsbD 0=false;decide) ml2147486800 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 r1 [],[]⟩
    have v8 : c4.get 8=fp := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11]
    have v13 : c4.get 13=waker := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11]
    rw [exec_store,v8,v13,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 114 aligned) (Memory.block_access object (off := 456) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r1⟩ ⟨c6,r2⟩ := by
    refine Quiet.step_of (by change (0x80000c54#32).getLsbD 0=false;decide) ml2147486804 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r1 0 [] [] = ⟨.ok c6 r2 [],[]⟩
    have v8 : c5.get 8=fp := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11]
    have v12 : c5.get 12=buf+filled := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11]
    rw [exec_store,v8,v12,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 115 aligned) (Memory.block_access object (off := 460) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r2⟩ ⟨c7,r3⟩ := by
    refine Quiet.step_of (by change (0x80000c58#32).getLsbD 0=false;decide) ml2147486808 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r2 0 [] [] = ⟨.ok c7 r3 [],[]⟩
    have v8 : c6.get 8=fp := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11]
    have v14 : c6.get 14=2048#32-filled := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11]
    rw [exec_store,v8,v14,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 116 aligned) (Memory.block_access object (off := 464) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r3⟩ ⟨c8,r4⟩ := by
    refine Quiet.step_of (by change (0x80000c5c#32).getLsbD 0=false;decide) ml2147486812 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r3 0 [] [] = ⟨.ok c8 r4 [],[]⟩
    have v8 : c7.get 8=fp := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11]
    rw [exec_store,v8,Core.get_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access object (off := 468) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c8,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.single t7))))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11]
  · intro reg h12 h13 h14;simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h12,h13,h14]
end E5R.Thermostat.MainLengthSliceSetup
