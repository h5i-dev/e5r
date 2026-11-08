import Projects.thermostat.MainChunkCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainChunkInit
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (fp start : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (fp+492#32) (0#32) .w) (fp+496#32) (0#32) .w) (fp+500#32) (0#32) .w) (fp+504#32) (0#32) .w) (fp+476#32) (0#32) .w) (fp+480#32) (0#32) .w) (fp+484#32) (0#32) .w) (fp+488#32) (0#32) .w) (fp+452#32) (start) .w) (fp+456#32) (start) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fp start : Word) (h8 : c.get 8=fp) (h23 : c.get 23=fp+476#32) (h20 : c.get 20=start) (hm : Memory.Block B fp 508) (ha : fp.toNat%4=0)
    (hp : c.pc=0x80000e54#32) :
    ∃ d, Quiet.Steps B img 12 ⟨c,ram⟩ ⟨d,memory ram fp start⟩ ∧ d.pc=0x80000e9a#32 ∧
      d.get 24=start ∧ (∀ r : Reg, r≠24 → d.get r=c.get r) ∧ d.sameCsr c := by
  let r1 := ramWrite ram (fp+492#32) (0#32) .w
  let c1 := c.goto 0x80000e58#32
  let r2 := ramWrite r1 (fp+496#32) (0#32) .w
  let c2 := c1.goto 0x80000e5c#32
  let r3 := ramWrite r2 (fp+500#32) (0#32) .w
  let c3 := c2.goto 0x80000e60#32
  let r4 := ramWrite r3 (fp+504#32) (0#32) .w
  let c4 := c3.goto 0x80000e64#32
  let r5 := ramWrite r4 (fp+476#32) (0#32) .w
  let c5 := c4.goto 0x80000e68#32
  let r6 := ramWrite r5 (fp+480#32) (0#32) .w
  let c6 := c5.goto 0x80000e6c#32
  let r7 := ramWrite r6 (fp+484#32) (0#32) .w
  let c7 := c6.goto 0x80000e70#32
  let r8 := ramWrite r7 (fp+488#32) (0#32) .w
  let c8 := c7.goto 0x80000e74#32
  let r9 := ramWrite r8 (fp+452#32) (start) .w
  let c9 := c8.goto 0x80000e78#32
  let r10 := ramWrite r9 (fp+456#32) (start) .w
  let c10 := c9.goto 0x80000e7c#32
  let c11 := c10.wr 24 (start) 0x80000e7e#32
  let c12 := c11.goto 0x80000e9a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,r1⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact cc2147487316) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 r1 [],[]⟩
    have v23 : c.get 23=fp+476#32 := by simp [Core.wr_get_ne,Core.wr_get,h8,h23,h20]
    rw [exec_store,v23,Core.get_zero,BitVec.add_assoc,show 476#32+16#32=492#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 123 ha)
        (Memory.block_access hm (off := 492) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,r1⟩ ⟨c2,r2⟩ := by
    refine Quiet.step_of (by change (0x80000e58#32).getLsbD 0=false;decide) cc2147487320 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) r1 0 [] [] = ⟨.ok c2 r2 [],[]⟩
    have v23 : c1.get 23=fp+476#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h23,h20]
    rw [exec_store,v23,Core.get_zero,BitVec.add_assoc,show 476#32+20#32=496#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 124 ha)
        (Memory.block_access hm (off := 496) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r2⟩ ⟨c3,r3⟩ := by
    refine Quiet.step_of (by change (0x80000e5c#32).getLsbD 0=false;decide) cc2147487324 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r2 0 [] [] = ⟨.ok c3 r3 [],[]⟩
    have v23 : c2.get 23=fp+476#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23,h20]
    rw [exec_store,v23,Core.get_zero,BitVec.add_assoc,show 476#32+24#32=500#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 125 ha)
        (Memory.block_access hm (off := 500) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r3⟩ ⟨c4,r4⟩ := by
    refine Quiet.step_of (by change (0x80000e60#32).getLsbD 0=false;decide) cc2147487328 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r3 0 [] [] = ⟨.ok c4 r4 [],[]⟩
    have v23 : c3.get 23=fp+476#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23,h20]
    rw [exec_store,v23,Core.get_zero,BitVec.add_assoc,show 476#32+28#32=504#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 126 ha)
        (Memory.block_access hm (off := 504) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r4⟩ ⟨c5,r5⟩ := by
    refine Quiet.step_of (by change (0x80000e64#32).getLsbD 0=false;decide) cc2147487332 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r4 0 [] [] = ⟨.ok c5 r5 [],[]⟩
    have v23 : c4.get 23=fp+476#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23,h20]
    rw [exec_store,v23,Core.get_zero,BitVec.add_assoc,show 476#32+0#32=476#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 119 ha)
        (Memory.block_access hm (off := 476) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r5⟩ ⟨c6,r6⟩ := by
    refine Quiet.step_of (by change (0x80000e68#32).getLsbD 0=false;decide) cc2147487336 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r5 0 [] [] = ⟨.ok c6 r6 [],[]⟩
    have v23 : c5.get 23=fp+476#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23,h20]
    rw [exec_store,v23,Core.get_zero,BitVec.add_assoc,show 476#32+4#32=480#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 120 ha)
        (Memory.block_access hm (off := 480) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r6⟩ ⟨c7,r7⟩ := by
    refine Quiet.step_of (by change (0x80000e6c#32).getLsbD 0=false;decide) cc2147487340 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r6 0 [] [] = ⟨.ok c7 r7 [],[]⟩
    have v23 : c6.get 23=fp+476#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23,h20]
    rw [exec_store,v23,Core.get_zero,BitVec.add_assoc,show 476#32+8#32=484#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 121 ha)
        (Memory.block_access hm (off := 484) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r7⟩ ⟨c8,r8⟩ := by
    refine Quiet.step_of (by change (0x80000e70#32).getLsbD 0=false;decide) cc2147487344 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r7 0 [] [] = ⟨.ok c8 r8 [],[]⟩
    have v23 : c7.get 23=fp+476#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23,h20]
    rw [exec_store,v23,Core.get_zero,BitVec.add_assoc,show 476#32+12#32=488#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 122 ha)
        (Memory.block_access hm (off := 488) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r8⟩ ⟨c9,r9⟩ := by
    refine Quiet.step_of (by change (0x80000e74#32).getLsbD 0=false;decide) cc2147487348 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r8 0 [] [] = ⟨.ok c9 r9 [],[]⟩
    have v8 : c8.get 8=fp := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23,h20]
    have v20 : c8.get 20=start := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23,h20]
    rw [exec_store,v8,v20,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned fp 113 ha) (Memory.block_access hm (off := 452) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r9⟩ ⟨c10,r10⟩ := by
    refine Quiet.step_of (by change (0x80000e78#32).getLsbD 0=false;decide) cc2147487352 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r9 0 [] [] = ⟨.ok c10 r10 [],[]⟩
    have v8 : c9.get 8=fp := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23,h20]
    have v20 : c9.get 20=start := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23,h20]
    rw [exec_store,v8,v20,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned fp 114 ha) (Memory.block_access hm (off := 456) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r10⟩ ⟨c11,r10⟩ := by
    refine Quiet.step_of (by change (0x80000e7c#32).getLsbD 0=false;decide) cc2147487356 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r10 0 [] [] = ⟨.ok c11 r10 [],[]⟩
    have v20 : c10.get 20=start := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23,h20]
    rw [exec_op,Core.get_zero,v20,(show alu .add (0 : Word) start=start from BitVec.zero_add _)];rfl
  have t11 : Quiet.Step B img ⟨c11,r10⟩ ⟨c12,r10⟩ := by
    refine Quiet.step_of (by change (0x80000e7e#32).getLsbD 0=false;decide) cc2147487358 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r10 0 [] [] = ⟨.ok c12 r10 [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c11 (c11.pc+28#32)) r10 0 [] [] = _
    rw [show c11.pc=0x80000e7e#32 by rfl,show 0x80000e7e#32+28#32=0x80000e9a#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c12,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.single t11))))))))))),rfl,?_ ,?_ ,by rfl⟩
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23,h20]
  · intro reg h24;simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23,h20,h24]
end E5R.Thermostat.MainChunkInit
