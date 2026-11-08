import Projects.thermostat.HeadDoneStoreGeometry
import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadDoneStore
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp tag low high method targetStart targetEnd count length minor : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) ((sp+4904#32)+0#32) (tag) .w) ((sp+4904#32)+4#32) (0#32) .w) ((sp+4904#32)+8#32) (low) .w) ((sp+4904#32)+12#32) (high) .w) ((sp+4904#32)+16#32) (0#32) .w) ((sp+4904#32)+20#32) (method) .w) ((sp+4904#32)+24#32) (targetStart) .w) ((sp+4904#32)+28#32) (targetEnd) .w) ((sp+4904#32)+288#32) (count) .w) ((sp+4904#32)+292#32) (length) .w) ((sp+4904#32)+296#32) (minor) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp tag low high method targetStart targetEnd count length minor : Word) (h2 : c.get 2=sp) (h21 : c.get 21=sp+4904#32) (hTag : c.get 20=tag) (h18 : c.get 18=low) (h19 : c.get 19=high) (h9 : c.get 9=count) (hLength : c.get 24=length) (h8 : c.get 8=minor)
(h20 : ramRead ram (sp+20#32) .w=method) (h24 : ramRead ram (sp+24#32) .w=targetStart) (h28 : ramRead ram (sp+28#32) .w=targetEnd)
(stack : Memory.Block B sp 56) (output : Memory.Block B (sp+4904#32) 297) (ha : sp.toNat%4=0)
    (hp : c.pc=0x8000349a#32) :
    ∃ d, Quiet.Steps B img 15 ⟨c,ram⟩ ⟨d,memory ram sp tag low high method targetStart targetEnd count length minor⟩ ∧ d.pc=0x80002d6a#32 ∧
      d.get 10=targetEnd ∧ (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let r1 := ramWrite ram ((sp+4904#32)+0#32) (tag) .w
  let c1 := c.goto 0x8000349e#32
  let r2 := ramWrite r1 ((sp+4904#32)+4#32) (0#32) .w
  let c2 := c1.goto 0x800034a2#32
  let r3 := ramWrite r2 ((sp+4904#32)+8#32) (low) .w
  let c3 := c2.goto 0x800034a6#32
  let r4 := ramWrite r3 ((sp+4904#32)+12#32) (high) .w
  let c4 := c3.goto 0x800034aa#32
  let r5 := ramWrite r4 ((sp+4904#32)+16#32) (0#32) .w
  let c5 := c4.goto 0x800034ae#32
  let c6 := c5.wr 10 (method) 0x800034b0#32
  let r6 := ramWrite r5 ((sp+4904#32)+20#32) (method) .w
  let c7 := c6.goto 0x800034b4#32
  let c8 := c7.wr 10 (targetStart) 0x800034b6#32
  let r7 := ramWrite r6 ((sp+4904#32)+24#32) (targetStart) .w
  let c9 := c8.goto 0x800034ba#32
  let c10 := c9.wr 10 (targetEnd) 0x800034bc#32
  let r8 := ramWrite r7 ((sp+4904#32)+28#32) (targetEnd) .w
  let c11 := c10.goto 0x800034c0#32
  let r9 := ramWrite r8 ((sp+4904#32)+288#32) (count) .w
  let c12 := c11.goto 0x800034c4#32
  let r10 := ramWrite r9 ((sp+4904#32)+292#32) (length) .w
  let c13 := c12.goto 0x800034c8#32
  let r11 := ramWrite r10 ((sp+4904#32)+296#32) (minor) .b
  let c14 := c13.goto 0x800034cc#32
  let c15 := c14.goto 0x80002d6a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,r1⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147497114) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 r1 [],[]⟩
    have v21 : c.get 21=sp+4904#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    have v20 : c.get 20=tag := by simp [Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    rw [exec_store,v21,v20,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned (sp+4904#32) 0 (Memory.word_aligned sp 1226 ha)) (Memory.block_access output (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,r1⟩ ⟨c2,r2⟩ := by
    refine Quiet.step_of (by change (0x8000349e#32).getLsbD 0=false;decide) hh2147497118 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) r1 0 [] [] = ⟨.ok c2 r2 [],[]⟩
    have v21 : c1.get 21=sp+4904#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    rw [exec_store,v21,Core.get_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned (sp+4904#32) 1 (Memory.word_aligned sp 1226 ha)) (Memory.block_access output (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r2⟩ ⟨c3,r3⟩ := by
    refine Quiet.step_of (by change (0x800034a2#32).getLsbD 0=false;decide) hh2147497122 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r2 0 [] [] = ⟨.ok c3 r3 [],[]⟩
    have v21 : c2.get 21=sp+4904#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    have v18 : c2.get 18=low := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    rw [exec_store,v21,v18,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned (sp+4904#32) 2 (Memory.word_aligned sp 1226 ha)) (Memory.block_access output (off := 8) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r3⟩ ⟨c4,r4⟩ := by
    refine Quiet.step_of (by change (0x800034a6#32).getLsbD 0=false;decide) hh2147497126 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r3 0 [] [] = ⟨.ok c4 r4 [],[]⟩
    have v21 : c3.get 21=sp+4904#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    have v19 : c3.get 19=high := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    rw [exec_store,v21,v19,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned (sp+4904#32) 3 (Memory.word_aligned sp 1226 ha)) (Memory.block_access output (off := 12) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r4⟩ ⟨c5,r5⟩ := by
    refine Quiet.step_of (by change (0x800034aa#32).getLsbD 0=false;decide) hh2147497130 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r4 0 [] [] = ⟨.ok c5 r5 [],[]⟩
    have v21 : c4.get 21=sp+4904#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    rw [exec_store,v21,Core.get_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned (sp+4904#32) 4 (Memory.word_aligned sp 1226 ha)) (Memory.block_access output (off := 16) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r5⟩ ⟨c6,r5⟩ := by
    refine Quiet.step_of (by change (0x800034ae#32).getLsbD 0=false;decide) hh2147497134 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r5 0 [] [] = ⟨.ok c6 r5 [],[]⟩
    have v2 : c5.get 2=sp := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 5 ha) (Memory.block_access stack (off := 20) (by decide) (by decide))]
    have source : ramRead r5 (sp+20#32) .w=method := by
      dsimp only [r5,r4,r3,r2,r1]
      rw [HeadDoneStoreGeometry.below _ sp _ 20 _ (by decide) (by decide)]
      rw [HeadDoneStoreGeometry.below _ sp _ 20 _ (by decide) (by decide)]
      rw [HeadDoneStoreGeometry.below _ sp _ 20 _ (by decide) (by decide)]
      rw [HeadDoneStoreGeometry.below _ sp _ 20 _ (by decide) (by decide)]
      rw [HeadDoneStoreGeometry.below _ sp _ 20 _ (by decide) (by decide)]
      exact h20
    rw [source];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r5⟩ ⟨c7,r6⟩ := by
    refine Quiet.step_of (by change (0x800034b0#32).getLsbD 0=false;decide) hh2147497136 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r5 0 [] [] = ⟨.ok c7 r6 [],[]⟩
    have v21 : c6.get 21=sp+4904#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    have v10 : c6.get 10=method := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    rw [exec_store,v21,v10,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned (sp+4904#32) 5 (Memory.word_aligned sp 1226 ha)) (Memory.block_access output (off := 20) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r6⟩ ⟨c8,r6⟩ := by
    refine Quiet.step_of (by change (0x800034b4#32).getLsbD 0=false;decide) hh2147497140 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r6 0 [] [] = ⟨.ok c8 r6 [],[]⟩
    have v2 : c7.get 2=sp := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 6 ha) (Memory.block_access stack (off := 24) (by decide) (by decide))]
    have source : ramRead r6 (sp+24#32) .w=targetStart := by
      dsimp only [r6,r5,r4,r3,r2,r1]
      rw [HeadDoneStoreGeometry.below _ sp _ 24 _ (by decide) (by decide)]
      rw [HeadDoneStoreGeometry.below _ sp _ 24 _ (by decide) (by decide)]
      rw [HeadDoneStoreGeometry.below _ sp _ 24 _ (by decide) (by decide)]
      rw [HeadDoneStoreGeometry.below _ sp _ 24 _ (by decide) (by decide)]
      rw [HeadDoneStoreGeometry.below _ sp _ 24 _ (by decide) (by decide)]
      rw [HeadDoneStoreGeometry.below _ sp _ 24 _ (by decide) (by decide)]
      exact h24
    rw [source];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r6⟩ ⟨c9,r7⟩ := by
    refine Quiet.step_of (by change (0x800034b6#32).getLsbD 0=false;decide) hh2147497142 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r6 0 [] [] = ⟨.ok c9 r7 [],[]⟩
    have v21 : c8.get 21=sp+4904#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    have v10 : c8.get 10=targetStart := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    rw [exec_store,v21,v10,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned (sp+4904#32) 6 (Memory.word_aligned sp 1226 ha)) (Memory.block_access output (off := 24) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r7⟩ ⟨c10,r7⟩ := by
    refine Quiet.step_of (by change (0x800034ba#32).getLsbD 0=false;decide) hh2147497146 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r7 0 [] [] = ⟨.ok c10 r7 [],[]⟩
    have v2 : c9.get 2=sp := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 7 ha) (Memory.block_access stack (off := 28) (by decide) (by decide))]
    have source : ramRead r7 (sp+28#32) .w=targetEnd := by
      dsimp only [r7,r6,r5,r4,r3,r2,r1]
      rw [HeadDoneStoreGeometry.below _ sp _ 28 _ (by decide) (by decide)]
      rw [HeadDoneStoreGeometry.below _ sp _ 28 _ (by decide) (by decide)]
      rw [HeadDoneStoreGeometry.below _ sp _ 28 _ (by decide) (by decide)]
      rw [HeadDoneStoreGeometry.below _ sp _ 28 _ (by decide) (by decide)]
      rw [HeadDoneStoreGeometry.below _ sp _ 28 _ (by decide) (by decide)]
      rw [HeadDoneStoreGeometry.below _ sp _ 28 _ (by decide) (by decide)]
      rw [HeadDoneStoreGeometry.below _ sp _ 28 _ (by decide) (by decide)]
      exact h28
    rw [source];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r7⟩ ⟨c11,r8⟩ := by
    refine Quiet.step_of (by change (0x800034bc#32).getLsbD 0=false;decide) hh2147497148 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r7 0 [] [] = ⟨.ok c11 r8 [],[]⟩
    have v21 : c10.get 21=sp+4904#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    have v10 : c10.get 10=targetEnd := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    rw [exec_store,v21,v10,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned (sp+4904#32) 7 (Memory.word_aligned sp 1226 ha)) (Memory.block_access output (off := 28) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r8⟩ ⟨c12,r9⟩ := by
    refine Quiet.step_of (by change (0x800034c0#32).getLsbD 0=false;decide) hh2147497152 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r8 0 [] [] = ⟨.ok c12 r9 [],[]⟩
    have v21 : c11.get 21=sp+4904#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    have v9 : c11.get 9=count := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    rw [exec_store,v21,v9,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned (sp+4904#32) 72 (Memory.word_aligned sp 1226 ha)) (Memory.block_access output (off := 288) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,r9⟩ ⟨c13,r10⟩ := by
    refine Quiet.step_of (by change (0x800034c4#32).getLsbD 0=false;decide) hh2147497156 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r9 0 [] [] = ⟨.ok c13 r10 [],[]⟩
    have v21 : c12.get 21=sp+4904#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    have v24 : c12.get 24=length := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    rw [exec_store,v21,v24,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned (sp+4904#32) 73 (Memory.word_aligned sp 1226 ha)) (Memory.block_access output (off := 292) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r10⟩ ⟨c14,r11⟩ := by
    refine Quiet.step_of (by change (0x800034c8#32).getLsbD 0=false;decide) hh2147497160 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r10 0 [] [] = ⟨.ok c14 r11 [],[]⟩
    have v21 : c13.get 21=sp+4904#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    have v8 : c13.get 8=minor := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
    rw [exec_store,v21,v8,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by change _%1=0;omega) (Memory.block_access output (off := 296) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,r11⟩ ⟨c15,r11⟩ := by
    refine Quiet.step_of (by change (0x800034cc#32).getLsbD 0=false;decide) hh2147497164 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) r11 0 [] [] = ⟨.ok c15 r11 [],[]⟩
    rw [exec_jal,Core.set_zero]
    change Observed.interp B img o (jump c14 (0x800034cc#32+0xfffff89e#32)) r11 0 [] []=_
    rw [show 0x800034cc#32+0xfffff89e#32=0x80002d6a#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c15,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.single t14)))))))))))))),rfl,?_ ,?_ ,by rfl⟩
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8]
  · intro reg h10;simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,hTag,h18,h19,h9,hLength,h8,h10]
end E5R.Thermostat.HeadDoneStore
