import Projects.thermostat.FrameOffsets
import Projects.thermostat.SuccessNextCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ChunkNextStores
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp ms me ts te high0 high1 high2 : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+28#32) (ms) .w) (sp+24#32) (me) .w) (sp+36#32) (ts) .w) (sp+32#32) (te) .w) (sp+5168#32) (alu .or high0 (alu .sll high1 16#32)) .w) (sp+5172#32) (high2) .h

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp ms me ts te high0 high1 high2 : Word) (h2 : c.get 2=sp) (h8 : c.get 8=sp+3204#32) (h10 : c.get 10=high0) (h11 : c.get 11=high1) (h12 : c.get 12=high2)
(hms : ramRead ram (sp+3336#32) .w=ms)
(hme : ramRead ram (sp+3340#32) .w=me)
(hts : ramRead ram (sp+3344#32) .w=ts)
(hte : ramRead ram (sp+3348#32) .w=te)
(stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
    (hp : c.pc=0x8000108e#32) :
    ∃ d, Quiet.Steps B img 12 ⟨c,ram⟩ ⟨d,memory ram sp ms me ts te high0 high1 high2⟩ ∧ d.pc=0x800010b2#32 ∧
      d.get 13=te ∧ d.get 11=alu .sll high1 16#32 ∧ d.get 10=alu .or high0 (alu .sll high1 16#32) ∧ (∀ r : Reg, r≠13 → r≠11 → r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 13 (ms) 0x80001092#32
  let r1 := ramWrite ram (sp+28#32) (ms) .w
  let c2 := c1.goto 0x80001094#32
  let c3 := c2.wr 13 (me) 0x80001098#32
  let r2 := ramWrite r1 (sp+24#32) (me) .w
  let c4 := c3.goto 0x8000109a#32
  let c5 := c4.wr 13 (ts) 0x8000109e#32
  let r3 := ramWrite r2 (sp+36#32) (ts) .w
  let c6 := c5.goto 0x800010a0#32
  let c7 := c6.wr 13 (te) 0x800010a4#32
  let r4 := ramWrite r3 (sp+32#32) (te) .w
  let c8 := c7.goto 0x800010a6#32
  let c9 := c8.wr 11 (alu .sll high1 16#32) 0x800010a8#32
  let c10 := c9.wr 10 (alu .or high0 (alu .sll high1 16#32)) 0x800010aa#32
  let r5 := ramWrite r4 (sp+5168#32) (alu .or high0 (alu .sll high1 16#32)) .w
  let c11 := c10.goto 0x800010ae#32
  let r6 := ramWrite r5 (sp+5172#32) (high2) .h
  let c12 := c11.goto 0x800010b2#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact xn2147487886) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=sp+3204#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+132#32=3336#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 834 aligned) (Memory.block_access stack (off := 3336) (by decide) (by decide)),hms];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x80001092#32).getLsbD 0=false;decide) xn2147487890 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
    have v13 : c1.get 13=ms := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
    rw [exec_store,v2,v13,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 7 aligned) (Memory.block_access stack (off := 28) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r1⟩ := by
    refine Quiet.step_of (by change (0x80001094#32).getLsbD 0=false;decide) xn2147487892 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r1 [],[]⟩
    have v8 : c2.get 8=sp+3204#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
    have input : ramRead r1 (sp+3340#32) .w=ramRead ram (sp+3340#32) .w := by
      dsimp only [r1]
      rw [FrameOffsets.word _ sp (ms) 3340 28 .w (by decide) (by decide) (by decide)]
      try rfl
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+136#32=3340#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 835 aligned) (Memory.block_access stack (off := 3340) (by decide) (by decide)),input,hme];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r1⟩ ⟨c4,r2⟩ := by
    refine Quiet.step_of (by change (0x80001098#32).getLsbD 0=false;decide) xn2147487896 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r1 0 [] [] = ⟨.ok c4 r2 [],[]⟩
    have v2 : c3.get 2=sp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
    have v13 : c3.get 13=me := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
    rw [exec_store,v2,v13,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 6 aligned) (Memory.block_access stack (off := 24) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r2⟩ ⟨c5,r2⟩ := by
    refine Quiet.step_of (by change (0x8000109a#32).getLsbD 0=false;decide) xn2147487898 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r2 0 [] [] = ⟨.ok c5 r2 [],[]⟩
    have v8 : c4.get 8=sp+3204#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
    have input : ramRead r2 (sp+3344#32) .w=ramRead ram (sp+3344#32) .w := by
      dsimp only [r2,r1]
      rw [FrameOffsets.word _ sp (me) 3344 24 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ sp (ms) 3344 28 .w (by decide) (by decide) (by decide)]
      try rfl
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+140#32=3344#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 836 aligned) (Memory.block_access stack (off := 3344) (by decide) (by decide)),input,hts];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r2⟩ ⟨c6,r3⟩ := by
    refine Quiet.step_of (by change (0x8000109e#32).getLsbD 0=false;decide) xn2147487902 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r2 0 [] [] = ⟨.ok c6 r3 [],[]⟩
    have v2 : c5.get 2=sp := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
    have v13 : c5.get 13=ts := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
    rw [exec_store,v2,v13,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 9 aligned) (Memory.block_access stack (off := 36) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r3⟩ ⟨c7,r3⟩ := by
    refine Quiet.step_of (by change (0x800010a0#32).getLsbD 0=false;decide) xn2147487904 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r3 0 [] [] = ⟨.ok c7 r3 [],[]⟩
    have v8 : c6.get 8=sp+3204#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
    have input : ramRead r3 (sp+3348#32) .w=ramRead ram (sp+3348#32) .w := by
      dsimp only [r3,r2,r1]
      rw [FrameOffsets.word _ sp (ts) 3348 36 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ sp (me) 3348 24 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ sp (ms) 3348 28 .w (by decide) (by decide) (by decide)]
      try rfl
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+144#32=3348#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 837 aligned) (Memory.block_access stack (off := 3348) (by decide) (by decide)),input,hte];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r3⟩ ⟨c8,r4⟩ := by
    refine Quiet.step_of (by change (0x800010a4#32).getLsbD 0=false;decide) xn2147487908 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r3 0 [] [] = ⟨.ok c8 r4 [],[]⟩
    have v2 : c7.get 2=sp := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
    have v13 : c7.get 13=te := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
    rw [exec_store,v2,v13,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 8 aligned) (Memory.block_access stack (off := 32) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r4⟩ ⟨c9,r4⟩ := by
    refine Quiet.step_of (by change (0x800010a6#32).getLsbD 0=false;decide) xn2147487910 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r4 0 [] [] = ⟨.ok c9 r4 [],[]⟩
    have v11 : c8.get 11=high1 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
    rw [exec_opimm,v11];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r4⟩ ⟨c10,r4⟩ := by
    refine Quiet.step_of (by change (0x800010a8#32).getLsbD 0=false;decide) xn2147487912 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r4 0 [] [] = ⟨.ok c10 r4 [],[]⟩
    have v10 : c9.get 10=high0 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
    have v11 : c9.get 11=alu .sll high1 16#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
    rw [exec_op,v10,v11];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r4⟩ ⟨c11,r5⟩ := by
    refine Quiet.step_of (by change (0x800010aa#32).getLsbD 0=false;decide) xn2147487914 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r4 0 [] [] = ⟨.ok c11 r5 [],[]⟩
    have v8 : c10.get 8=sp+3204#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
    have v10 : c10.get 10=alu .or high0 (alu .sll high1 16#32) := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
    rw [exec_store,v8,v10,BitVec.add_assoc,show 3204#32+1964#32=5168#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1292 aligned) (Memory.block_access stack (off := 5168) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r5⟩ ⟨c12,r6⟩ := by
    refine Quiet.step_of (by change (0x800010ae#32).getLsbD 0=false;decide) xn2147487918 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r5 0 [] [] = ⟨.ok c12 r6 [],[]⟩
    have v8 : c11.get 8=sp+3204#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
    have v12 : c11.get 12=high2 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
    rw [exec_store,v8,v12,BitVec.add_assoc,show 3204#32+1968#32=5172#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 2586 (by omega)) (Memory.block_access stack (off := 5172) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c12,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.single t11))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12]
  · intro reg h13 h11 h10;simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h12,h13,h11,h10]
end E5R.Thermostat.ChunkNextStores
