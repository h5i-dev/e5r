import Projects.thermostat.UartWriteCode
import Projects.thermostat.QuietRam
import Projects.thermostat.UartWriteActiveData
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.UartWriteActive
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (obj io src len : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ram) (obj+24#32) (io) .w) (obj+28#32) (src) .w) (obj+32#32) (len) .w) (obj+36#32) (0#32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (obj io src len : Word) (h10 : c.get 10=obj) (h11 : c.get 11=src) (h12 : c.get 12=len) (hne : len≠0#32)
    (hm : Memory.Block B obj 41) (ha : obj.toNat%4=0) (hslot : ramRead ram (obj+12#32) .w=io)
    (hp : c.pc=0x800007ce#32) :
    ∃ d, Quiet.Steps B img 11 ⟨c,ram⟩ ⟨d,memory ram obj io src len⟩ ∧ d.pc=0x800007f4#32 ∧
      d.get 14=src+len ∧ d.get 11=len ∧ d.get 12=src ∧ d.get 15=0x10000000#32 ∧ (∀ r : Reg, r≠14 → r≠11 → r≠12 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (io) 0x800007d0#32
  let r1 := ramWrite ram (obj+24#32) (io) .w
  let c2 := c1.goto 0x800007d2#32
  let r2 := ramWrite r1 (obj+28#32) (src) .w
  let c3 := c2.goto 0x800007d4#32
  let r3 := ramWrite r2 (obj+32#32) (len) .w
  let c4 := c3.goto 0x800007d6#32
  let r4 := ramWrite r3 (obj+36#32) (0#32) .b
  let c5 := c4.goto 0x800007da#32
  let c6 := c5.wr 11 (len) 0x800007dc#32
  let c7 := c6.goto 0x800007de#32
  let c8 := c7.wr 12 (src) 0x800007e0#32
  let c9 := c8.wr 14 (src+len) 0x800007e4#32
  let c10 := c9.wr 15 (0x10000000#32) 0x800007e8#32
  let c11 := c10.goto 0x800007f4#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact uw2147485646) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have hv : c.get 10=obj := by simp [Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_load,hv,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide))]
    have hvread : ramRead ram (obj+12#32) .w=io := hslot
    rw [hvread];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x800007d0#32).getLsbD 0=false;decide) uw2147485648 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have vo : c1.get 10=obj := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    have vv : c1.get 14=io := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_store,vo,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 6 ha) (Memory.block_access hm (off := 24) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine Quiet.step_of (by change (0x800007d2#32).getLsbD 0=false;decide) uw2147485650 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r2 [],[]⟩
    have vo : c2.get 10=obj := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    have vv : c2.get 11=src := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_store,vo,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 7 ha) (Memory.block_access hm (off := 28) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r3⟩ := by
    refine Quiet.step_of (by change (0x800007d4#32).getLsbD 0=false;decide) uw2147485652 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r2 0 [] [] = ⟨.ok c4 r3 [],[]⟩
    have vo : c3.get 10=obj := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    have vv : c3.get 12=len := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_store,vo,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 8 ha) (Memory.block_access hm (off := 32) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r3⟩ ⟨c5,r4⟩ := by
    refine Quiet.step_of (by change (0x800007d6#32).getLsbD 0=false;decide) uw2147485654 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r3 0 [] [] = ⟨.ok c5 r4 [],[]⟩
    have vo : c4.get 10=obj := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_store,vo,Core.get_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 36) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r4⟩ ⟨c6,r4⟩ := by
    refine Quiet.step_of (by change (0x800007da#32).getLsbD 0=false;decide) uw2147485658 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r4 0 [] [] = ⟨.ok c6 r4 [],[]⟩
    have hv : c5.get 10=obj := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_load,hv,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 8 ha) (Memory.block_access hm (off := 32) (by decide) (by decide))]
    have hvread : ramRead r4 (obj+32#32) .w=len := UartWriteActiveData.length ram obj io src len
    rw [hvread];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r4⟩ ⟨c7,r4⟩ := by
    refine Quiet.step_of (by change (0x800007dc#32).getLsbD 0=false;decide) uw2147485660 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r4 0 [] [] = ⟨.ok c7 r4 [],[]⟩
    have hv : c6.get 11=len := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_branch,hv,Core.get_zero,show taken .eq len (0 : Word)=false by simp [taken,hne]]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r4⟩ ⟨c8,r4⟩ := by
    refine Quiet.step_of (by change (0x800007de#32).getLsbD 0=false;decide) uw2147485662 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r4 0 [] [] = ⟨.ok c8 r4 [],[]⟩
    have hv : c7.get 10=obj := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_load,hv,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 7 ha) (Memory.block_access hm (off := 28) (by decide) (by decide))]
    have hvread : ramRead r4 (obj+28#32) .w=src := UartWriteActiveData.source ram obj io src len
    rw [hvread];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r4⟩ ⟨c9,r4⟩ := by
    refine Quiet.step_of (by change (0x800007e0#32).getLsbD 0=false;decide) uw2147485664 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r4 0 [] [] = ⟨.ok c9 r4 [],[]⟩
    have v12 : c8.get 12=src := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    have v11 : c8.get 11=len := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_op,v12,v11];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r4⟩ ⟨c10,r4⟩ := by
    refine Quiet.step_of (by change (0x800007e4#32).getLsbD 0=false;decide) uw2147485668 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r4 0 [] [] = ⟨.ok c10 r4 [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r4⟩ ⟨c11,r4⟩ := by
    refine Quiet.step_of (by change (0x800007e8#32).getLsbD 0=false;decide) uw2147485672 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r4 0 [] [] = ⟨.ok c11 r4 [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c10 0x800007f4#32) r4 0 [] [] = _
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c11,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.single t10)))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
  · intro reg h14 h11 h12 h15;simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h14,h11,h12,h15]
end E5R.Thermostat.UartWriteActive
