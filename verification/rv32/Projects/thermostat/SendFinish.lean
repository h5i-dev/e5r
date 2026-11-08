import Projects.thermostat.SendCode
import Projects.thermostat.QuietRam
import Projects.thermostat.StoreRead
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.SendFinish
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (obj res io flag : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (obj+48#32) (io) .w) (obj+52#32) (0#32) .w) (obj+52#32) (1#32) .b) (res+0#32) (0xffffffff#32) .w) (res+4#32) (flag) .w) (obj+45#32) (1#32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (obj res io flag : Word) (h8 : c.get 8=obj) (h9 : c.get 9=res) (hm : Memory.Block B obj 89) (ha : obj.toNat%4=0) (hr : Memory.Block B res 8) (hra : res.toNat%4=0) (hio : ramRead ram (obj+16#32) .w=io) (hflag : extend .b false (ramRead ram (obj+44#32) .b)=flag)
    (hp : c.pc=0x8000044e#32) :
    ∃ d, Quiet.Steps B img 11 ⟨c,ram⟩ ⟨d,memory ram obj res io flag⟩ ∧ d.pc=0x8000046e#32 ∧
      d.get 10=0xffffffff#32 ∧ d.get 22=flag ∧ d.get 11=1#32 ∧ (∀ r : Reg, r≠10 → r≠22 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (io) 0x80000450#32
  let r1 := ramWrite ram (obj+48#32) (io) .w
  let c2 := c1.goto 0x80000452#32
  let r2 := ramWrite r1 (obj+52#32) (0#32) .w
  let c3 := c2.goto 0x80000456#32
  let c4 := c3.wr 22 (flag) 0x8000045a#32
  let c5 := c4.wr 10 (1#32) 0x8000045c#32
  let r3 := ramWrite r2 (obj+52#32) (1#32) .b
  let c6 := c5.goto 0x80000460#32
  let c7 := c6.wr 10 (0xffffffff#32) 0x80000462#32
  let c8 := c7.wr 11 (1#32) 0x80000464#32
  let r4 := ramWrite r3 (res+0#32) (0xffffffff#32) .w
  let c9 := c8.goto 0x80000466#32
  let r5 := ramWrite r4 (res+4#32) (flag) .w
  let c10 := c9.goto 0x8000046a#32
  let r6 := ramWrite r5 (obj+45#32) (1#32) .b
  let c11 := c10.goto 0x8000046e#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact se2147484750) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=obj := by simp [Core.wr_get_ne,Core.wr_get,h8,h9]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 4 ha) (Memory.block_access hm (off := 16) (by decide) (by decide)),hio,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x80000450#32).getLsbD 0=false;decide) se2147484752 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v8 : c1.get 8=obj := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h9]
    have v10 : c1.get 10=io := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h9]
    rw [exec_store,v8,v10,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 12 ha) (Memory.block_access hm (off := 48) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine Quiet.step_of (by change (0x80000452#32).getLsbD 0=false;decide) se2147484754 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r2 [],[]⟩
    have v8 : c2.get 8=obj := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9]
    
    rw [exec_store,v8,Core.get_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 13 ha) (Memory.block_access hm (off := 52) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r2⟩ := by
    refine Quiet.step_of (by change (0x80000456#32).getLsbD 0=false;decide) se2147484758 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r2 0 [] [] = ⟨.ok c4 r2 [],[]⟩
    have v8 : c3.get 8=obj := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 44) (by decide) (by decide))]
    have he : ramRead r2 (obj+44#32) .b=ramRead ram (obj+44#32) .b := by
      change ramRead (ramWrite (ramWrite ram (obj+48#32) io .w) (obj+52#32) 0#32 .w) (obj+44#32) .b=_
      rw [StoreRead.other _ _ _ _ .b .w (StoreWords.offsets obj 44 1 52 4 (by decide) (by decide) (by decide)),StoreRead.other _ _ _ _ .b .w (StoreWords.offsets obj 44 1 48 4 (by decide) (by decide) (by decide))]
    rw [he,hflag];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r2⟩ ⟨c5,r2⟩ := by
    refine Quiet.step_of (by change (0x8000045a#32).getLsbD 0=false;decide) se2147484762 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r2 0 [] [] = ⟨.ok c5 r2 [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r2⟩ ⟨c6,r3⟩ := by
    refine Quiet.step_of (by change (0x8000045c#32).getLsbD 0=false;decide) se2147484764 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r2 0 [] [] = ⟨.ok c6 r3 [],[]⟩
    have v8 : c5.get 8=obj := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9]
    have v10 : c5.get 10=1#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9]
    rw [exec_store,v8,v10,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 52) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r3⟩ ⟨c7,r3⟩ := by
    refine Quiet.step_of (by change (0x80000460#32).getLsbD 0=false;decide) se2147484768 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r3 0 [] [] = ⟨.ok c7 r3 [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r3⟩ ⟨c8,r3⟩ := by
    refine Quiet.step_of (by change (0x80000462#32).getLsbD 0=false;decide) se2147484770 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r3 0 [] [] = ⟨.ok c8 r3 [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r3⟩ ⟨c9,r4⟩ := by
    refine Quiet.step_of (by change (0x80000464#32).getLsbD 0=false;decide) se2147484772 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r3 0 [] [] = ⟨.ok c9 r4 [],[]⟩
    have v9 : c8.get 9=res := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9]
    have v10 : c8.get 10=0xffffffff#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9]
    rw [exec_store,v9,v10,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned res 0 hra) (Memory.block_access hr (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r4⟩ ⟨c10,r5⟩ := by
    refine Quiet.step_of (by change (0x80000466#32).getLsbD 0=false;decide) se2147484774 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r4 0 [] [] = ⟨.ok c10 r5 [],[]⟩
    have v9 : c9.get 9=res := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9]
    have v22 : c9.get 22=flag := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9]
    rw [exec_store,v9,v22,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned res 1 hra) (Memory.block_access hr (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r5⟩ ⟨c11,r6⟩ := by
    refine Quiet.step_of (by change (0x8000046a#32).getLsbD 0=false;decide) se2147484778 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r5 0 [] [] = ⟨.ok c11 r6 [],[]⟩
    have v8 : c10.get 8=obj := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9]
    have v11 : c10.get 11=1#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9]
    rw [exec_store,v8,v11,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 45) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c11,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.single t10)))))))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9]
  · intro reg h10 h22 h11;simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h22,h11]
end E5R.Thermostat.SendFinish
