import Projects.thermostat.MainChunkCode
import Projects.thermostat.QuietRam
import Projects.thermostat.FrameOffsets
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainChunkDataAppend
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp w r value : Word) :=
  ramWrite (ramWrite (ram) (((sp+132#32)+w)) (value) .b) (sp+3660#32) (w+1#32) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp w r value : Word) (h8 : c.get 8=sp+3204#32) (h20 : c.get 20=value)
    (hm : Memory.Block B sp 4928) (ha : sp.toNat%4=0) (hbound : w.toNat<2048)
    (hw : ramRead ram (sp+3660#32) .w=w) (hr : ramRead ram (sp+3656#32) .w=r)
    (hcap : ramRead ram (sp+3316#32) .w=2048#32) (hrx : ramRead ram (sp+3312#32) .w=sp+132#32)
    (hp : c.pc=0x80000f6a#32) :
    ∃ d, Quiet.Steps B img 11 ⟨c,ram⟩ ⟨d,memory ram sp w r value⟩ ∧ d.pc=0x80000e9a#32 ∧
      d.get 10=w+1#32 ∧ d.get 11=sp+132#32 ∧ d.get 24=r ∧ (∀ r : Reg, r≠10 → r≠11 → r≠24 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (w) 0x80000f6e#32
  let c2 := c1.wr 11 (2048#32) 0x80000f70#32
  let c3 := c2.goto 0x80000f74#32
  let c4 := c3.wr 11 (sp+132#32) 0x80000f76#32
  let c5 := c4.wr 10 ((sp+132#32)+w) 0x80000f78#32
  let r1 := ramWrite ram (((sp+132#32)+w)) (value) .b
  let c6 := c5.goto 0x80000f7c#32
  let c7 := c6.wr 10 (w) 0x80000f80#32
  let c8 := c7.wr 24 (r) 0x80000f84#32
  let c9 := c8.wr 10 (w+1#32) 0x80000f86#32
  let r2 := ramWrite r1 (sp+3660#32) (w+1#32) .w
  let c10 := c9.goto 0x80000f8a#32
  let c11 := c10.goto 0x80000e9a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact cc2147487594) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=sp+3204#32 := by simp [Core.wr_get_ne,Core.wr_get,h8,h20]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+456#32=3660#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 915 ha)
        (Memory.block_access hm (off := 3660) (by decide) (by decide)),hw];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f6e#32).getLsbD 0=false;decide) cc2147487598 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=sp+3204#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h20]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+112#32=3316#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 829 ha)
        (Memory.block_access hm (off := 3316) (by decide) (by decide)),hcap];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f70#32).getLsbD 0=false;decide) cc2147487600 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v10 : c2.get 10=w := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
    have v11 : c2.get 11=2048#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
    have ht : taken .geu w 2048#32=false := by simp [taken,BitVec.ult,hbound]
    rw [exec_branch,v10,v11,ht];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f74#32).getLsbD 0=false;decide) cc2147487604 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v8 : c3.get 8=sp+3204#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+108#32=3312#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 828 ha)
        (Memory.block_access hm (off := 3312) (by decide) (by decide)),hrx];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f76#32).getLsbD 0=false;decide) cc2147487606 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v10 : c4.get 10=w := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
    have v11 : c4.get 11=sp+132#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
    rw [exec_op,v10,v11,(show alu .add w (sp+132#32)=(sp+132#32)+w from BitVec.add_comm _ _)];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,r1⟩ := by
    refine Quiet.step_of (by change (0x80000f78#32).getLsbD 0=false;decide) cc2147487608 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 r1 [],[]⟩
    have addr : (sp+132#32)+w=sp+BitVec.ofNat 32 (132+w.toNat) := by
      rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc]
    have v10 : c5.get 10=(sp+132#32)+w := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
    have v20 : c5.get 20=value := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
    have hr : B.inRam ((sp+132#32)+w) 1=true := by
      rw [addr]
      exact Memory.block_access hm (off := 132+w.toNat) (by decide) (by omega)
    rw [exec_store,v10,v20,BitVec.add_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hr];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r1⟩ ⟨c7,r1⟩ := by
    refine Quiet.step_of (by change (0x80000f7c#32).getLsbD 0=false;decide) cc2147487612 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r1 0 [] [] = ⟨.ok c7 r1 [],[]⟩
    have addr : (sp+132#32)+w=sp+BitVec.ofNat 32 (132+w.toNat) := by
      rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc]
    have framed : ramRead r1 (sp+3660#32) .w=ramRead ram (sp+3660#32) .w := by
      change ramRead (ramWrite ram ((sp+132#32)+w) value .b) (sp+3660#32) .w=_
      rw [addr]
      exact FrameOffsets.word ram sp value 3660 (132+w.toNat) .b (by decide) (by change 132+w.toNat+1≤4294967296;omega) (by right;change 132+w.toNat+1≤3660;omega)
    have v8 : c6.get 8=sp+3204#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+456#32=3660#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 915 ha)
        (Memory.block_access hm (off := 3660) (by decide) (by decide)),framed,hw];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r1⟩ ⟨c8,r1⟩ := by
    refine Quiet.step_of (by change (0x80000f80#32).getLsbD 0=false;decide) cc2147487616 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r1 0 [] [] = ⟨.ok c8 r1 [],[]⟩
    have addr : (sp+132#32)+w=sp+BitVec.ofNat 32 (132+w.toNat) := by
      rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc]
    have framed : ramRead r1 (sp+3656#32) .w=ramRead ram (sp+3656#32) .w := by
      change ramRead (ramWrite ram ((sp+132#32)+w) value .b) (sp+3656#32) .w=_
      rw [addr]
      exact FrameOffsets.word ram sp value 3656 (132+w.toNat) .b (by decide) (by change 132+w.toNat+1≤4294967296;omega) (by right;change 132+w.toNat+1≤3656;omega)
    have v8 : c7.get 8=sp+3204#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+452#32=3656#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 914 ha)
        (Memory.block_access hm (off := 3656) (by decide) (by decide)),framed,hr];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r1⟩ ⟨c9,r1⟩ := by
    refine Quiet.step_of (by change (0x80000f84#32).getLsbD 0=false;decide) cc2147487620 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r1 0 [] [] = ⟨.ok c9 r1 [],[]⟩
    have v10 : c8.get 10=w := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r1⟩ ⟨c10,r2⟩ := by
    refine Quiet.step_of (by change (0x80000f86#32).getLsbD 0=false;decide) cc2147487622 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r1 0 [] [] = ⟨.ok c10 r2 [],[]⟩
    have v8 : c9.get 8=sp+3204#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
    have v10 : c9.get 10=w+1#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
    rw [exec_store,v8,v10,BitVec.add_assoc,show 3204#32+456#32=3660#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 915 ha)
        (Memory.block_access hm (off := 3660) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r2⟩ ⟨c11,r2⟩ := by
    refine Quiet.step_of (by change (0x80000f8a#32).getLsbD 0=false;decide) cc2147487626 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r2 0 [] [] = ⟨.ok c11 r2 [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c10 (c10.pc+0xffffff10#32)) r2 0 [] [] = _
    rw [show c10.pc=0x80000f8a#32 by rfl,show 0x80000f8a#32+0xffffff10#32=0x80000e9a#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c11,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.single t10)))))))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20]
  · intro reg h10 h11 h24;simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20,h10,h11,h24]
end E5R.Thermostat.MainChunkDataAppend
