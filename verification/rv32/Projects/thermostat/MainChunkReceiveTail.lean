import Projects.thermostat.MainChunkCode
import Projects.thermostat.QuietRam
import Projects.thermostat.FrameOffsets
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainChunkReceiveTail
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp filled read datum : Word) :=
  ramWrite (ramWrite (ramWrite (ram) (((sp+132#32)+filled)) (datum) .b) (sp+3676#32) (1#32) .b) (sp+3288#32) (filled+1#32) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp filled read datum : Word) (h8 : c.get 8=sp+3204#32) (h10 : c.get 10=(sp+132#32)+filled)
(h11 : c.get 11=datum) (h22 : c.get 22=1#32)
(hm : Memory.Block B sp 4928) (ha : sp.toNat%4=0) (hbound : filled.toNat<2048)
(hfilledPtr : ramRead ram (sp+3640#32) .w=sp+3288#32)
(hfilled : ramRead ram (sp+3288#32) .w=filled) (hread : ramRead ram (sp+3656#32) .w=read)
    (hp : c.pc=0x80000e84#32) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,memory ram sp filled read datum⟩ ∧ d.pc=0x80000e9a#32 ∧
      d.get 10=sp+3288#32 ∧ d.get 11=filled+1#32 ∧ d.get 24=read ∧ (∀ r : Reg, r≠10 → r≠11 → r≠24 → d.get r=c.get r) ∧ d.sameCsr c := by
  let r1 := ramWrite ram (((sp+132#32)+filled)) (datum) .b
  let c1 := c.goto 0x80000e88#32
  let c2 := c1.wr 10 (sp+3288#32) 0x80000e8c#32
  let r2 := ramWrite r1 (sp+3676#32) (1#32) .b
  let c3 := c2.goto 0x80000e90#32
  let c4 := c3.wr 11 (filled) 0x80000e92#32
  let c5 := c4.wr 11 (filled+1#32) 0x80000e94#32
  let r3 := ramWrite r2 (sp+3288#32) (filled+1#32) .w
  let c6 := c5.goto 0x80000e96#32
  let c7 := c6.wr 24 (read) 0x80000e9a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,r1⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact cc2147487364) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 r1 [],[]⟩
    have addr : (sp+132#32)+filled=sp+BitVec.ofNat 32 (132+filled.toNat) := by
     rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc]
    have v10 : c.get 10=(sp+132#32)+filled := h10
    rw [exec_store,v10,h11,BitVec.add_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _)
    (by rw [addr];exact Memory.block_access hm (off := 132+filled.toNat) (by decide) (by simp only [Width.bytes];omega)),hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,r1⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x80000e88#32).getLsbD 0=false;decide) cc2147487368 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) r1 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have addr : (sp+132#32)+filled=sp+BitVec.ofNat 32 (132+filled.toNat) := by
     rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc]
    have framed : ramRead r1 (sp+3640#32) .w=ramRead ram (sp+3640#32) .w := by
     change ramRead (ramWrite ram ((sp+132#32)+filled) datum .b) (sp+3640#32) .w=_
     rw [addr]
     exact FrameOffsets.word ram sp datum 3640 (132+filled.toNat) .b (by decide) (by simp only [Width.bytes];omega) (by simp only [Width.bytes];omega)
    have v8 : c1.get 8=sp+3204#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+436#32=3640#32 by decide +kernel,
    Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 910 ha)
    (Memory.block_access hm (off := 3640) (by decide) (by decide)),framed,hfilledPtr];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine Quiet.step_of (by change (0x80000e8c#32).getLsbD 0=false;decide) cc2147487372 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r2 [],[]⟩
    have v8 : c2.get 8=sp+3204#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    have v22 : c2.get 22=1#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_store,v8,v22,BitVec.add_assoc,show 3204#32+472#32=3676#32 by decide +kernel,
    Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _)
    (Memory.block_access hm (off := 3676) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r2⟩ := by
    refine Quiet.step_of (by change (0x80000e90#32).getLsbD 0=false;decide) cc2147487376 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r2 0 [] [] = ⟨.ok c4 r2 [],[]⟩
    have addr : (sp+132#32)+filled=sp+BitVec.ofNat 32 (132+filled.toNat) := by
     rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc]
    have framed : ramRead r2 (sp+3288#32) .w=ramRead ram (sp+3288#32) .w := by
     change ramRead (ramWrite (ramWrite ram ((sp+132#32)+filled) datum .b) (sp+3676#32) 1#32 .b) (sp+3288#32) .w=_
     rw [FrameOffsets.word _ sp 1#32 3288 3676 .b (by decide) (by decide) (by decide),addr]
     exact FrameOffsets.word ram sp datum 3288 (132+filled.toNat) .b (by decide) (by simp only [Width.bytes];omega) (by simp only [Width.bytes];omega)
    have v10 : c3.get 10=sp+3288#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_load,v10,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 822 ha)
    (Memory.block_access hm (off := 3288) (by decide) (by decide)),framed,hfilled];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r2⟩ ⟨c5,r2⟩ := by
    refine Quiet.step_of (by change (0x80000e92#32).getLsbD 0=false;decide) cc2147487378 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r2 0 [] [] = ⟨.ok c5 r2 [],[]⟩
    have v11 : c4.get 11=filled := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_opimm,v11];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r2⟩ ⟨c6,r3⟩ := by
    refine Quiet.step_of (by change (0x80000e94#32).getLsbD 0=false;decide) cc2147487380 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r2 0 [] [] = ⟨.ok c6 r3 [],[]⟩
    have v10 : c5.get 10=sp+3288#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    have v11 : c5.get 11=filled+1#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_store,v10,v11,BitVec.add_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 822 ha)
    (Memory.block_access hm (off := 3288) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r3⟩ ⟨c7,r3⟩ := by
    refine Quiet.step_of (by change (0x80000e96#32).getLsbD 0=false;decide) cc2147487382 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r3 0 [] [] = ⟨.ok c7 r3 [],[]⟩
    have finalFrame : ramRead r3 (sp+3656#32) .w=ramRead r2 (sp+3656#32) .w :=
    FrameOffsets.word r2 sp (filled+1#32) 3656 3288 .w (by decide) (by decide) (by decide)
    have addr : (sp+132#32)+filled=sp+BitVec.ofNat 32 (132+filled.toNat) := by
     rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc]
    have framed : ramRead r2 (sp+3656#32) .w=ramRead ram (sp+3656#32) .w := by
     change ramRead (ramWrite (ramWrite ram ((sp+132#32)+filled) datum .b) (sp+3676#32) 1#32 .b) (sp+3656#32) .w=_
     rw [FrameOffsets.word _ sp 1#32 3656 3676 .b (by decide) (by decide) (by decide),addr]
     exact FrameOffsets.word ram sp datum 3656 (132+filled.toNat) .b (by decide) (by simp only [Width.bytes];omega) (by simp only [Width.bytes];omega)
    have v8 : c6.get 8=sp+3204#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+452#32=3656#32 by decide +kernel,
    Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 914 ha)
    (Memory.block_access hm (off := 3656) (by decide) (by decide)),finalFrame,framed,hread];first | rfl | (rw [hp];rfl)
  refine ⟨c7,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.single t6)))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
  · intro reg h10 h11 h24;simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22,h10,h11,h24]
end E5R.Thermostat.MainChunkReceiveTail
