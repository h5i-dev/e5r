import Projects.thermostat.MainChunkReceiveSetup
import Projects.thermostat.MainChunkReceiveTail
import Projects.thermostat.ChunkStateFrame
import Projects.thermostat.MainChunkLayout
import Projects.thermostat.AppState
namespace E5R.Thermostat.MainChunkReceiveMemory
open E5R E5R.Thermostat

theorem setup_frame (ram : Word → BitVec 8) (sp filled io x : Word)
    (h : ∀ k : Fin 13, x≠(sp+3664#32)+BitVec.ofNat 32 k.val) :
    MainChunkReceiveSetup.memory ram sp filled io x=ram x := by
  unfold MainChunkReceiveSetup.memory
  rw [StoreBytes.frame _ _ _ _ .b (fun i => by
    have hi : i.val=0 := by have := i.isLt;change i.val<1 at this;omega
    simpa only [hi,BitVec.add_zero,show 3664#32+12#32=3676#32 by decide +kernel,BitVec.add_assoc] using h ⟨12,by decide⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (fun i => by
    have hi : i.val<4 := i.isLt
    have hn := h ⟨8+i.val,by omega⟩
    have addr : (sp+3664#32)+BitVec.ofNat 32 (8+i.val)=(sp+3672#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc sp 3664#32 8#32,
        show 3664#32+8#32=3672#32 by decide +kernel]
    rw [addr] at hn
    exact hn)]
  rw [StoreBytes.frame _ _ _ _ .w (fun i => by
    have hi : i.val<4 := i.isLt
    have hn := h ⟨4+i.val,by omega⟩
    have addr : (sp+3664#32)+BitVec.ofNat 32 (4+i.val)=(sp+3668#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc sp 3664#32 4#32,
        show 3664#32+4#32=3668#32 by decide +kernel]
    rw [addr] at hn
    exact hn)]
  exact StoreBytes.frame _ _ _ _ .w (fun i => h ⟨i.val,by have hi : i.val<4 := i.isLt;omega⟩)

theorem setup_region (ram : Word → BitVec 8) (sp filled io : Word) (off len : Nat)
    (hb : off+len≤4294967296) (hs : off+len≤3664 ∨ 3677≤off) :
    ViewFrame.Region ram (MainChunkReceiveSetup.memory ram sp filled io) (sp+BitVec.ofNat 32 off) len := by
  intro i
  apply setup_frame
  intro j
  exact FrameOffsets.ne sp off 3664 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;omega)
    (by have := i.isLt;have := j.isLt;omega)

theorem setup_word (ram : Word → BitVec 8) (sp filled io : Word) (off : Nat)
    (hb : off+4≤4294967296) (hs : off+4≤3664 ∨ 3677≤off) :
    ramRead (MainChunkReceiveSetup.memory ram sp filled io) (sp+BitVec.ofNat 32 off) .w=
      ramRead ram (sp+BitVec.ofNat 32 off) .w := by
  simpa only [BitVec.add_zero] using ViewFrame.word (setup_region ram sp filled io off 4 hb hs) 0 (by decide)

theorem tail_frame (ram : Word → BitVec 8) (sp filled read datum x : Word)
    (hb : x≠(sp+132#32)+filled) (ht : x≠sp+3676#32)
    (hc : ∀ i : Fin 4, x≠(sp+3288#32)+BitVec.ofNat 32 i.val) :
    MainChunkReceiveTail.memory ram sp filled read datum x=ram x := by
  unfold MainChunkReceiveTail.memory
  rw [StoreBytes.frame _ _ _ _ .w hc]
  change ramPut (ramPut ram ((sp+132#32)+filled) (byteOf datum 0)) (sp+3676#32) (byteOf 1#32 0) x=ram x
  rw [ramPut_ne _ ht,ramPut_ne _ hb]

theorem tail_region (ram : Word → BitVec 8) (sp filled read datum : Word) (off len : Nat)
    (hf : filled.toNat<2048) (hb : off+len≤4294967296)
    (hr : off+len≤132+filled.toNat ∨ 132+filled.toNat+1≤off)
    (ht : off+len≤3676 ∨ 3677≤off) (hc : off+len≤3288 ∨ 3292≤off) :
    ViewFrame.Region ram (MainChunkReceiveTail.memory ram sp filled read datum) (sp+BitVec.ofNat 32 off) len := by
  intro i
  apply tail_frame
  · have hn := FrameOffsets.ne sp off 132 i.val filled.toNat (by have := i.isLt;omega) (by omega)
      (by have := i.isLt;omega)
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using hn
  · have hn := FrameOffsets.ne sp off 3676 i.val 0 (by have := i.isLt;omega) (by decide)
      (by have := i.isLt;omega)
    simpa only [BitVec.add_zero] using hn
  · intro j
    exact FrameOffsets.ne sp off 3288 i.val j.val (by have := i.isLt;omega)
      (by have := j.isLt;omega) (by have := i.isLt;have := j.isLt;omega)

theorem tail_word (ram : Word → BitVec 8) (sp filled read datum : Word) (off : Nat)
    (hf : filled.toNat<2048) (hb : off+4≤4294967296)
    (hr : 2180≤off) (ht : off+4≤3676 ∨ 3677≤off) (hc : off+4≤3288 ∨ 3292≤off) :
    ramRead (MainChunkReceiveTail.memory ram sp filled read datum) (sp+BitVec.ofNat 32 off) .w=
      ramRead ram (sp+BitVec.ofNat 32 off) .w := by
  simpa only [BitVec.add_zero] using ViewFrame.word (tail_region ram sp filled read datum off 4 hf hb (by omega) ht hc) 0 (by decide)

theorem tail_filled (ram : Word → BitVec 8) (sp filled read datum : Word) :
    ramRead (MainChunkReceiveTail.memory ram sp filled read datum) (sp+3288#32) .w=filled+1#32 := by
  unfold MainChunkReceiveTail.memory
  exact ramRead_ramWrite_w _ _ _

theorem tail_stored (ram : Word → BitVec 8) (sp filled read datum : Word) (hf : filled.toNat<2048) :
    MainChunkReceiveTail.memory ram sp filled read datum ((sp+132#32)+filled)=byteOf datum 0 := by
  unfold MainChunkReceiveTail.memory
  have addr : (sp+132#32)+filled=sp+BitVec.ofNat 32 (132+filled.toNat) := by
    rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc]
  rw [addr,FrameOffsets.byte _ sp _ (132+filled.toNat) 3288 .w (by omega) (by decide) (by left;omega),
    FrameOffsets.byte _ sp _ (132+filled.toNat) 3676 .b (by omega) (by decide) (by left;omega)]
  exact ramPut_eq _ _ _

end E5R.Thermostat.MainChunkReceiveMemory
