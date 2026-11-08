import Projects.thermostat.MainChunkInit
import Projects.thermostat.ChunkLayout
import Projects.thermostat.FrameOffsets
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainChunkInitData
open E5R E5R.Thermostat HttpRequestSpec

theorem initial (ram : Word → BitVec 8) (fp start : Word) :
    ChunkLayout.At (MainChunkInit.memory ram fp start) (fp+476#32) cStart := by
  constructor
  · intro i
    have hi := i.isLt
    have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 := by omega
    rcases hc with h0|h0|h0|h0|h0|h0
    · simp only [h0,show 4*0=0 by decide,BitVec.add_assoc]
      change ramRead (MainChunkInit.memory ram fp start) (fp+476#32) .w=ChunkLayout.words cStart i
      unfold MainChunkInit.memory
      rw [FrameOffsets.word _ fp _ 476 456 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 476 452 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 476 488 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 476 484 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 476 480 .w (by decide) (by decide) (by decide)]
      rw [ramRead_ramWrite_w]
      simp [ChunkLayout.words,cStart,h0]
    · simp only [h0,show 4*1=4 by decide,BitVec.add_assoc]
      change ramRead (MainChunkInit.memory ram fp start) (fp+480#32) .w=ChunkLayout.words cStart i
      unfold MainChunkInit.memory
      rw [FrameOffsets.word _ fp _ 480 456 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 480 452 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 480 488 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 480 484 .w (by decide) (by decide) (by decide)]
      rw [ramRead_ramWrite_w]
      simp [ChunkLayout.words,cStart,h0]
    · simp only [h0,show 4*2=8 by decide,BitVec.add_assoc]
      change ramRead (MainChunkInit.memory ram fp start) (fp+484#32) .w=ChunkLayout.words cStart i
      unfold MainChunkInit.memory
      rw [FrameOffsets.word _ fp _ 484 456 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 484 452 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 484 488 .w (by decide) (by decide) (by decide)]
      rw [ramRead_ramWrite_w]
      simp [ChunkLayout.words,cStart,h0]
    · simp only [h0,show 4*3=12 by decide,BitVec.add_assoc]
      change ramRead (MainChunkInit.memory ram fp start) (fp+488#32) .w=ChunkLayout.words cStart i
      unfold MainChunkInit.memory
      rw [FrameOffsets.word _ fp _ 488 456 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 488 452 .w (by decide) (by decide) (by decide)]
      rw [ramRead_ramWrite_w]
      simp [ChunkLayout.words,cStart,h0]
    · simp only [h0,show 4*4=16 by decide,BitVec.add_assoc]
      change ramRead (MainChunkInit.memory ram fp start) (fp+492#32) .w=ChunkLayout.words cStart i
      unfold MainChunkInit.memory
      rw [FrameOffsets.word _ fp _ 492 456 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 492 452 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 492 488 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 492 484 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 492 480 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 492 476 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 492 504 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 492 500 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 492 496 .w (by decide) (by decide) (by decide)]
      rw [ramRead_ramWrite_w]
      simp [ChunkLayout.words,cStart,h0]
    · simp only [h0,show 4*5=20 by decide,BitVec.add_assoc]
      change ramRead (MainChunkInit.memory ram fp start) (fp+496#32) .w=ChunkLayout.words cStart i
      unfold MainChunkInit.memory
      rw [FrameOffsets.word _ fp _ 496 456 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 496 452 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 496 488 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 496 484 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 496 480 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 496 476 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 496 504 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ fp _ 496 500 .w (by decide) (by decide) (by decide)]
      rw [ramRead_ramWrite_w]
      simp [ChunkLayout.words,cStart,h0]
  · change MainChunkInit.memory ram fp start ((fp+476#32)+24#32)=0#8
    rw [BitVec.add_assoc,show 476#32+24#32=500#32 by decide +kernel]
    unfold MainChunkInit.memory
    rw [FrameOffsets.byte _ fp _ 500 456 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.byte _ fp _ 500 452 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.byte _ fp _ 500 488 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.byte _ fp _ 500 484 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.byte _ fp _ 500 480 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.byte _ fp _ 500 476 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.byte _ fp _ 500 504 .w (by decide) (by decide) (by decide)]
    simp [ramWrite,ramPut,BitVec.add_assoc,BitVec.add_right_inj,BitVec.self_eq_add_right,byteOf]

theorem cursor452 (ram : Word → BitVec 8) (fp start : Word) :
    ramRead (MainChunkInit.memory ram fp start) (fp+452#32) .w=start := by
  unfold MainChunkInit.memory
  rw [FrameOffsets.word _ fp _ 452 456 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem cursor456 (ram : Word → BitVec 8) (fp start : Word) :
    ramRead (MainChunkInit.memory ram fp start) (fp+456#32) .w=start := by
  unfold MainChunkInit.memory
  exact ramRead_ramWrite_w _ _ _

theorem frame (ram : Word → BitVec 8) (fp start x : Word)
    (hm : ∀ i : Fin 8, x≠(fp+452#32)+BitVec.ofNat 32 i.val)
    (hs : ∀ i : Fin 32, x≠(fp+476#32)+BitVec.ofNat 32 i.val) :
    MainChunkInit.memory ram fp start x=ram x := by
  unfold MainChunkInit.memory
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have hx := hm ⟨4+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (fp+452#32)+BitVec.ofNat 32 (4+i.val)=(fp+456#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc fp (452#32) (4#32),
        show 452#32+4#32=456#32 by decide +kernel]
    rw [ha] at hx
    exact hx)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have hx := hm ⟨0+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (fp+452#32)+BitVec.ofNat 32 (0+i.val)=(fp+452#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc fp (452#32) (0#32),
        show 452#32+0#32=452#32 by decide +kernel]
    rw [ha] at hx
    exact hx)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have hx := hs ⟨12+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (fp+476#32)+BitVec.ofNat 32 (12+i.val)=(fp+488#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc fp (476#32) (12#32),
        show 476#32+12#32=488#32 by decide +kernel]
    rw [ha] at hx
    exact hx)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have hx := hs ⟨8+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (fp+476#32)+BitVec.ofNat 32 (8+i.val)=(fp+484#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc fp (476#32) (8#32),
        show 476#32+8#32=484#32 by decide +kernel]
    rw [ha] at hx
    exact hx)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have hx := hs ⟨4+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (fp+476#32)+BitVec.ofNat 32 (4+i.val)=(fp+480#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc fp (476#32) (4#32),
        show 476#32+4#32=480#32 by decide +kernel]
    rw [ha] at hx
    exact hx)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have hx := hs ⟨0+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (fp+476#32)+BitVec.ofNat 32 (0+i.val)=(fp+476#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc fp (476#32) (0#32),
        show 476#32+0#32=476#32 by decide +kernel]
    rw [ha] at hx
    exact hx)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have hx := hs ⟨28+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (fp+476#32)+BitVec.ofNat 32 (28+i.val)=(fp+504#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc fp (476#32) (28#32),
        show 476#32+28#32=504#32 by decide +kernel]
    rw [ha] at hx
    exact hx)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have hx := hs ⟨24+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (fp+476#32)+BitVec.ofNat 32 (24+i.val)=(fp+500#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc fp (476#32) (24#32),
        show 476#32+24#32=500#32 by decide +kernel]
    rw [ha] at hx
    exact hx)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have hx := hs ⟨20+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (fp+476#32)+BitVec.ofNat 32 (20+i.val)=(fp+496#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc fp (476#32) (20#32),
        show 476#32+20#32=496#32 by decide +kernel]
    rw [ha] at hx
    exact hx)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have hx := hs ⟨16+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (fp+476#32)+BitVec.ofNat 32 (16+i.val)=(fp+492#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc fp (476#32) (16#32),
        show 476#32+16#32=492#32 by decide +kernel]
    rw [ha] at hx
    exact hx)]
end E5R.Thermostat.MainChunkInitData
