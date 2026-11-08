import Projects.thermostat.MainChunkPersist
import Projects.thermostat.ChunkWordMath
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainChunkPersistData
open E5R E5R.Thermostat HttpRequestSpec

theorem word0 (ram : Word → BitVec 8) (sp index : Word) :
    ramRead (MainChunkPersist.memory ram sp index) (sp+3680#32) .w=
      ramRead ram (sp+4824#32) .w := by
  unfold MainChunkPersist.memory
  rw [FrameOffsets.word _ sp _ 3680 3656 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3692 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3688 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3684 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word4 (ram : Word → BitVec 8) (sp index : Word) :
    ramRead (MainChunkPersist.memory ram sp index) (sp+3684#32) .w=
      ramRead ram (sp+4828#32) .w := by
  unfold MainChunkPersist.memory
  rw [FrameOffsets.word _ sp _ 3684 3656 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3684 3692 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3684 3688 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word8 (ram : Word → BitVec 8) (sp index : Word) :
    ramRead (MainChunkPersist.memory ram sp index) (sp+3688#32) .w=
      ramRead ram (sp+4832#32) .w := by
  unfold MainChunkPersist.memory
  rw [FrameOffsets.word _ sp _ 3688 3656 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3688 3692 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word12 (ram : Word → BitVec 8) (sp index : Word) :
    ramRead (MainChunkPersist.memory ram sp index) (sp+3692#32) .w=
      ramRead ram (sp+4836#32) .w := by
  unfold MainChunkPersist.memory
  rw [FrameOffsets.word _ sp _ 3692 3656 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word16 (ram : Word → BitVec 8) (sp index : Word) :
    ramRead (MainChunkPersist.memory ram sp index) (sp+3696#32) .w=
      ramRead ram (sp+4840#32) .w := by
  unfold MainChunkPersist.memory
  rw [FrameOffsets.word _ sp _ 3696 3656 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3696 3692 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3696 3688 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3696 3684 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3696 3680 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3696 3708 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3696 3704 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3696 3700 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word20 (ram : Word → BitVec 8) (sp index : Word) :
    ramRead (MainChunkPersist.memory ram sp index) (sp+3700#32) .w=
      ramRead ram (sp+4844#32) .w := by
  unfold MainChunkPersist.memory
  rw [FrameOffsets.word _ sp _ 3700 3656 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3700 3692 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3700 3688 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3700 3684 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3700 3680 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3700 3708 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3700 3704 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem phase (ram : Word → BitVec 8) (sp index : Word) :
    MainChunkPersist.memory ram sp index (sp+3704#32)=byteOf (ramRead ram (sp+4848#32) .w) 0 := by
  unfold MainChunkPersist.memory
  rw [FrameOffsets.byte _ sp _ 3704 3656 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp _ 3704 3692 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp _ 3704 3688 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp _ 3704 3684 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp _ 3704 3680 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp _ 3704 3708 .w (by decide) (by decide) (by decide)]
  simp [ramWrite,ramPut,BitVec.add_assoc,BitVec.add_right_inj,BitVec.self_eq_add_right]

theorem state (ram : Word → BitVec 8) (sp index : Word) (st : CState)
    (h : ChunkLayout.At ram (sp+4824#32) st) :
    ChunkLayout.At (MainChunkPersist.memory ram sp index) (sp+3680#32) st := by
  constructor
  · intro i
    have hi := i.isLt
    have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 := by omega
    rcases hc with h0|h0|h0|h0|h0|h0
    · simp only [h0,show 4*0=0 by decide,BitVec.add_assoc]
      change ramRead (MainChunkPersist.memory ram sp index) (sp+3680#32) .w=ChunkLayout.words st i
      rw [word0]
      simpa [ChunkLayout.words,h0,BitVec.add_assoc] using h.1 ⟨0,by decide⟩
    · simp only [h0,show 4*1=4 by decide,BitVec.add_assoc]
      change ramRead (MainChunkPersist.memory ram sp index) (sp+3684#32) .w=ChunkLayout.words st i
      rw [word4]
      simpa [ChunkLayout.words,h0,BitVec.add_assoc] using h.1 ⟨1,by decide⟩
    · simp only [h0,show 4*2=8 by decide,BitVec.add_assoc]
      change ramRead (MainChunkPersist.memory ram sp index) (sp+3688#32) .w=ChunkLayout.words st i
      rw [word8]
      simpa [ChunkLayout.words,h0,BitVec.add_assoc] using h.1 ⟨2,by decide⟩
    · simp only [h0,show 4*3=12 by decide,BitVec.add_assoc]
      change ramRead (MainChunkPersist.memory ram sp index) (sp+3692#32) .w=ChunkLayout.words st i
      rw [word12]
      simpa [ChunkLayout.words,h0,BitVec.add_assoc] using h.1 ⟨3,by decide⟩
    · simp only [h0,show 4*4=16 by decide,BitVec.add_assoc]
      change ramRead (MainChunkPersist.memory ram sp index) (sp+3696#32) .w=ChunkLayout.words st i
      rw [word16]
      simpa [ChunkLayout.words,h0,BitVec.add_assoc] using h.1 ⟨4,by decide⟩
    · simp only [h0,show 4*5=20 by decide,BitVec.add_assoc]
      change ramRead (MainChunkPersist.memory ram sp index) (sp+3700#32) .w=ChunkLayout.words st i
      rw [word20]
      simpa [ChunkLayout.words,h0,BitVec.add_assoc] using h.1 ⟨5,by decide⟩
  · rw [BitVec.add_assoc,show 3680#32+24#32=3704#32 by decide +kernel,phase,ChunkWordMath.first_byte]
    simpa only [BitVec.add_assoc,show 4824#32+24#32=4848#32 by decide +kernel] using h.2

theorem cursor (ram : Word → BitVec 8) (sp index : Word) :
    ramRead (MainChunkPersist.memory ram sp index) (sp+3656#32) .w=index+1#32 := by
  unfold MainChunkPersist.memory
  exact ramRead_ramWrite_w _ _ _

theorem frame (ram : Word → BitVec 8) (sp index x : Word)
    (hc : ∀ i : Fin 4, x≠(sp+3656#32)+BitVec.ofNat 32 i.val)
    (hs : ∀ i : Fin 32, x≠(sp+3680#32)+BitVec.ofNat 32 i.val) :
    MainChunkPersist.memory ram sp index x=ram x := by
  unfold MainChunkPersist.memory
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have h := hc ⟨0+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (sp+3656#32)+BitVec.ofNat 32 (0+i.val)=(sp+3656#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc sp (3656#32) (0#32),
        show 3656#32+0#32=3656#32 by decide +kernel]
    rw [ha] at h
    exact h)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have h := hs ⟨12+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (sp+3680#32)+BitVec.ofNat 32 (12+i.val)=(sp+3692#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc sp (3680#32) (12#32),
        show 3680#32+12#32=3692#32 by decide +kernel]
    rw [ha] at h
    exact h)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have h := hs ⟨8+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (sp+3680#32)+BitVec.ofNat 32 (8+i.val)=(sp+3688#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc sp (3680#32) (8#32),
        show 3680#32+8#32=3688#32 by decide +kernel]
    rw [ha] at h
    exact h)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have h := hs ⟨4+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (sp+3680#32)+BitVec.ofNat 32 (4+i.val)=(sp+3684#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc sp (3680#32) (4#32),
        show 3680#32+4#32=3684#32 by decide +kernel]
    rw [ha] at h
    exact h)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have h := hs ⟨0+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (sp+3680#32)+BitVec.ofNat 32 (0+i.val)=(sp+3680#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc sp (3680#32) (0#32),
        show 3680#32+0#32=3680#32 by decide +kernel]
    rw [ha] at h
    exact h)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have h := hs ⟨28+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (sp+3680#32)+BitVec.ofNat 32 (28+i.val)=(sp+3708#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc sp (3680#32) (28#32),
        show 3680#32+28#32=3708#32 by decide +kernel]
    rw [ha] at h
    exact h)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have h := hs ⟨24+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (sp+3680#32)+BitVec.ofNat 32 (24+i.val)=(sp+3704#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc sp (3680#32) (24#32),
        show 3680#32+24#32=3704#32 by decide +kernel]
    rw [ha] at h
    exact h)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have h := hs ⟨20+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (sp+3680#32)+BitVec.ofNat 32 (20+i.val)=(sp+3700#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc sp (3680#32) (20#32),
        show 3680#32+20#32=3700#32 by decide +kernel]
    rw [ha] at h
    exact h)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have h := hs ⟨16+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (sp+3680#32)+BitVec.ofNat 32 (16+i.val)=(sp+3696#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc sp (3680#32) (16#32),
        show 3680#32+16#32=3696#32 by decide +kernel]
    rw [ha] at h
    exact h)]
end E5R.Thermostat.MainChunkPersistData
