import Projects.thermostat.MainChunkCall
import Projects.thermostat.ChunkWordMath
import Projects.thermostat.FrameOffsets
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainChunkCallData
open E5R E5R.Thermostat HttpRequestSpec

theorem word0 (ram : Word → BitVec 8) (sp rx lim index maxBody : Word) :
    ramRead (MainChunkCall.memory ram sp rx lim index maxBody) (sp+4864#32) .w=
      ramRead ram (sp+3680#32) .w := by
  unfold MainChunkCall.memory
  rw [FrameOffsets.word _ sp _ 4864 4876 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 4864 4872 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 4864 4868 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word4 (ram : Word → BitVec 8) (sp rx lim index maxBody : Word) :
    ramRead (MainChunkCall.memory ram sp rx lim index maxBody) (sp+4868#32) .w=
      ramRead ram (sp+3684#32) .w := by
  unfold MainChunkCall.memory
  rw [FrameOffsets.word _ sp _ 4868 4876 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 4868 4872 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word8 (ram : Word → BitVec 8) (sp rx lim index maxBody : Word) :
    ramRead (MainChunkCall.memory ram sp rx lim index maxBody) (sp+4872#32) .w=
      ramRead ram (sp+3688#32) .w := by
  unfold MainChunkCall.memory
  rw [FrameOffsets.word _ sp _ 4872 4876 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word12 (ram : Word → BitVec 8) (sp rx lim index maxBody : Word) :
    ramRead (MainChunkCall.memory ram sp rx lim index maxBody) (sp+4876#32) .w=
      ramRead ram (sp+3692#32) .w := by
  unfold MainChunkCall.memory
  exact ramRead_ramWrite_w _ _ _

theorem word16 (ram : Word → BitVec 8) (sp rx lim index maxBody : Word) :
    ramRead (MainChunkCall.memory ram sp rx lim index maxBody) (sp+4880#32) .w=
      ramRead ram (sp+3696#32) .w := by
  unfold MainChunkCall.memory
  rw [FrameOffsets.word _ sp _ 4880 4876 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 4880 4872 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 4880 4868 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 4880 4864 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 4880 4892 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 4880 4888 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 4880 4884 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word20 (ram : Word → BitVec 8) (sp rx lim index maxBody : Word) :
    ramRead (MainChunkCall.memory ram sp rx lim index maxBody) (sp+4884#32) .w=
      ramRead ram (sp+3700#32) .w := by
  unfold MainChunkCall.memory
  rw [FrameOffsets.word _ sp _ 4884 4876 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 4884 4872 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 4884 4868 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 4884 4864 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 4884 4892 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 4884 4888 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem phase (ram : Word → BitVec 8) (sp rx lim index maxBody : Word) :
    MainChunkCall.memory ram sp rx lim index maxBody (sp+4888#32)=byteOf (ramRead ram (sp+3704#32) .w) 0 := by
  unfold MainChunkCall.memory
  rw [FrameOffsets.byte _ sp _ 4888 4876 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp _ 4888 4872 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp _ 4888 4868 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp _ 4888 4864 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp _ 4888 4892 .w (by decide) (by decide) (by decide)]
  simp [ramWrite,ramPut,BitVec.add_assoc,BitVec.add_right_inj,BitVec.self_eq_add_right]

theorem state (ram : Word → BitVec 8) (sp rx lim index maxBody : Word) (st : CState)
    (h : ChunkLayout.At ram (sp+3680#32) st) :
    ChunkLayout.At (MainChunkCall.memory ram sp rx lim index maxBody) (sp+4864#32) st := by
  constructor
  · intro i
    have hi := i.isLt
    have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 := by omega
    rcases hc with h0|h0|h0|h0|h0|h0
    · simp only [h0,show 4*0=0 by decide,BitVec.add_assoc]
      change ramRead (MainChunkCall.memory ram sp rx lim index maxBody) (sp+4864#32) .w=ChunkLayout.words st i
      rw [word0]
      simpa [ChunkLayout.words,h0,BitVec.add_assoc] using h.1 ⟨0,by decide⟩
    · simp only [h0,show 4*1=4 by decide,BitVec.add_assoc]
      change ramRead (MainChunkCall.memory ram sp rx lim index maxBody) (sp+4868#32) .w=ChunkLayout.words st i
      rw [word4]
      simpa [ChunkLayout.words,h0,BitVec.add_assoc] using h.1 ⟨1,by decide⟩
    · simp only [h0,show 4*2=8 by decide,BitVec.add_assoc]
      change ramRead (MainChunkCall.memory ram sp rx lim index maxBody) (sp+4872#32) .w=ChunkLayout.words st i
      rw [word8]
      simpa [ChunkLayout.words,h0,BitVec.add_assoc] using h.1 ⟨2,by decide⟩
    · simp only [h0,show 4*3=12 by decide,BitVec.add_assoc]
      change ramRead (MainChunkCall.memory ram sp rx lim index maxBody) (sp+4876#32) .w=ChunkLayout.words st i
      rw [word12]
      simpa [ChunkLayout.words,h0,BitVec.add_assoc] using h.1 ⟨3,by decide⟩
    · simp only [h0,show 4*4=16 by decide,BitVec.add_assoc]
      change ramRead (MainChunkCall.memory ram sp rx lim index maxBody) (sp+4880#32) .w=ChunkLayout.words st i
      rw [word16]
      simpa [ChunkLayout.words,h0,BitVec.add_assoc] using h.1 ⟨4,by decide⟩
    · simp only [h0,show 4*5=20 by decide,BitVec.add_assoc]
      change ramRead (MainChunkCall.memory ram sp rx lim index maxBody) (sp+4884#32) .w=ChunkLayout.words st i
      rw [word20]
      simpa [ChunkLayout.words,h0,BitVec.add_assoc] using h.1 ⟨5,by decide⟩
  · rw [BitVec.add_assoc,show 4864#32+24#32=4888#32 by decide +kernel,phase,ChunkWordMath.first_byte]
    simpa only [BitVec.add_assoc,show 3680#32+24#32=3704#32 by decide +kernel] using h.2

theorem frame (ram : Word → BitVec 8) (sp rx lim index maxBody x : Word)
    (hx : ∀ i : Fin 32, x≠(sp+4864#32)+BitVec.ofNat 32 i.val) :
    MainChunkCall.memory ram sp rx lim index maxBody x=ram x := by
  unfold MainChunkCall.memory
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have h := hx ⟨12+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (sp+4864#32)+BitVec.ofNat 32 (12+i.val)=(sp+4876#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc sp (4864#32) (12#32),
        show 4864#32+12#32=4876#32 by decide +kernel]
    rw [ha] at h
    exact h)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have h := hx ⟨8+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (sp+4864#32)+BitVec.ofNat 32 (8+i.val)=(sp+4872#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc sp (4864#32) (8#32),
        show 4864#32+8#32=4872#32 by decide +kernel]
    rw [ha] at h
    exact h)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have h := hx ⟨4+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (sp+4864#32)+BitVec.ofNat 32 (4+i.val)=(sp+4868#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc sp (4864#32) (4#32),
        show 4864#32+4#32=4868#32 by decide +kernel]
    rw [ha] at h
    exact h)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have h := hx ⟨0+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (sp+4864#32)+BitVec.ofNat 32 (0+i.val)=(sp+4864#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc sp (4864#32) (0#32),
        show 4864#32+0#32=4864#32 by decide +kernel]
    rw [ha] at h
    exact h)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have h := hx ⟨28+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (sp+4864#32)+BitVec.ofNat 32 (28+i.val)=(sp+4892#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc sp (4864#32) (28#32),
        show 4864#32+28#32=4892#32 by decide +kernel]
    rw [ha] at h
    exact h)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have h := hx ⟨24+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (sp+4864#32)+BitVec.ofNat 32 (24+i.val)=(sp+4888#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc sp (4864#32) (24#32),
        show 4864#32+24#32=4888#32 by decide +kernel]
    rw [ha] at h
    exact h)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have h := hx ⟨20+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (sp+4864#32)+BitVec.ofNat 32 (20+i.val)=(sp+4884#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc sp (4864#32) (20#32),
        show 4864#32+20#32=4884#32 by decide +kernel]
    rw [ha] at h
    exact h)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have h := hx ⟨16+i.val,by have hi : i.val<4 := i.isLt;omega⟩
    have ha : (sp+4864#32)+BitVec.ofNat 32 (16+i.val)=(sp+4880#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_assoc sp (4864#32) (16#32),
        show 4864#32+16#32=4880#32 by decide +kernel]
    rw [ha] at h
    exact h)]
end E5R.Thermostat.MainChunkCallData
