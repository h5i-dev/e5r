import Projects.thermostat.MainRequestBodyStores
import Projects.thermostat.MainRequestMetadataStores
import Projects.thermostat.MainRequestMinorRawStores
import Projects.thermostat.MainRequestPaddingStores
import Projects.thermostat.FrameOffsets
set_option autoImplicit false
namespace E5R.Thermostat.MainRequestStoreWords
open E5R E5R.Thermostat

theorem BodyStores_3632 (ram : Word → BitVec 8) (sp bodyPtr bodyLen method : Word) :
    ramRead (MainRequestBodyStores.memory ram sp bodyPtr bodyLen method) (sp+3632#32) .w=bodyPtr := by
  unfold MainRequestBodyStores.memory
  rw [FrameOffsets.word _ sp (method) 3632 3684 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (bodyLen) 3632 3636 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem BodyStores_3636 (ram : Word → BitVec 8) (sp bodyPtr bodyLen method : Word) :
    ramRead (MainRequestBodyStores.memory ram sp bodyPtr bodyLen method) (sp+3636#32) .w=bodyLen := by
  unfold MainRequestBodyStores.memory
  rw [FrameOffsets.word _ sp (method) 3636 3684 .b (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem BodyStores_3684 (ram : Word → BitVec 8) (sp bodyPtr bodyLen method : Word) :
    MainRequestBodyStores.memory ram sp bodyPtr bodyLen method (sp+3684#32)=byteOf method 0 := by
  unfold MainRequestBodyStores.memory
  exact ramPut_eq _ _ _

theorem MetadataStores_3616 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd) (sp+3616#32) .w=path := by
  unfold MainRequestMetadataStores.memory
  rw [FrameOffsets.word _ sp (targetEnd) 3616 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetStart) 3616 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (methodEnd) 3616 3332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (methodStart) 3616 3328 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (low) 3616 3320 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (pad) 3616 3316 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (tag) 3616 3312 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (0#32) 3616 3326 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (0#32) 3616 3324 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (0#32) 3616 3322 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (queryLen) 3616 3628 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (query) 3616 3624 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (pathLen) 3616 3620 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem MetadataStores_3620 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd) (sp+3620#32) .w=pathLen := by
  unfold MainRequestMetadataStores.memory
  rw [FrameOffsets.word _ sp (targetEnd) 3620 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetStart) 3620 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (methodEnd) 3620 3332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (methodStart) 3620 3328 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (low) 3620 3320 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (pad) 3620 3316 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (tag) 3620 3312 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (0#32) 3620 3326 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (0#32) 3620 3324 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (0#32) 3620 3322 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (queryLen) 3620 3628 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (query) 3620 3624 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem MetadataStores_3624 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd) (sp+3624#32) .w=query := by
  unfold MainRequestMetadataStores.memory
  rw [FrameOffsets.word _ sp (targetEnd) 3624 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetStart) 3624 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (methodEnd) 3624 3332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (methodStart) 3624 3328 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (low) 3624 3320 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (pad) 3624 3316 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (tag) 3624 3312 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (0#32) 3624 3326 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (0#32) 3624 3324 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (0#32) 3624 3322 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (queryLen) 3624 3628 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem MetadataStores_3628 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd) (sp+3628#32) .w=queryLen := by
  unfold MainRequestMetadataStores.memory
  rw [FrameOffsets.word _ sp (targetEnd) 3628 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetStart) 3628 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (methodEnd) 3628 3332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (methodStart) 3628 3328 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (low) 3628 3320 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (pad) 3628 3316 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (tag) 3628 3312 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (0#32) 3628 3326 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (0#32) 3628 3324 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (0#32) 3628 3322 .h (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem MetadataStores_3312 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd) (sp+3312#32) .w=tag := by
  unfold MainRequestMetadataStores.memory
  rw [FrameOffsets.word _ sp (targetEnd) 3312 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetStart) 3312 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (methodEnd) 3312 3332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (methodStart) 3312 3328 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (low) 3312 3320 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (pad) 3312 3316 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem MetadataStores_3316 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd) (sp+3316#32) .w=pad := by
  unfold MainRequestMetadataStores.memory
  rw [FrameOffsets.word _ sp (targetEnd) 3316 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetStart) 3316 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (methodEnd) 3316 3332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (methodStart) 3316 3328 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (low) 3316 3320 .h (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem MetadataStores_3328 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd) (sp+3328#32) .w=methodStart := by
  unfold MainRequestMetadataStores.memory
  rw [FrameOffsets.word _ sp (targetEnd) 3328 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetStart) 3328 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (methodEnd) 3328 3332 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem MetadataStores_3332 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd) (sp+3332#32) .w=methodEnd := by
  unfold MainRequestMetadataStores.memory
  rw [FrameOffsets.word _ sp (targetEnd) 3332 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp (targetStart) 3332 3336 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem MetadataStores_3336 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd) (sp+3336#32) .w=targetStart := by
  unfold MainRequestMetadataStores.memory
  rw [FrameOffsets.word _ sp (targetEnd) 3336 3340 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem MetadataStores_3340 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd) (sp+3340#32) .w=targetEnd := by
  unfold MainRequestMetadataStores.memory
  exact ramRead_ramWrite_w _ _ _

theorem MinorRawStores_3608 (ram : Word → BitVec 8) (sp minor rx used : Word) :
    MainRequestMinorRawStores.memory ram sp minor rx used (sp+3608#32)=byteOf minor 0 := by
  unfold MainRequestMinorRawStores.memory
  rw [FrameOffsets.byte _ sp (used) 3608 3644 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (rx) 3608 3640 .w (by decide) (by decide) (by decide)]
  exact ramPut_eq _ _ _

theorem MinorRawStores_3640 (ram : Word → BitVec 8) (sp minor rx used : Word) :
    ramRead (MainRequestMinorRawStores.memory ram sp minor rx used) (sp+3640#32) .w=rx := by
  unfold MainRequestMinorRawStores.memory
  rw [FrameOffsets.word _ sp (used) 3640 3644 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem MinorRawStores_3644 (ram : Word → BitVec 8) (sp minor rx used : Word) :
    ramRead (MainRequestMinorRawStores.memory ram sp minor rx used) (sp+3644#32) .w=used := by
  unfold MainRequestMinorRawStores.memory
  exact ramRead_ramWrite_w _ _ _

theorem PaddingStores_3609 (ram : Word → BitVec 8) (sp b0 b1 b2 b3 b4 b5 b6 : Word) :
    MainRequestPaddingStores.memory ram sp b0 b1 b2 b3 b4 b5 b6 (sp+3609#32)=byteOf b0 0 := by
  unfold MainRequestPaddingStores.memory
  rw [FrameOffsets.byte _ sp (b6) 3609 3615 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (b5) 3609 3614 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (b4) 3609 3613 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (b3) 3609 3612 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (b2) 3609 3611 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (b1) 3609 3610 .b (by decide) (by decide) (by decide)]
  exact ramPut_eq _ _ _

theorem PaddingStores_3610 (ram : Word → BitVec 8) (sp b0 b1 b2 b3 b4 b5 b6 : Word) :
    MainRequestPaddingStores.memory ram sp b0 b1 b2 b3 b4 b5 b6 (sp+3610#32)=byteOf b1 0 := by
  unfold MainRequestPaddingStores.memory
  rw [FrameOffsets.byte _ sp (b6) 3610 3615 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (b5) 3610 3614 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (b4) 3610 3613 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (b3) 3610 3612 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (b2) 3610 3611 .b (by decide) (by decide) (by decide)]
  exact ramPut_eq _ _ _

theorem PaddingStores_3611 (ram : Word → BitVec 8) (sp b0 b1 b2 b3 b4 b5 b6 : Word) :
    MainRequestPaddingStores.memory ram sp b0 b1 b2 b3 b4 b5 b6 (sp+3611#32)=byteOf b2 0 := by
  unfold MainRequestPaddingStores.memory
  rw [FrameOffsets.byte _ sp (b6) 3611 3615 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (b5) 3611 3614 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (b4) 3611 3613 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (b3) 3611 3612 .b (by decide) (by decide) (by decide)]
  exact ramPut_eq _ _ _

theorem PaddingStores_3612 (ram : Word → BitVec 8) (sp b0 b1 b2 b3 b4 b5 b6 : Word) :
    MainRequestPaddingStores.memory ram sp b0 b1 b2 b3 b4 b5 b6 (sp+3612#32)=byteOf b3 0 := by
  unfold MainRequestPaddingStores.memory
  rw [FrameOffsets.byte _ sp (b6) 3612 3615 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (b5) 3612 3614 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (b4) 3612 3613 .b (by decide) (by decide) (by decide)]
  exact ramPut_eq _ _ _

theorem PaddingStores_3613 (ram : Word → BitVec 8) (sp b0 b1 b2 b3 b4 b5 b6 : Word) :
    MainRequestPaddingStores.memory ram sp b0 b1 b2 b3 b4 b5 b6 (sp+3613#32)=byteOf b4 0 := by
  unfold MainRequestPaddingStores.memory
  rw [FrameOffsets.byte _ sp (b6) 3613 3615 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (b5) 3613 3614 .b (by decide) (by decide) (by decide)]
  exact ramPut_eq _ _ _

theorem PaddingStores_3614 (ram : Word → BitVec 8) (sp b0 b1 b2 b3 b4 b5 b6 : Word) :
    MainRequestPaddingStores.memory ram sp b0 b1 b2 b3 b4 b5 b6 (sp+3614#32)=byteOf b5 0 := by
  unfold MainRequestPaddingStores.memory
  rw [FrameOffsets.byte _ sp (b6) 3614 3615 .b (by decide) (by decide) (by decide)]
  exact ramPut_eq _ _ _

theorem PaddingStores_3615 (ram : Word → BitVec 8) (sp b0 b1 b2 b3 b4 b5 b6 : Word) :
    MainRequestPaddingStores.memory ram sp b0 b1 b2 b3 b4 b5 b6 (sp+3615#32)=byteOf b6 0 := by
  unfold MainRequestPaddingStores.memory
  exact ramPut_eq _ _ _
/-- A GET discriminator is actually stored as zero in the Request method byte. -/
theorem get_method (ram : Word → BitVec 8) (sp bodyPtr bodyLen : Word) :
    MainRequestBodyStores.memory ram sp bodyPtr bodyLen 0#32 (sp+3684#32)=0#8 := by
  simpa only [show byteOf 0#32 0=0#8 by decide +kernel] using BodyStores_3684 ram sp bodyPtr bodyLen 0#32

end E5R.Thermostat.MainRequestStoreWords
