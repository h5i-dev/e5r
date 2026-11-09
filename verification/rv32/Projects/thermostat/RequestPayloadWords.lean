import Projects.thermostat.RequestPayloadMetadata
import Projects.thermostat.FrameOffsets
namespace E5R.Thermostat.RequestPayloadWords
open E5R E5R.Thermostat

theorem word_3616 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (RequestPayloadMetadata.memory ram sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd) (sp+3616#32) .w=path := by
  unfold RequestPayloadMetadata.memory
  rw [FrameOffsets.word _ sp targetEnd 3616 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp targetStart 3616 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp methodEnd 3616 3332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp methodStart 3616 3328 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp low 3616 3320 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp pad 3616 3316 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp tag 3616 3312 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp high2 3616 3326 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp high1 3616 3324 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp high0 3616 3322 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp queryLen 3616 3628 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp query 3616 3624 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp pathLen 3616 3620 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word_3620 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (RequestPayloadMetadata.memory ram sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd) (sp+3620#32) .w=pathLen := by
  unfold RequestPayloadMetadata.memory
  rw [FrameOffsets.word _ sp targetEnd 3620 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp targetStart 3620 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp methodEnd 3620 3332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp methodStart 3620 3328 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp low 3620 3320 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp pad 3620 3316 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp tag 3620 3312 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp high2 3620 3326 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp high1 3620 3324 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp high0 3620 3322 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp queryLen 3620 3628 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp query 3620 3624 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word_3624 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (RequestPayloadMetadata.memory ram sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd) (sp+3624#32) .w=query := by
  unfold RequestPayloadMetadata.memory
  rw [FrameOffsets.word _ sp targetEnd 3624 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp targetStart 3624 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp methodEnd 3624 3332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp methodStart 3624 3328 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp low 3624 3320 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp pad 3624 3316 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp tag 3624 3312 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp high2 3624 3326 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp high1 3624 3324 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp high0 3624 3322 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp queryLen 3624 3628 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word_3628 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (RequestPayloadMetadata.memory ram sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd) (sp+3628#32) .w=queryLen := by
  unfold RequestPayloadMetadata.memory
  rw [FrameOffsets.word _ sp targetEnd 3628 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp targetStart 3628 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp methodEnd 3628 3332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp methodStart 3628 3328 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp low 3628 3320 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp pad 3628 3316 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp tag 3628 3312 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp high2 3628 3326 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp high1 3628 3324 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp high0 3628 3322 .h (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word_3312 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (RequestPayloadMetadata.memory ram sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd) (sp+3312#32) .w=tag := by
  unfold RequestPayloadMetadata.memory
  rw [FrameOffsets.word _ sp targetEnd 3312 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp targetStart 3312 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp methodEnd 3312 3332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp methodStart 3312 3328 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp low 3312 3320 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp pad 3312 3316 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word_3316 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (RequestPayloadMetadata.memory ram sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd) (sp+3316#32) .w=pad := by
  unfold RequestPayloadMetadata.memory
  rw [FrameOffsets.word _ sp targetEnd 3316 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp targetStart 3316 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp methodEnd 3316 3332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp methodStart 3316 3328 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp low 3316 3320 .h (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word_3328 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (RequestPayloadMetadata.memory ram sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd) (sp+3328#32) .w=methodStart := by
  unfold RequestPayloadMetadata.memory
  rw [FrameOffsets.word _ sp targetEnd 3328 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp targetStart 3328 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp methodEnd 3328 3332 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word_3332 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (RequestPayloadMetadata.memory ram sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd) (sp+3332#32) .w=methodEnd := by
  unfold RequestPayloadMetadata.memory
  rw [FrameOffsets.word _ sp targetEnd 3332 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp targetStart 3332 3336 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word_3336 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (RequestPayloadMetadata.memory ram sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd) (sp+3336#32) .w=targetStart := by
  unfold RequestPayloadMetadata.memory
  rw [FrameOffsets.word _ sp targetEnd 3336 3340 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem word_3340 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (RequestPayloadMetadata.memory ram sp path pathLen query queryLen tag pad low high0 high1 high2 methodStart methodEnd targetStart targetEnd) (sp+3340#32) .w=targetEnd := by
  unfold RequestPayloadMetadata.memory
  exact ramRead_ramWrite_w _ _ _
end E5R.Thermostat.RequestPayloadWords
