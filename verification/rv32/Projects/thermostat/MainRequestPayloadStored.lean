import Projects.thermostat.MainRequestMetadataStores
import Projects.thermostat.RamWriteBytes
import Projects.thermostat.MainRamHalves
import Projects.thermostat.FrameOffsets
namespace E5R.Thermostat.MainRequestPayloadStored
open E5R E5R.Thermostat

theorem byte3320 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) :
    MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd (sp+3320#32)=byteOf (low) 0 := by
  unfold MainRequestMetadataStores.memory
  rw [FrameOffsets.byte _ sp (targetEnd) 3320 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (targetStart) 3320 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (methodEnd) 3320 3332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (methodStart) 3320 3328 .w (by decide) (by decide) (by decide)]
  simpa only [BitVec.add_assoc,show 3320#32+0#32=3320#32 by decide +kernel] using RamWriteBytes.written (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+3616#32) (path) .w) (sp+3620#32) (pathLen) .w) (sp+3624#32) (query) .w) (sp+3628#32) (queryLen) .w) (sp+3322#32) (0#32) .h) (sp+3324#32) (0#32) .h) (sp+3326#32) (0#32) .h) (sp+3312#32) (tag) .w) (sp+3316#32) (pad) .w) (sp+3320#32) (low) .h ⟨0,by decide⟩

theorem byte3321 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) :
    MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd (sp+3321#32)=byteOf (low) 1 := by
  unfold MainRequestMetadataStores.memory
  rw [FrameOffsets.byte _ sp (targetEnd) 3321 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (targetStart) 3321 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (methodEnd) 3321 3332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (methodStart) 3321 3328 .w (by decide) (by decide) (by decide)]
  simpa only [BitVec.add_assoc,show 3320#32+1#32=3321#32 by decide +kernel] using RamWriteBytes.written (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+3616#32) (path) .w) (sp+3620#32) (pathLen) .w) (sp+3624#32) (query) .w) (sp+3628#32) (queryLen) .w) (sp+3322#32) (0#32) .h) (sp+3324#32) (0#32) .h) (sp+3326#32) (0#32) .h) (sp+3312#32) (tag) .w) (sp+3316#32) (pad) .w) (sp+3320#32) (low) .h ⟨1,by decide⟩

theorem byte3322 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) :
    MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd (sp+3322#32)=byteOf (0#32) 0 := by
  unfold MainRequestMetadataStores.memory
  rw [FrameOffsets.byte _ sp (targetEnd) 3322 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (targetStart) 3322 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (methodEnd) 3322 3332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (methodStart) 3322 3328 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (low) 3322 3320 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (pad) 3322 3316 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (tag) 3322 3312 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (0#32) 3322 3326 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (0#32) 3322 3324 .h (by decide) (by decide) (by decide)]
  simpa only [BitVec.add_assoc,show 3322#32+0#32=3322#32 by decide +kernel] using RamWriteBytes.written (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+3616#32) (path) .w) (sp+3620#32) (pathLen) .w) (sp+3624#32) (query) .w) (sp+3628#32) (queryLen) .w) (sp+3322#32) (0#32) .h ⟨0,by decide⟩

theorem byte3323 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) :
    MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd (sp+3323#32)=byteOf (0#32) 1 := by
  unfold MainRequestMetadataStores.memory
  rw [FrameOffsets.byte _ sp (targetEnd) 3323 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (targetStart) 3323 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (methodEnd) 3323 3332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (methodStart) 3323 3328 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (low) 3323 3320 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (pad) 3323 3316 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (tag) 3323 3312 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (0#32) 3323 3326 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (0#32) 3323 3324 .h (by decide) (by decide) (by decide)]
  simpa only [BitVec.add_assoc,show 3322#32+1#32=3323#32 by decide +kernel] using RamWriteBytes.written (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+3616#32) (path) .w) (sp+3620#32) (pathLen) .w) (sp+3624#32) (query) .w) (sp+3628#32) (queryLen) .w) (sp+3322#32) (0#32) .h ⟨1,by decide⟩

theorem byte3324 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) :
    MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd (sp+3324#32)=byteOf (0#32) 0 := by
  unfold MainRequestMetadataStores.memory
  rw [FrameOffsets.byte _ sp (targetEnd) 3324 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (targetStart) 3324 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (methodEnd) 3324 3332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (methodStart) 3324 3328 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (low) 3324 3320 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (pad) 3324 3316 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (tag) 3324 3312 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (0#32) 3324 3326 .h (by decide) (by decide) (by decide)]
  simpa only [BitVec.add_assoc,show 3324#32+0#32=3324#32 by decide +kernel] using RamWriteBytes.written (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+3616#32) (path) .w) (sp+3620#32) (pathLen) .w) (sp+3624#32) (query) .w) (sp+3628#32) (queryLen) .w) (sp+3322#32) (0#32) .h) (sp+3324#32) (0#32) .h ⟨0,by decide⟩

theorem byte3325 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) :
    MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd (sp+3325#32)=byteOf (0#32) 1 := by
  unfold MainRequestMetadataStores.memory
  rw [FrameOffsets.byte _ sp (targetEnd) 3325 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (targetStart) 3325 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (methodEnd) 3325 3332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (methodStart) 3325 3328 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (low) 3325 3320 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (pad) 3325 3316 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (tag) 3325 3312 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (0#32) 3325 3326 .h (by decide) (by decide) (by decide)]
  simpa only [BitVec.add_assoc,show 3324#32+1#32=3325#32 by decide +kernel] using RamWriteBytes.written (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+3616#32) (path) .w) (sp+3620#32) (pathLen) .w) (sp+3624#32) (query) .w) (sp+3628#32) (queryLen) .w) (sp+3322#32) (0#32) .h) (sp+3324#32) (0#32) .h ⟨1,by decide⟩

theorem byte3326 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) :
    MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd (sp+3326#32)=byteOf (0#32) 0 := by
  unfold MainRequestMetadataStores.memory
  rw [FrameOffsets.byte _ sp (targetEnd) 3326 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (targetStart) 3326 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (methodEnd) 3326 3332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (methodStart) 3326 3328 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (low) 3326 3320 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (pad) 3326 3316 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (tag) 3326 3312 .w (by decide) (by decide) (by decide)]
  simpa only [BitVec.add_assoc,show 3326#32+0#32=3326#32 by decide +kernel] using RamWriteBytes.written (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+3616#32) (path) .w) (sp+3620#32) (pathLen) .w) (sp+3624#32) (query) .w) (sp+3628#32) (queryLen) .w) (sp+3322#32) (0#32) .h) (sp+3324#32) (0#32) .h) (sp+3326#32) (0#32) .h ⟨0,by decide⟩

theorem byte3327 (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) :
    MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd (sp+3327#32)=byteOf (0#32) 1 := by
  unfold MainRequestMetadataStores.memory
  rw [FrameOffsets.byte _ sp (targetEnd) 3327 3340 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (targetStart) 3327 3336 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (methodEnd) 3327 3332 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (methodStart) 3327 3328 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (low) 3327 3320 .h (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (pad) 3327 3316 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp (tag) 3327 3312 .w (by decide) (by decide) (by decide)]
  simpa only [BitVec.add_assoc,show 3326#32+1#32=3327#32 by decide +kernel] using RamWriteBytes.written (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+3616#32) (path) .w) (sp+3620#32) (pathLen) .w) (sp+3624#32) (query) .w) (sp+3628#32) (queryLen) .w) (sp+3322#32) (0#32) .h) (sp+3324#32) (0#32) .h) (sp+3326#32) (0#32) .h ⟨1,by decide⟩

theorem low_word (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) (small : low.toNat<65536) :
    ramRead (MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd) (sp+3320#32) .w=low := by
  apply ResponseWordBytes.word
  intro i
  have casesIndex : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by have := i.isLt;omega
  rcases casesIndex with h|h|h|h
  · have value := byte3320 ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd
    simpa only [h,BitVec.add_assoc,show 3320#32+0#32=3320#32 by decide +kernel] using value
  · have value := byte3321 ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd
    simpa only [h,BitVec.add_assoc,show 3320#32+1#32=3321#32 by decide +kernel] using value
  · have value := byte3322 ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd
    have high : byteOf low 2=0#8 := MainRamHalves.high_byte low small ⟨0,by decide⟩
    simpa only [h,BitVec.add_assoc,show 3320#32+2#32=3322#32 by decide +kernel,high,show byteOf 0#32 0=0#8 by decide +kernel] using value
  · have value := byte3323 ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd
    have high : byteOf low 3=0#8 := MainRamHalves.high_byte low small ⟨1,by decide⟩
    simpa only [h,BitVec.add_assoc,show 3320#32+3#32=3323#32 by decide +kernel,high,show byteOf 0#32 1=0#8 by decide +kernel] using value

theorem high_word (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) :
    ramRead (MainRequestMetadataStores.memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd) (sp+3324#32) .w=0#32 := by
  apply ResponseWordBytes.word
  intro i
  have casesIndex : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by have := i.isLt;omega
  rcases casesIndex with h|h|h|h
  · have value := byte3324 ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd
    simpa only [h,BitVec.add_assoc,show 3324#32+0#32=3324#32 by decide +kernel,show byteOf 0#32 0=byteOf 0#32 0 by decide +kernel] using value
  · have value := byte3325 ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd
    simpa only [h,BitVec.add_assoc,show 3324#32+1#32=3325#32 by decide +kernel,show byteOf 0#32 1=byteOf 0#32 1 by decide +kernel] using value
  · have value := byte3326 ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd
    simpa only [h,BitVec.add_assoc,show 3324#32+2#32=3326#32 by decide +kernel,show byteOf 0#32 0=byteOf 0#32 2 by decide +kernel] using value
  · have value := byte3327 ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd
    simpa only [h,BitVec.add_assoc,show 3324#32+3#32=3327#32 by decide +kernel,show byteOf 0#32 1=byteOf 0#32 3 by decide +kernel] using value
end E5R.Thermostat.MainRequestPayloadStored
