import Projects.thermostat.MainChunkLayout
import Projects.thermostat.MainChunkInput
import Projects.thermostat.ChunkDecodedInvariant
namespace E5R.Thermostat.MainChunkLoopInvariant
open E5R E5R.Thermostat HttpRequestSpec

/-- A body-loop cutpoint, before checking whether another buffered byte is
    available. Protocol headers and the external input stream are separate. -/
structure At (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (start read written filled : Nat) (s : CState) : Prop where
  pc : c.pc=0x80000e9a#32
  stackPtr : c.get 2=sp
  framePtr : c.get 8=sp+3204#32
  statePtr : c.get 23=sp+3680#32
  cursor : c.get 24=BitVec.ofNat 32 read
  one : c.get 22=1#32
  uart : c.get 19=0x10000000#32
  masked : c.mie_=false
  stack : Memory.Block B sp 4928
  align : sp.toNat%4=0
  layout : MainChunkLayout.At ram sp
  filledWord : ramRead ram (sp+3288#32) .w=BitVec.ofNat 32 filled
  readWord : ramRead ram (sp+3656#32) .w=BitVec.ofNat 32 read
  writeWord : ramRead ram (sp+3660#32) .w=BitVec.ofNat 32 written
  object : ChunkLayout.At ram (sp+3680#32) s
  decoder : ChunkDecodedInvariant.Inv 1024 s (written-start)
  startWritten : start≤written
  writtenRead : written≤read
  readFilled : read≤filled
  capacity : filled≤2048

/-- The data write guard follows from the loop bounds whenever a byte is
    available. It is not a separate assumed successful bounds check. -/
theorem write_bound {B c ram sp start read written filled s}
    (h : At B c ram sp start read written filled s) (available : read<filled) : written<2048 := by
  have := h.writtenRead
  have := h.capacity
  omega

theorem decoded_bound {B c ram sp start read written filled s}
    (h : At B c ram sp start read written filled s) : written-start≤1024 :=
  ChunkDecodedInvariant.decoded_bound h.decoder

end E5R.Thermostat.MainChunkLoopInvariant
