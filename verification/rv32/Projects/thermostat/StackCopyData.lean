import Projects.thermostat.StackAccess
import Projects.thermostat.CopyTwoResult
import Projects.thermostat.CopyThreeResult
import Projects.thermostat.CopyErrorTailData
import Projects.thermostat.ForbiddenCopyData
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.StackCopyData
open E5R E5R.Thermostat
abbrev small := StackBoard.board

theorem aligned {src ws} (h : AlignedSource.Source UartPlatform.board src ws) : AlignedSource.Source small src ws :=
  ⟨h.aligned,fun i => StackAccess.outside (h.outside i),h.values⟩

theorem tail_span (wide : Bool) (ram : Word → BitVec 8) : ReadBytes.Span small img ram (CopyErrorTailData.pointer wide) [125#8] := by
  apply StackAccess.rom_span (CopyErrorTailData.span wide ram)
  intro i
  have hi : i.val=0 := by have := i.isLt;change i.val<1 at this;omega
  simpa only [hi,show BitVec.ofNat 32 0=0#32 from rfl,BitVec.add_zero] using CopyErrorTailData.outside wide

theorem final_span (ram : Word → BitVec 8) : ReadBytes.Span small img ram 0x80005bf4#32 [125#8] := by
  apply StackAccess.rom_span (ForbiddenCopyData.final_byte ram)
  intro i
  have hi : i.val=0 := by have := i.isLt;change i.val<1 at this;omega
  simpa only [hi,show BitVec.ofNat 32 0=0#32 from rfl,BitVec.add_zero] using ForbiddenCopyData.final_outside

theorem written_two (ram : Word → BitVec 8) (sp dst : Word)
    (hd : Memory.Block small dst 33) (hw : dst.toNat+33<2^32)
    (hn : WordRegions.Disjoint sp 16 dst 33) :
    Bytes.Span small (CopyTwoExecute.memory ram sp dst) dst (ReplyJson.errorBody (UnalignedCopyData.error true)) := by
  have original := CopyTwoResult.written ram sp dst (StackAccess.block hd) hw hn
  exact Bytes.of_block small _ _ _ (by change Memory.Block small dst 33;exact hd) original.length original.bytes

theorem written_three (ram : Word → BitVec 8) (sp dst : Word)
    (hd : Memory.Block small dst 25) (hw : dst.toNat+25<2^32)
    (hn : WordRegions.Disjoint sp 16 dst 25) :
    Bytes.Span small (CopyThreeExecute.memory ram sp dst) dst (ReplyJson.errorBody (UnalignedCopyData.error false)) := by
  have original := CopyThreeResult.written ram sp dst (StackAccess.block hd) hw hn
  exact Bytes.of_block small _ _ _ (by change Memory.Block small dst 25;exact hd) original.length original.bytes
end E5R.Thermostat.StackCopyData
