import Projects.thermostat.FormatCallbackInput
import Projects.thermostat.StackFormatLayout
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.StackFormatCallbackInput
open E5R E5R.Thermostat 
theorem from_source {ram p obj dst cap pos value}
    (h : StackFormatSpace.Space ram p obj dst cap pos)
    (hs : FormatSource.At StackBoard.board ram value)
    (hn : WordRegions.Disjoint (FormatValue.pointer value) (FormatValue.size value) p 224) :
    FormatCallbackData.Data StackBoard.board (FormatArgumentCall.memory ram (p+160#32) obj)
      p (p+160#32) obj dst cap pos value := by
  have hv := FormatSource.frame hs (FormatSpace.stored_region (obj := obj) hn)
  have hh := StackFormatSpace.stored h
  have hw := FormatArgumentCall.words ram (p+160#32) obj
  cases hv with
  | signed ptr v hm ha hx =>
    change WordRegions.Disjoint ptr 2 p 224 at hn
    apply FormatCallbackData.Data.signed ptr v
    exact ⟨StackFormatSpace.char hh,
      by simpa only [BitVec.add_zero] using Memory.sub_block h.arena (off := 0) (m := 160) (by decide) (by decide),
      h.aligned,hm,ha,hx,
      Memory.sub_block h.arena (off := 160) (m := 14) (by decide) (by decide),Memory.word_aligned p 40 h.aligned,
      hw.1,hw.2.1,hw.2.2.1,FormatArgumentCall.width ram (p+160#32) obj,
      by simpa only [BitVec.add_zero] using Subregion.right h.objectArena 0 160 (by decide),
      by simpa only [BitVec.add_zero] using Subregion.right h.outputArena 0 160 (by decide),
      by simpa only [BitVec.add_zero] using Subregion.right hn 0 160 (by decide),
      by simpa only [BitVec.add_zero] using FormatSpace.offsets_disjoint p 160 14 0 160 (by decide) (by decide) (by decide)⟩
  | boolean ptr v hx =>
    apply FormatCallbackData.Data.boolean ptr v hx
    apply StackFormatSpace.format_stored h (FormatLiterals.boolPointer v) (ReplyJson.boolean v) (StackAccess.rom_span (FormatLiterals.bool_span v _) (FormatLiterals.bool_outside v))
    · cases v <;> decide
    · exact fun i => StackAccess.outside (FormatLiterals.bool_outside v i)
  | mode ptr v hm ha hp hl =>
    apply FormatCallbackData.Data.mode ptr v hm ha hp hl
    apply StackFormatSpace.format_stored h (ModeLiterals.pointer v) (ReplyJson.mode v) (StackAccess.rom_span (ModeLiterals.span v _) (ModeLiterals.outside v))
    · cases v <;> decide
    · exact fun i => StackAccess.outside (ModeLiterals.outside v i)
end E5R.Thermostat.StackFormatCallbackInput
