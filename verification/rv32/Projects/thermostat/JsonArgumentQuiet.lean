-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.JsonArgument
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.FormatArgumentPieceQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.JsonArgument
theorem contract_quiet (c : Core) (ram : Word → BitVec 8) (p obj args dst : Word)
    (cap : Nat) (litPrefix : List (BitVec 8)) (values : Fin 8 → FormatValue.Value) (i : Fin 8)
    (hr : FormatEngineReady.Ready c (p+160#32) obj args (JsonFormatData.tagPointer ⟨2*i.val+1,by have := i.isLt;omega⟩)
      i.val (JsonFormatData.tagByte ⟨2*i.val+1,by have := i.isLt;omega⟩))
    (h : FormatLayout.Layout ram p obj args dst cap litPrefix.length values)
    (hx : Bytes.Span UartPlatform.board ram dst litPrefix)
    (hf : litPrefix.length+(FormatValue.bytes (values i)).length ≤ cap) :
    ∃ d n r, n ≤ 312 ∧ Quiet.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      FormatEngineReady.Ready d (p+160#32) obj args (JsonFormatData.tagPointer ⟨2*(i.val+1),by have := i.isLt;omega⟩)
        (i.val+1) (JsonFormatData.tagByte ⟨2*(i.val+1),by have := i.isLt;omega⟩) ∧
      d.get 27 = c.get 27 ∧ d.sameCsr c ∧
      FormatLayout.Layout r p obj args dst cap (litPrefix++FormatValue.bytes (values i)).length values ∧
      Bytes.Span UartPlatform.board r dst (litPrefix++FormatValue.bytes (values i)) ∧ FormatLoopFrame.Frame ram r p obj dst cap := by
  let desc := JsonFormatData.tagPointer ⟨2*i.val+1,by have := i.isLt;omega⟩
  let nextIndex : Fin 9 := ⟨i.val+1,by have := i.isLt;omega⟩
  let nxt := JsonFormatData.tagByte ⟨2*(i.val+1),by have := i.isLt;omega⟩
  have hr' : FormatEngineReady.Ready c (p+160#32) obj args desc i.val 192#8 := by
    simpa only [JsonFormatData.argument_tag,desc] using hr
  have hn : ReadBytes.Byte UartPlatform.board img ram (desc+1#32) nxt := by
    rw [JsonFormatData.argument_end];exact JsonFormatData.tag _ ram
  have hro : UartPlatform.board.inRam (desc+1#32) 1 = false := by
    rw [JsonFormatData.argument_end];exact (JsonFormatData.tag_layout _).2.2
  have ha := FormatTable.accessible h.table i
  obtain ⟨d,n,r,hb,td,hpc,hsp,ready,h27,hc,he⟩ := E5R.Thermostat.FormatArgumentPiece.contract_quiet UartPlatform.board c ram p obj args desc dst cap litPrefix.length i.val
    (values i) nxt hr' i.isLt ha.1 ha.2 (h.table.pointer i) (h.table.method i)
    (Memory.sub_block h.arena (off := 160) (m := 16) (by decide) (by decide)) (Memory.word_aligned p 40 h.aligned)
    (FormatCallbackInput.from_source h.toSpace (h.sources i) (h.sourceArena i)) hf hn hro
    FormatLiterals.cursor_method_outside (by unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) DigitTable.outside
  have he224 := AppendEffect.expand he (total := 224) (by decide)
  refine ⟨d,n,r,hb,td,?_,h27,hc,?_,
    AppendEffect.accumulates he224 h.output h.capacity hf h.outputArena h.objectOutput hx,
    FormatLoopFrame.of_effect he hf⟩
  · have hh := ready (JsonFormatData.literal_nonzero nextIndex)
    rw [JsonFormatData.argument_end] at hh
    exact hh
  · simpa only [List.length_append] using FormatLayout.after_append h he224 hf

end E5R.Thermostat.JsonArgument
