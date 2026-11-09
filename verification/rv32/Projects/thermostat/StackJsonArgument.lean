import Projects.thermostat.JsonArgumentQuiet
import Projects.thermostat.StackAccess
import Projects.thermostat.StackFormatCallbackInput
import Projects.thermostat.StackFormatLayout
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.StackJsonArgument
open E5R E5R.Thermostat JsonArgument
theorem contract_quiet (c : Core) (ram : Word → BitVec 8) (p obj args dst : Word)
    (cap : Nat) (litPrefix : List (BitVec 8)) (values : Fin 8 → FormatValue.Value) (i : Fin 8)
    (hr : FormatEngineReady.Ready c (p+160#32) obj args (JsonFormatData.tagPointer ⟨2*i.val+1,by have := i.isLt;omega⟩)
      i.val (JsonFormatData.tagByte ⟨2*i.val+1,by have := i.isLt;omega⟩))
    (h : StackFormatLayout.Layout ram p obj args dst cap litPrefix.length values)
    (hx : Bytes.Span StackBoard.board ram dst litPrefix)
    (hf : litPrefix.length+(FormatValue.bytes (values i)).length ≤ cap) :
    ∃ d n r, n ≤ 312 ∧ Quiet.Steps StackBoard.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      FormatEngineReady.Ready d (p+160#32) obj args (JsonFormatData.tagPointer ⟨2*(i.val+1),by have := i.isLt;omega⟩)
        (i.val+1) (JsonFormatData.tagByte ⟨2*(i.val+1),by have := i.isLt;omega⟩) ∧
      d.get 27 = c.get 27 ∧ d.sameCsr c ∧
      StackFormatLayout.Layout r p obj args dst cap (litPrefix++FormatValue.bytes (values i)).length values ∧
      Bytes.Span StackBoard.board r dst (litPrefix++FormatValue.bytes (values i)) ∧ FormatLoopFrame.Frame ram r p obj dst cap := by
  let desc := JsonFormatData.tagPointer ⟨2*i.val+1,by have := i.isLt;omega⟩
  let nextIndex : Fin 9 := ⟨i.val+1,by have := i.isLt;omega⟩
  let nxt := JsonFormatData.tagByte ⟨2*(i.val+1),by have := i.isLt;omega⟩
  have hr' : FormatEngineReady.Ready c (p+160#32) obj args desc i.val 192#8 := by
    simpa only [JsonFormatData.argument_tag,desc] using hr
  have hn : ReadBytes.Byte StackBoard.board img ram (desc+1#32) nxt := by
    rw [JsonFormatData.argument_end];exact StackAccess.rom_byte (JsonFormatData.tag _ ram) (JsonFormatData.tag_layout _).2.2
  have hro : StackBoard.board.inRam (desc+1#32) 1 = false := by
    rw [JsonFormatData.argument_end];exact StackAccess.outside (JsonFormatData.tag_layout _).2.2
  have ha := FormatTable.accessible h.table i
  obtain ⟨d,n,r,hb,td,hpc,hsp,ready,h27,hc,he⟩ := E5R.Thermostat.FormatArgumentPiece.contract_quiet StackBoard.board c ram p obj args desc dst cap litPrefix.length i.val
    (values i) nxt hr' i.isLt ha.1 ha.2 (h.table.pointer i) (h.table.method i)
    (Memory.sub_block h.arena (off := 160) (m := 16) (by decide) (by decide)) (Memory.word_aligned p 40 h.aligned)
    (StackFormatCallbackInput.from_source h.toSpace (h.sources i) (h.sourceArena i)) hf hn hro
    (StackAccess.outside FormatLiterals.cursor_method_outside) (by unfold StackBoard.board;decide +kernel) (fun j unit => StackAccess.outside (DigitTable.outside j unit))
  have he224 := AppendEffect.expand he (total := 224) (by decide)
  refine ⟨d,n,r,hb,td,?_,h27,hc,?_,
    AppendEffect.accumulates he224 h.output h.capacity hf h.outputArena h.objectOutput hx,
    FormatLoopFrame.of_effect he hf⟩
  · have hh := ready (JsonFormatData.literal_nonzero nextIndex)
    rw [JsonFormatData.argument_end] at hh
    exact hh
  · simpa only [List.length_append] using StackFormatLayout.after_append h he224 hf

end E5R.Thermostat.StackJsonArgument
