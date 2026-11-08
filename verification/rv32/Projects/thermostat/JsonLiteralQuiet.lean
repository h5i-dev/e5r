-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.JsonLiteral
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.FormatLiteralPieceQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.JsonLiteral
theorem contract_quiet (c : Core) (ram : Word → BitVec 8) (p obj args dst : Word)
    (cap : Nat) (litPrefix : List (BitVec 8)) (values : Fin 8 → FormatValue.Value) (i : Fin 9)
    (hr : FormatEngineReady.Ready c (p+160#32) obj args (JsonFormatData.tagPointer ⟨2*i.val,by have := i.isLt;omega⟩)
      i.val (JsonFormatData.tagByte ⟨2*i.val,by have := i.isLt;omega⟩))
    (h : FormatLayout.Layout ram p obj args dst cap litPrefix.length values)
    (hx : Bytes.Span UartPlatform.board ram dst litPrefix)
    (hf : litPrefix.length+(JsonProgram.literal i).length ≤ cap) :
    ∃ d n r, n ≤ 144 ∧ Quiet.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      d.pc = FormatEngineNext.resultPc (JsonFormatData.tagByte ⟨2*i.val+1,by have := i.isLt;omega⟩) ∧
      d.get 2 = p+160#32 ∧
      ((JsonFormatData.tagByte ⟨2*i.val+1,by have := i.isLt;omega⟩).toNat ≠ 0 →
        FormatEngineReady.Ready d (p+160#32) obj args (JsonFormatData.tagPointer ⟨2*i.val+1,by have := i.isLt;omega⟩)
          i.val (JsonFormatData.tagByte ⟨2*i.val+1,by have := i.isLt;omega⟩)) ∧
      d.get 27 = c.get 27 ∧ d.sameCsr c ∧
      FormatLayout.Layout r p obj args dst cap (litPrefix++JsonProgram.literal i).length values ∧
      Bytes.Span UartPlatform.board r dst (litPrefix++JsonProgram.literal i) ∧ FormatLoopFrame.Frame ram r p obj dst cap := by
  let desc := JsonFormatData.tagPointer ⟨2*i.val,by have := i.isLt;omega⟩
  let nxt := JsonFormatData.tagByte ⟨2*i.val+1,by have := i.isLt;omega⟩
  have hlen := (JsonProgram.literal_lengths i).2
  have hl := FormatSpace.cursor h.toSpace 128 (by decide) (by decide) (JsonFormatData.literalPointer i)
    (JsonProgram.literal i) (JsonFormatData.literal_span i ram) hlen (fun j => ((JsonFormatData.literal_layout i).2.2 j).2)
  rw [JsonFormatData.literal_start] at hl
  have hr' : FormatEngineReady.Ready c ((p+128#32)+32#32) obj args desc i.val (BitVec.ofNat 8 (JsonProgram.literal i).length) := by
    simpa only [BitVec.add_assoc,show (128#32+32#32)=160#32 by decide +kernel,JsonFormatData.literal_tag,desc] using hr
  have hn : ReadBytes.Byte UartPlatform.board img ram ((desc+1#32)+BitVec.ofNat 32 (JsonProgram.literal i).length) nxt := by
    rw [←JsonFormatData.literal_start,JsonFormatData.literal_end]
    exact JsonFormatData.tag _ ram
  have hro : UartPlatform.board.inRam ((desc+1#32)+BitVec.ofNat 32 (JsonProgram.literal i).length) 1 = false := by
    rw [←JsonFormatData.literal_start,JsonFormatData.literal_end]
    exact (JsonFormatData.tag_layout _).2.2
  obtain ⟨d,n,r,hb,td,hpc,hsp,ready,h27,hc,he⟩ := E5R.Thermostat.FormatLiteralPiece.contract_quiet UartPlatform.board c ram (p+128#32) obj args desc dst cap litPrefix.length i.val
    (JsonProgram.literal i) nxt hr' hl hf hn hro
  have he176 := AppendEffect.widen he (total := 176) (by decide)
  have he224 := AppendEffect.expand he176 (total := 224) (by decide)
  refine ⟨d,n,r,by omega,td,hpc,?_,?_,h27,hc,?_,
    AppendEffect.accumulates he224 h.output h.capacity hf h.outputArena h.objectOutput hx,
    FormatLoopFrame.of_effect he176 hf⟩
  · simpa only [BitVec.add_assoc,show (128#32+32#32)=160#32 by decide +kernel] using hsp
  · intro hnz
    have hh := ready hnz
    rw [←JsonFormatData.literal_start,JsonFormatData.literal_end] at hh
    simpa only [BitVec.add_assoc,show (128#32+32#32)=160#32 by decide +kernel] using hh
  · simpa only [List.length_append] using FormatLayout.after_append h he224 hf

end E5R.Thermostat.JsonLiteral
