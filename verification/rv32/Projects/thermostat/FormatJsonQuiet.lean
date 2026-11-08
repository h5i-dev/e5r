-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.FormatJson
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.FormatEngineEndQuiet
import Projects.thermostat.FormatEngineEnterQuiet
import Projects.thermostat.FormatEngineExitQuiet
import Projects.thermostat.JsonLoopQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.FormatJson
theorem contract_quiet (c : Core) (ram : Word → BitVec 8) (p obj args dst : Word)
    (cap : Nat) (values : Fin 8 → FormatValue.Value) (s : Spec.Snapshot)
    (hp : c.pc = 0x80004976#32) (hsp : c.get 2 = p+224#32)
    (h10 : c.get 10 = obj) (h11 : c.get 11 = 0x80005c04#32)
    (h12 : c.get 12 = 0x8000574b#32) (h13 : c.get 13 = args)
    (h : FormatLayout.Layout ram p obj args dst cap 0 values)
    (hv : ∀ i, FormatValue.bytes (values i) = JsonProgram.argument s i)
    (hf : (ReplyJson.snapshot s).length ≤ cap) :
    ∃ d n r, n ≤ 3836 ∧ Quiet.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      FormatCursor.Returned c d ∧ d.get 10 = 0#32 ∧
      FormatLayout.Layout r p obj args dst cap (ReplyJson.snapshot s).length values ∧
      Bytes.Span UartPlatform.board r dst (ReplyJson.snapshot s) ∧
      (∀ x, (∀ i : Fin 224, x ≠ p+BitVec.ofNat 32 i.val) →
        (∀ i : Fin cap, x ≠ dst+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 12, x ≠ obj+BitVec.ofNat 32 i.val) → r x = ram x) := by
  have hm := Memory.sub_block h.arena (off := 160) (m := 64) (by decide) (by decide)
  have ha := Memory.word_aligned p 40 h.aligned
  have hsp' : c.get 2 = (p+160#32)+64#32 := by
    simpa only [BitVec.add_assoc,show (160#32+64#32)=224#32 by decide +kernel] using hsp
  have htag := JsonFormatData.tag (0:Fin 18) ram
  have htagsep : WordRegions.Disjoint 0x8000574b#32 1 (p+160#32) 64 := by
    apply WordRegions.outside_ram
    · intro i
      have hi : i.val = 0 := by have := i.isLt;omega
      have hh := (JsonFormatData.tag_layout (0:Fin 18)).2.2
      change UartPlatform.board.inRam 0x8000574b#32 1 = false at hh
      simpa only [hi,show BitVec.ofNat 32 0 = 0#32 from rfl,BitVec.add_zero] using hh
    · exact hm
  obtain ⟨a,ta,har,hac,ha27⟩ := E5R.Thermostat.FormatEngineEnter.contract_quiet UartPlatform.board c ram (p+160#32) obj args 0x8000574b#32
    (JsonFormatData.tagByte 0) hp hsp' h10 h11 h13 h12 hm ha (FormatBits.even args h.table.aligned)
    htag (JsonFormatData.literal_nonzero (0:Fin 9)) htagsep FormatLiterals.cursor_method_outside
  let saved := FormatEngineSave.memory ram (p+160#32) c
  have hsaved := FormatLayout.saved h c
  have hfit : ([] : List (BitVec 8)).length+(JsonSequence.suffix values 8).length ≤ cap := by
    simp only [List.length_nil,Nat.zero_add]
    exact Nat.le_trans (Nat.le_of_eq (congrArg List.length (JsonSequence.snapshot (s := s) (values := values) hv))) hf
  have har0 : FormatEngineReady.Ready a (p+160#32) obj args (JsonFormatData.tagPointer ⟨2*(8-8),by decide⟩)
      (8-8) (JsonFormatData.tagByte ⟨2*(8-8),by decide⟩) := by
    simpa only [show (8:Nat)-8=0 by decide,show (2:Nat)*0=0 by decide,show (⟨0,by decide⟩:Fin 18) = 0 by decide +kernel,
      show JsonFormatData.tagPointer (0:Fin 18) = 0x8000574b#32 by decide +kernel] using har
  obtain ⟨z,n,r,hn,tz,zpc,zsp,z27,zc,hl,hs,fr⟩ := E5R.Thermostat.JsonLoop.contract_quiet 8 (by decide) a saved p obj args dst cap [] values har0 hsaved
    (Bytes.empty _ _ _) hfit
  obtain ⟨u,tu,upc,u10,ur,uc⟩ := E5R.Thermostat.FormatEngineEnd.contract_quiet UartPlatform.board z r zpc
  have usp : u.get 2 = p+160#32 := (ur 2 (by decide)).trans zsp
  have u27 : u.get 27 = c.get 27 := ((ur 27 (by decide)).trans z27).trans ha27
  have ucsr : u.sameCsr c := ((uc.trans zc).trans hac)
  have hregion : ViewFrame.Region saved r (p+176#32) 48 := FormatLoopFrame.region fr
    (by simpa only [BitVec.add_zero] using FormatSpace.offsets_disjoint p 176 48 0 176 (by decide) (by decide) (by decide))
    (WordRegions.symm (Subregion.right h.outputArena 176 48 (by decide)))
    (WordRegions.symm (Subregion.right h.objectArena 176 48 (by decide)))
  have hregion' : ViewFrame.Region saved r ((p+160#32)+16#32) 48 := by
    simpa only [BitVec.add_assoc,show (160#32+16#32)=176#32 by decide +kernel] using hregion
  obtain ⟨d,td,hd,d10⟩ := E5R.Thermostat.FormatEngineExit.contract_quiet UartPlatform.board c u ram r (p+160#32)
    upc usp hsp' hm ha ucsr u27 hregion'
  refine ⟨d,28+n+2+14,r,by omega,((ta.trans tz).trans tu).trans td,hd,d10.trans u10,?_,?_,?_⟩
  · simpa only [List.nil_append,JsonSequence.snapshot hv] using hl
  · simpa only [List.nil_append,JsonSequence.snapshot hv] using hs
  · intro x hx hout hobj
    apply Eq.trans (fr x (fun i => hx ⟨i.val,by have := i.isLt;omega⟩) hout hobj)
    exact FormatEngineSave.frame ram (p+160#32) c x (by
      intro i
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨160+i.val,by have := i.isLt;omega⟩)

end E5R.Thermostat.FormatJson
