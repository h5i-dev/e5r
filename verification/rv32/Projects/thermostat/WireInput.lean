import Projects.thermostat.PathDispatch
import Projects.thermostat.Param
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.WireInput
open E5R E5R.Thermostat

/-- First capture, tied to the same actual path view as path selection. -/
inductive Params (B : Board) (ram : Word → BitVec 8) (req p : Word) (path : List (BitVec 8)) :
    Option (List (BitVec 8)) → Prop
  | missing (object : Memory.Block B req 372) (aligned : req.toNat%4 = 0)
      (count : ramRead ram (req+368#32) .w = 0#32) : Params B ram req p path none
  | present {s e count : Nat} (capture : ParamInput.Capture B ram req p path s e count) :
      Params B ram req p path (some (ParamInput.captured path s e))

theorem Params.as_pre {B ram req p path first} (h : Params B ram req p path first) : Param.Pre B ram req first := by
  cases h with
  | missing hm ha hz => exact .missing hm ha hz
  | present hc => exact .present hc

def Separate (req sp : Word) : Prop := ∀ i : Fin 372, ∀ j : Fin 16,
  req+BitVec.ofNat 32 i.val ≠ sp+BitVec.ofNat 32 j.val

theorem word_saved (ram : Word → BitVec 8) (sp req : Word) (c : Core) (k : Nat)
    (hk : k+4 ≤ 372) (hs : Separate req sp) :
    ramRead (DecodeSave.memory ram sp c) (req+BitVec.ofNat 32 k) .w = ramRead ram (req+BitVec.ofNat 32 k) .w := by
  apply DecodeInput.word_preserved
  intro i j
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  exact hs ⟨k+i.val,by have := i.isLt;omega⟩ j

theorem path_saved {B ram req p path} (h : PathDispatch.PathAt B ram req p path) (sp : Word) (c : Core)
    (hs : Separate req sp)
    (hp : ∀ i : Fin path.length, ∀ j : Fin 16, p+BitVec.ofNat 32 i.val ≠ sp+BitVec.ofNat 32 j.val) :
    PathDispatch.PathAt B (DecodeSave.memory ram sp c) req p path :=
  ⟨h.object,h.aligned,(word_saved ram sp req c 304 (by decide) hs).trans h.pointer,
    (word_saved ram sp req c 308 (by decide) hs).trans h.length,DecodeSave.preserves_span h.bytes sp c hp⟩

theorem params_saved {B ram req p path first} (h : Params B ram req p path first) (sp : Word) (c : Core)
    (hs : Separate req sp)
    (hp : ∀ i : Fin path.length, ∀ j : Fin 16, p+BitVec.ofNat 32 i.val ≠ sp+BitVec.ofNat 32 j.val) :
    Params B (DecodeSave.memory ram sp c) req p path first := by
  have hw (k : Nat) (hk : k+4 ≤ 372) := word_saved ram sp req c k hk hs
  cases h with
  | missing hm ha hz => exact .missing hm ha ((hw 368 (by decide)).trans hz)
  | present hc =>
    exact .present ⟨hc.object,hc.aligned,(hw 368 (by decide)).trans hc.count_word,hc.count_bound,
      (hw 304 (by decide)).trans hc.path_pointer,(hw 308 (by decide)).trans hc.path_length,
      (hw 336 (by decide)).trans hc.start_word,(hw 340 (by decide)).trans hc.finish_word,
      hc.ordered,hc.bounded,DecodeSave.preserves_span hc.bytes sp c hp⟩

theorem body_separate {req sp} (h : Separate req sp) : DecodeInput.Separate req sp := by
  intro i j;exact h ⟨i.val,by have := i.isLt;omega⟩ j
end E5R.Thermostat.WireInput
