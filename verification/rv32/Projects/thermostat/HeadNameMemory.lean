import Projects.thermostat.HeadNameChecked
import Projects.thermostat.HeadFieldsView
import Projects.thermostat.HeadSavedTail
namespace E5R.Thermostat.HeadNameMemory
open E5R E5R.Thermostat HttpRequestSpec

/-- The one possible name-end scratch store is disjoint from fields, saved
    registers, metadata, application state and receive bytes. -/
theorem region (ram after : Word → BitVec 8) (sp : Word) (k off len : Nat)
    (effect : after=ram ∨ after=ramWrite ram (sp+4#32) (BitVec.ofNat 32 k) .w)
    (hb : off+len≤4294967296) (hs : off+len≤4 ∨ 8≤off) :
    ViewFrame.Region ram after (sp+BitVec.ofNat 32 off) len := by
  rcases effect with same | store
  · rw [same];intro _;rfl
  · rw [store];intro i
    exact StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 4 i.val j.val
      (by have hi := i.isLt;omega) (by have hj : j.val<4 := j.isLt;omega) (by have hi := i.isLt;have hj : j.val<4 := j.isLt;omega))

theorem word_frame (ram after : Word → BitVec 8) (sp : Word) (k off : Nat)
    (effect : after=ram ∨ after=ramWrite ram (sp+4#32) (BitVec.ofNat 32 k) .w)
    (hb : off+4≤4294967296) (hs : off+4≤4 ∨ 8≤off) :
    ramRead after (sp+BitVec.ofNat 32 off) .w=ramRead ram (sp+BitVec.ofNat 32 off) .w := by
  simpa only [BitVec.add_zero] using ViewFrame.word (region ram after sp k off 4 effect hb hs) 0 (by decide)

theorem saved {ram after : Word → BitVec 8} {sp : Word} {k : Nat} {values : Reg → Word}
    (effect : after=ram ∨ after=ramWrite ram (sp+4#32) (BitVec.ofNat 32 k) .w) (stored : HeadSaved.At ram sp values) :
    HeadSaved.At after sp values :=
  HeadSavedTail.preserve stored (region ram after sp k 332 52 effect (by decide) (by decide))

theorem fields {ram after : Word → BitVec 8} {sp : Word} {k : Nat} {f : Fields}
    (effect : after=ram ∨ after=ramWrite ram (sp+4#32) (BitVec.ofNat 32 k) .w) (view : HeadFieldsView.At ram sp f) :
    HeadFieldsView.At after sp f :=
  HeadFieldsView.preserve view (region ram after sp k 56 271 effect (by decide) (by decide))
end E5R.Thermostat.HeadNameMemory
