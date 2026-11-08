import Projects.thermostat.FormatValue
import Projects.thermostat.ViewFrame
namespace E5R.Thermostat.FormatTable
open E5R E5R.Thermostat

structure At (B : Board) (ram : Word → BitVec 8) (args : Word) (values : Fin 8 → FormatValue.Value) : Prop where
  object : Memory.Block B args 64
  aligned : args.toNat%4 = 0
  pointer : ∀ i : Fin 8, ramRead ram (args+BitVec.ofNat 32 (8*i.val)) .w = FormatValue.pointer (values i)
  method : ∀ i : Fin 8, ramRead ram ((args+BitVec.ofNat 32 (8*i.val))+4#32) .w = FormatValue.entry (values i)

theorem frame {B before after args values} (h : At B before args values)
    (hf : ViewFrame.Region before after args 64) : At B after args values := by
  refine ⟨h.object,h.aligned,?_,?_⟩
  · intro i
    exact (ViewFrame.word hf (8*i.val) (by have := i.isLt;omega)).trans (h.pointer i)
  · intro i
    have hh := ViewFrame.word hf (8*i.val+4) (by have := i.isLt;omega)
    have he : args+BitVec.ofNat 32 (8*i.val+4) = (args+BitVec.ofNat 32 (8*i.val))+4#32 := by
      rw [BitVec.ofNat_add,BitVec.add_assoc]
    rw [he] at hh
    exact hh.trans (h.method i)

theorem accessible {B ram args values} (h : At B ram args values) (i : Fin 8) :
    Memory.Block B (args+BitVec.ofNat 32 (8*i.val)) 8 ∧ (args+BitVec.ofNat 32 (8*i.val)).toNat%4 = 0 := by
  constructor
  · exact Memory.sub_block h.object (off := 8*i.val) (m := 8) (by decide) (by have := i.isLt;omega)
  · simpa only [←Nat.mul_assoc] using Memory.word_aligned args (2*i.val) h.aligned
end E5R.Thermostat.FormatTable
