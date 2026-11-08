import Projects.thermostat.EncodeValues
import Projects.thermostat.Subregion
namespace E5R.Thermostat.EncodeValueRegions
open E5R E5R.Thermostat

theorem regions {reply tuple a n s}
    (hr : WordRegions.Disjoint reply 10 a n) (ht : WordRegions.Disjoint tuple 8 a n) :
    ∀ i : Fin 8, WordRegions.Disjoint (FormatValue.pointer (EncodeValues.values reply tuple s i))
      (FormatValue.size (EncodeValues.values reply tuple s i)) a n := by
  intro i
  have hi := i.isLt
  have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 ∨ i.val=6 ∨ i.val=7 := by omega
  rcases hc with h0|h0|h0|h0|h0|h0|h0|h0
  · simp only [EncodeValues.values,h0,FormatValue.pointer,FormatValue.size]
    exact Subregion.left hr 4 2 (by decide)
  · simp only [EncodeValues.values,h0,FormatValue.pointer,FormatValue.size]
    exact Subregion.left hr 6 2 (by decide)
  · simp only [EncodeValues.values,h0,FormatValue.pointer,FormatValue.size]
    exact Subregion.left hr 8 1 (by decide)
  · simp only [EncodeValues.values,h0,FormatValue.pointer,FormatValue.size]
    simpa only [BitVec.add_zero] using Subregion.left hr 0 1 (by decide)
  · simp only [EncodeValues.values,h0,FormatValue.pointer,FormatValue.size]
    exact Subregion.left hr 1 1 (by decide)
  · simp only [EncodeValues.values,h0,FormatValue.pointer,FormatValue.size]
    exact Subregion.left hr 2 1 (by decide)
  · simp only [EncodeValues.values,h0,FormatValue.pointer,FormatValue.size]
    exact Subregion.left hr 3 1 (by decide)
  · simp only [EncodeValues.values,h0,FormatValue.pointer,FormatValue.size]
    exact ht
end E5R.Thermostat.EncodeValueRegions
