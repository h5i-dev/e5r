import Projects.thermostat.JsonFormatData
namespace E5R.Thermostat.JsonFormatData
open E5R E5R.Thermostat

theorem literal_tag : ∀ i : Fin 9, tagByte ⟨2*i.val,by have := i.isLt;omega⟩ = BitVec.ofNat 8 (JsonProgram.literal i).length := by decide +kernel

theorem argument_tag : ∀ i : Fin 8, tagByte ⟨2*i.val+1,by have := i.isLt;omega⟩ = 192#8 := by decide +kernel

theorem literal_nonzero : ∀ i : Fin 9, (tagByte ⟨2*i.val,by have := i.isLt;omega⟩).toNat ≠ 0 := by decide +kernel

theorem final_tag : tagByte 17 = 0#8 := by decide +kernel
end E5R.Thermostat.JsonFormatData
