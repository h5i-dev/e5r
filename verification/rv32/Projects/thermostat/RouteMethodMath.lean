import Projects.thermostat.Literal
set_option autoImplicit false
namespace E5R.Thermostat.RouteMethodMath
open E5R E5R.Thermostat
/-- The special HEAD/GET fallback cannot accept a non-GET registered method:
    OR with its nonzero discriminant remains nonzero before SEQZ. -/
theorem refuse (x wanted : Word) (nonzero : wanted≠0#32) : alu .sltu (x ||| wanted) 1#32=0#32 := by
  have word : x ||| wanted≠0#32 := fun equal => nonzero (BitVec.or_eq_zero_iff.mp equal).2
  have notZero : (x ||| wanted).toNat≠0 := by
    intro zero
    apply word
    exact BitVec.eq_of_toNat_eq zero
  have positive : 0<(x ||| wanted).toNat := by omega
  change (if (x ||| wanted).ult 1#32 then 1#32 else 0#32)=0#32
  have no : (x ||| wanted).ult 1#32=false := by
    simp only [BitVec.ult,BitVec.toNat_ofNat]
    exact decide_eq_false (by omega)
  rw [no];rfl
end E5R.Thermostat.RouteMethodMath
