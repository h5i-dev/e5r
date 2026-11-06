/- Regression for the shared-memory relational bridge using the existing
concrete reduction entry and its checked phased execution derivations.
This is infrastructure validation, not an FP4 equivalence certificate. -/
import Ptx.Logic.RelationalPhases
import Ptx.Examples.Reduce

namespace Ptx.Examples.RelationalPhases
open Ptx Ptx.Relational

theorem concrete_shared_reduction (A : Reduce.Args) (hpre : A.Pre)
    (m : Mem) (sh : Dim3 → Mem) (r : Tid → String → Val) (p : Tid → String → Bool) :
    SharedEquivalent Reduce.K Reduce.K A.launch (Cfg.init r p m sh)
      (phaseWrites (A.phased m sh)) (phaseWrites (A.phased m sh)) := by
  apply shared_equivalent_of_phases (A.ok hpre m sh r p) (A.ok hpre m sh r p)
  · intro a
    exact not_false
  · intro a
    exact not_false
  · intro a
    exact Iff.rfl
  · intro t ht a hw
    exact ⟨t, ht, hw, rfl⟩

#print axioms concrete_shared_reduction
end Ptx.Examples.RelationalPhases
