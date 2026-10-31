/- Axiom audit of the main theorems (scripts/check-lean-ptx.sh). -/
import Ptx
#print axioms Ptx.grid_sound
#print axioms Ptx.wp_sound
#print axioms Ptx.Safe.solo
#print axioms Ptx.Safe.loop
#print axioms Ptx.Examples.VectorAdd.vadd_correct
#print axioms Ptx.Examples.Sum.sum_correct
#print axioms Ptx.Examples.Map.saxpy_correct
#print axioms Ptx.Examples.Buggy.nobound_faults
#print axioms Ptx.Examples.Buggy.tid_races
#print axioms Ptx.Examples.Buggy.sub_wrong
