/-
The `ptx_eval` simp set extended to phase derivations (`wpR`).
-/
import Ptx.Tactics.Eval
import Ptx.Logic.PhaseWp

namespace Ptx

attribute [ptx_eval] wpR_succ wpR_zero wpRAct_next wpRAct_load wpRAct_store wpRAct_atom
  wpRAct_atom_shared wpRAct_atom_b8 wpRAct_bar wpRAct_done wpRAct_fault wpRAct_ite atomic atomVal
  Heap.at_global Heap.at_shared Heap.set_global Heap.set_shared Launch.allocs_global
  Launch.allocs_shared Launch.sregions

end Ptx
