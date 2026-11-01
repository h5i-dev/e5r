/-
Symbolic evaluation of `wp` on a concrete kernel.

`simp only [ptx_eval, K]` rewrites `wp … (f + 1) s m` with `wp_succ`, computes
the next action of `s` from the kernel's statement list, and continues until
the program reaches `done`, a cut point, or a branch condition it cannot
decide. What is left is the verification condition: access legality,
footprint membership and the postcondition, over the symbolic register
values. Every rewrite is a definitional unfolding or a proved lemma, so the
evaluation is part of the proof, not trusted.
-/
import Ptx.Tactics.Attr
import Ptx.Logic.Regions

namespace Ptx

attribute [ptx_eval] wp_succ wp_zero action exec opVal fit Ty.width Ty.signed
  TState.set TState.setp TState.skip guardHolds jump Kernel.label? lookupLabel cmpVal atWidth
  shiftBy convert upd Ctx.sreg Dim3.get Launch.ctx lo32_ext32 Size.bytes
  wpAct_next wpAct_load wpAct_store wpAct_done wpAct_fault wpAct_ite
  List.getElem?_cons_succ List.getElem?_cons_zero List.getElem?_nil
  Bool.false_eq_true beq_self_eq_true beq_iff_eq Option.map_some Option.map
  String.reduceEq Nat.reduceAdd Nat.reduceBEq Nat.reduceBNe reduceIte Prod.snd Prod.fst
  Ty.size reduceCtorEq dataAddr wpAct_bar wpAct_atom wpAct_load_shared wpAct_store_shared

end Ptx
