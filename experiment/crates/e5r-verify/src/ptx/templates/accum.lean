/-
@HEADER@
-/
import Ptx.Auto.Accum

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace E5rCheck
open Ptx Ptx.Auto Ptx.Auto.Accum

@KERNEL_DEF@
@SPEC_DEF@
theorem obligation : Accum.Obligation spec @K@ @N@ := by
  intro A hpre m₀ sh₀ t ht s hs
  obtain ⟨pc, r, p⟩ := s
  simp only at hs; subst hs
  obtain ⟨hGB, fx, xal, fout, oal, hsep⟩ := hpre
  simp only [spec_k, Nat.one_mul, Nat.mul_one] at fx xal fout oal hsep
  obtain ⟨hc, hi, -, -, -, -⟩ := (A.launch_oneD).thread ht
  have hcB := gid_lt_of hc hi
  have hcB' : t.ctaid.x.toNat * A.B.toNat < 2 ^ 32 := by omega
  refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
  simp only [ptx_eval, @K@, Accum.Args.launch, Accum.Args.params, spec_input, spec_output,
    spec_length, spec_k, spec_sz, Phased.J, Accum.phased, Accum.foot, Accum.gid, Accum.Args.elt,
    List.map_cons, List.map_nil, Nat.one_mul, Nat.mul_one]
  ptx_branches4
  all_goals ptx_addrs4 [A.x, A.out] [@IDX@, 0]
  all_goals (try and_intros)
  all_goals first
    | exact trivial
    | rfl
    | (intro _ h; exact h.elim)
    | (exfalso; omega)
@ACCESS@
    | exact elem_zero _
    | exact fun y hy => .inl ⟨rfl, by omega, hy⟩
    | exact fun y hy => .inl ⟨trivial, by omega, hy⟩
    | (funext a
       have hn : ¬ (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat ∧ a = A.out) :=
         fun h => absurd h.1 (by omega)
       simp only [hn, ↓reduceIte])
    | (refine ⟨_, @ACCUM@ _, fun v => ⟨?_, fun _ h => h.elim, trivial⟩⟩
       rw [acc_e _ _ @TRUNC@]
       funext a
       simp only [elem_zero]
       by_cases ha : a = A.out
       · subst ha
         simp only [show t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat by omega, and_self,
           ↓reduceIte, @VALSIMP@]
       · simp only [ha, and_false, ↓reduceIte])
  done

theorem correct : Accum.Correct spec @K@ := correct_of obligation

end E5rCheck

#print axioms E5rCheck.correct
