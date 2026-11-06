/- e5r-proof ptx=96e5da6355319cc83fe1a89c4faa72a145b8249f22f3eced208b6acdc3cb7b42 spec=c649e95400f87122a5574ce3654846e3ed4d48215daa0667315c91dae14989a3 toolchain=leanprover/lean4:v4.35.0 -/
import E5rSpec
import Ptx.Auto.Tactic
set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
namespace E5rProof
open Ptx Ptx.Auto Ptx.Auto.ZeroSegments Ptx.Auto.ZeroSegments.Spec
abbrev S := E5rSpec.domain
abbrev K₀ := E5rSpec.Original._ZN7NKernel21ZeroSegmentStartsImplIjEEvPKjjjPT_
abbrev K₁ := E5rSpec.Optimized._ZN7NKernel21ZeroSegmentStartsImplIjEEvPKjjjPT_

theorem lo32_cast (v : BitVec 32) : lo32 (v.setWidth 64) = v := by
  simp [lo32]

theorem lo32_five : lo32 (5 : Val) = (5#32) := rfl

theorem lo32_nat (n : Nat) : lo32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  simp [lo32]

theorem shl64_two (v : Val) : v <<< 2 = v * 4 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_mul]

theorem paired (A : Args) (hp : S.Pre A) (m : Mem)
    (r : Tid → String → Val) (p : Tid → String → Bool) :
    Relational.Paired K₀ K₁ (S.launch A)
      (fun t => S.R A (gid A.B t)) (fun t => S.W A (gid A.B t)) r p m := by
  apply Relational.paired_of_safe
  intro t ht
  have hd := S.oneD A
  obtain ⟨hc,htt,hy,hz,hty,htz⟩ := hd.thread ht
  have hg := hd.gid_lt ht
  obtain ⟨fi,fo,ai,ao,sep,hnsmall,hn,hmax⟩ := hp
  have hp : S.Pre A := ⟨fi,fo,ai,ao,sep,hnsmall,hn,hmax⟩
  have hBc : A.B.toNat * t.ctaid.x.toNat = t.ctaid.x.toNat * A.B.toNat := Nat.mul_comm _ _
  have hg32 := hd.gid_bv ht hmax
  have hprod : t.ctaid.x.toNat * A.B.toNat % 4294967296 = t.ctaid.x.toNat * A.B.toNat :=
    Nat.mod_eq_of_lt (by unfold gid at hg; omega)
  have hsum : (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) % 4294967296 = t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat :=
    Nat.mod_eq_of_lt (by unfold gid at hg; omega)
  unfold gid at *
  have castidx : (t.ctaid.x * A.B + t.tid.x).setWidth 64 =
      BitVec.ofNat 64 (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, hg32, BitVec.toNat_ofNat]
  have addr (base : Addr) : base + (t.ctaid.x * A.B + t.tid.x).setWidth 64 * 4 =
      elem base (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) := by
    simp only [castidx, elem, BitVec.ofNat_mul]
    exact congrArg (base + ·) (BitVec.mul_comm _ _)
  have addr_lit (base : Addr) : base + (t.ctaid.x * A.B + t.tid.x).setWidth 64 * (4#64) =
      elem base (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) := addr base
  let Q : Mem → Prop := fun M₀ =>
    Safe K₁ (S.launch A).alloc ((S.launch A).ctx t)
      (S.R A (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat))
      (S.W A (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat))
      (fun s M₁ => action K₁ ((S.launch A).ctx t) s = .done ∧
        ∀ x, S.W A (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) x → M₀ x = M₁ x)
      (s0 r p m t) m
  change Safe K₀ _ _ _ _ (fun s M => action K₀ ((S.launch A).ctx t) s = .done ∧ Q M) _ _
  refine (wp_sound (f := 48) (cut := fun _ => false) ?_).weaken
    fun s m h => ⟨h.2.resolve_left (by simp),h.1⟩
  simp only [ptx_eval, List.find?, lo32_five, lo32_nat, BitVec.reduceOfInt, BitVec.reduceBEq, BitVec.reduceBNe, BitVec.reduceAnd, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceLT, BitVec.reduceEq, BitVec.reduceSLT, BitVec.reduceSLE, BitVec.reduceULT, BitVec.reduceULE, BitVec.reduceSetWidth, Bool.or_false, Bool.bne_false, K₀, E5rSpec.Original._ZN7NKernel21ZeroSegmentStartsImplIjEEvPKjjjPT_, launch, S, E5rSpec.domain, s0, Cfg.init]
  simp only [ext32, BitVec.reduceSetWidth, BitVec.reduceToNat, (show min 2 64 = 2 from rfl),
      BitVec.add_zero, shl64_two]
  simp only [addr_lit, addr]
  simp only [ule_toNat, hg32, decide_eq_true_eq]
  repeat' split

  all_goals (try and_intros)
  all_goals (first
    | trivial
    | (simpa only [launch,S,E5rSpec.domain] using (access_input hp (i := t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) (by omega)))
    | (simpa only [launch,S,E5rSpec.domain] using (access_output hp (i := t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) (by omega)))
    | (simpa only [S,E5rSpec.domain] using (load_foot (S := S) (A := A) (i := t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) (by omega)))
    | (simpa only [S,E5rSpec.domain] using (store_foot (S := S) (A := A) (i := t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) (by omega)))
    | skip)
  all_goals (
    change Q _
    unfold Q
    refine (wp_sound (f := 48) (cut := fun _ => false) ?_).weaken
      fun s m h => ⟨h.2.resolve_left (by simp),h.1⟩
    simp only [ptx_eval, List.find?, lo32_five, lo32_nat, BitVec.reduceOfInt, BitVec.reduceBEq, BitVec.reduceBNe, BitVec.reduceAnd, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceLT, BitVec.reduceEq, BitVec.reduceSLT, BitVec.reduceSLE, BitVec.reduceULT, BitVec.reduceULE, BitVec.reduceSetWidth, Bool.or_false, Bool.bne_false, K₁, E5rSpec.Optimized._ZN7NKernel21ZeroSegmentStartsImplIjEEvPKjjjPT_, launch, S, E5rSpec.domain, s0, Cfg.init]
    simp only [ext32, BitVec.reduceSetWidth, BitVec.reduceToNat, (show min 2 64 = 2 from rfl),
      BitVec.add_zero, shl64_two]
    simp only [addr_lit, addr]
    simp only [ule_toNat, hg32, decide_eq_true_eq]
    clear addr addr_lit castidx
    simp_all only [Bool.not_eq_true, reduceIte, implies_true, forall_const]
  
    all_goals (try and_intros)
    all_goals (first
      | trivial
      | (simpa only [launch,S,E5rSpec.domain] using (access_input hp (i := t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) (by omega)))
      | (simpa only [launch,S,E5rSpec.domain] using (access_output hp (i := t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) (by omega)))
      | (simpa only [S,E5rSpec.domain] using (load_foot (S := S) (A := A) (i := t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) (by omega)))
      | (simpa only [S,E5rSpec.domain] using (store_foot (S := S) (A := A) (i := t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) (by omega)))
      | skip)
    all_goals (try (intro x hx; rfl))
  )

theorem correct : E5rSpec.statement := by
  intro A m sh r p hp
  exact Relational.equivalent_of_paired rfl rfl (paired A hp m r p) (S.disjoint hp) sh
end E5rProof
