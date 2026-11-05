/- e5r-proof ptx=c3c6482c6b1ef57291f94e316ddae0741c096cd6c354f55f6d296f2691685c23 spec=fa5b1d93e0c1d7d3c5917bd4ae5df27c63b7860a4de9dbc7d89474ab6094ff11 toolchain=leanprover/lean4:v4.35.0 -/
import E5rSpec
import Ptx.Auto.Tactic
set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
namespace E5rProof
open Ptx Ptx.Auto Ptx.Auto.Equivalence Ptx.Auto.Equivalence.Spec
abbrev S := E5rSpec.domain
abbrev K₀ := E5rSpec.Original.unpack4
abbrev K₁ := E5rSpec.Optimized.unpack4

-- A direct arithmetic relation between the actual instruction expressions.
-- No algorithm specification or independent correctness theorem is used.
theorem spread_relation (x : BitVec 32) :
    let z := x &&& (15#32)
    let b := bfi32 z z 14 4
    ((b <<< (7 : Nat)) ||| b) &&& (16843009#32) =
      (z * (2113665#32)) &&& (16843009#32) := by
  dsimp only
  have hz : (x &&& (15#32)).toNat < 16 := by
    have hm : (x &&& (15#32)).toNat = x.toNat % 16 := by
      simpa only [BitVec.toNat_and, BitVec.reduceToNat, Nat.reducePow, Nat.reduceSub] using
        Nat.and_two_pow_sub_one_eq_mod x.toNat 4
    rw [hm]
    exact Nat.mod_lt _ (by decide)
  generalize he : x &&& (15#32) = z at *
  have cases : z.toNat = 0 ∨ z.toNat = 1 ∨ z.toNat = 2 ∨ z.toNat = 3 ∨ z.toNat = 4 ∨ z.toNat = 5 ∨ z.toNat = 6 ∨ z.toNat = 7 ∨ z.toNat = 8 ∨ z.toNat = 9 ∨ z.toNat = 10 ∨ z.toNat = 11 ∨ z.toNat = 12 ∨ z.toNat = 13 ∨ z.toNat = 14 ∨ z.toNat = 15 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals have hz' : z = BitVec.ofNat 32 z.toNat := by simp
  all_goals rw [hz', h]
  all_goals decide

theorem paired (A : Args) (hp : S.Pre A) (m : Mem)
    (r : Tid → String → Val) (p : Tid → String → Bool) :
    Relational.Paired K₀ K₁ (S.launch A)
      (fun t => S.R A (gid A.B t)) (fun t => S.W A (gid A.B t)) r p m := by
  apply Relational.paired_of_safe
  intro t ht
  have hd := S.oneD A
  obtain ⟨hc,htt,hy,hz,hty,htz⟩ := hd.thread ht
  have hg := hd.gid_lt ht
  obtain ⟨fi,fo,ai,ao,sep,htail,hn,hmax⟩ := hp
  have hp : S.Pre A := ⟨fi,fo,ai,ao,sep,htail,hn,hmax⟩
  have hBc : A.B.toNat * t.ctaid.x.toNat = t.ctaid.x.toNat * A.B.toNat := Nat.mul_comm _ _
  have hg32 := hd.gid_bv ht hmax
  have hprod : t.ctaid.x.toNat * A.B.toNat % 4294967296 = t.ctaid.x.toNat * A.B.toNat :=
    Nat.mod_eq_of_lt (by unfold gid at hg; omega)
  have hsum : (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) % 4294967296 = t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat :=
    Nat.mod_eq_of_lt (by unfold gid at hg; omega)
  unfold gid at *
  let Q : Mem → Prop := fun M₀ =>
    Safe K₁ (S.launch A).alloc ((S.launch A).ctx t)
      (S.R A (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat))
      (S.W A (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat))
      (fun s M₁ => action K₁ ((S.launch A).ctx t) s = .done ∧
        ∀ x, S.W A (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) x → M₀ x = M₁ x)
      (s0 r p m t) m
  change Safe K₀ _ _ _ _ (fun s M => action K₀ ((S.launch A).ctx t) s = .done ∧ Q M) _ _
  refine (wp_sound (f := 40) (cut := fun _ => false) ?_).weaken
    fun s m h => ⟨h.2.resolve_left (by simp),h.1⟩
  simp only [ptx_eval, K₀, E5rSpec.Original.unpack4, launch, S, E5rSpec.domain, s0, Cfg.init]
  ptx_addrs [A.base "unpack4_param_0", A.base "unpack4_param_1"]
    [t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat, (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)/8]
  ptx_branches
  all_goals (try simp only [hprod,hsum])
  all_goals (try and_intros)
  all_goals (first
    | trivial
    | (simpa only [launch,S,E5rSpec.domain] using (access_input hp (i := t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) (by omega)))
    | (simpa only [launch,S,E5rSpec.domain] using (access_output hp (i := t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) (by omega)))
    | (exact load_foot (S := S) (by omega))
    | (exact store_foot (S := S) (by omega))
    | skip)
  all_goals (
    change Q _
    unfold Q
    refine (wp_sound (f := 40) (cut := fun _ => false) ?_).weaken
      fun s m h => ⟨h.2.resolve_left (by simp),h.1⟩
    simp only [ptx_eval, K₁, E5rSpec.Optimized.unpack4, launch, S, E5rSpec.domain, s0, Cfg.init]
    ptx_addrs [A.base "unpack4_param_0", A.base "unpack4_param_1"]
      [t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat, (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)/8]
    ptx_branches
    all_goals (try simp only [hprod,hsum] at *)
    all_goals (try and_intros)
    all_goals (first
      | trivial
      | (simpa only [launch,S,E5rSpec.domain] using (access_input hp (i := t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) (by omega)))
      | (simpa only [launch,S,E5rSpec.domain] using (access_output hp (i := t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) (by omega)))
      | (exact load_foot (S := S) (by omega))
      | (exact store_foot (S := S) (by omega))
      | skip)
    all_goals (
      intro x hx
      first
      | rfl
      | (exfalso; omega)
      | (simpa only [lo32, BitVec.reduceOfInt, BitVec.reduceSetWidth, BitVec.reduceToNat,
            (show min 2 32 = 2 from rfl), (show min 7 32 = 7 from rfl)] using
          congrArg (fun v : BitVec 32 => wr m
            (elem (A.base "unpack4_param_1") (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat))
            .b4 (ext32 v) x)
            (spread_relation ((lo32 (rd m
              (elem (A.base "unpack4_param_0") ((t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)/8)) .b4)) >>>
              (min (((t.ctaid.x * A.B + t.tid.x) <<< (2 : Nat)) &&& (28#32)).toNat 32))))
    )
  )

theorem correct : E5rSpec.statement := by
  intro A m sh r p hp
  exact Relational.equivalent_of_paired rfl rfl (paired A hp m r p) (S.disjoint hp) sh
end E5rProof
