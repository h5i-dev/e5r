/- e5r-proof ptx=fcf5f87efb33363196b9578518bc9d63d7eb3054bf96ee58023a9bdb60b22a89 spec=7bc6eda04200f678cee3c5f88425d1597a48c622bfa1aa3715caff957f3e8a16 toolchain=leanprover/lean4:v4.35.0 -/
import E5rSpec
import Ptx.Auto.Tactic
set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
namespace E5rProof
open Ptx Ptx.Auto Ptx.Auto.OssInc Ptx.Auto.OssInc.Spec
abbrev S := E5rSpec.domain
abbrev K₀ := E5rSpec.Original._Z9incKernelPiS_ii
abbrev K₁ := E5rSpec.Optimized._Z9incKernelPiS_ii

theorem lo32_cast (v : BitVec 32) : lo32 (v.setWidth 64) = v := by
  simp [lo32]

theorem lo32_five : lo32 (5 : Val) = (5#32) := rfl

theorem lo32_nat (n : Nat) : lo32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  simp [lo32]

theorem input_read_frame (A : Args) (hp : S.Pre A)
    {i j : Nat} (hi : i < A.n.toNat) (hj : j < A.n.toNat) (m : Mem) (v : Val) :
    rd32 (wr m (elem (A.base S.output) j) .b4 v) (elem (A.base S.input) i) =
      rd32 m (elem (A.base S.input) i) := by
  exact rd32_wr_disjoint (fun x hx => elem_disjoint₂ hp.1 hp.2.1 hp.2.2.2.2.1 hi hj hx)

theorem wr_same_twice (m : Mem) (a : Addr) (sz : Size) (v : Val) :
    wr (wr m a sz v) a sz v = wr m a sz v := by
  funext x
  by_cases h : covers a sz.bytes x
  · rw [wr_inside h, wr_inside h]
  · simp only [wr_outside h]

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
  have sign : (t.ctaid.x * A.B + t.tid.x).signExtend 64 =
      BitVec.ofNat 64 (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) := by
    have msb : (t.ctaid.x * A.B + t.tid.x).msb = false := by
      rw [BitVec.msb_eq_decide, hg32]
      exact decide_eq_false (by omega)
    rw [BitVec.signExtend_eq_setWidth_of_msb_false msb]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, hg32, BitVec.toNat_ofNat]
  have addr (base : Addr) : base + (t.ctaid.x * A.B + t.tid.x).signExtend 64 *
      (4#32).signExtend 64 + (0#64) =
      elem base (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) := by
    simp only [sign, BitVec.reduceSignExtend, BitVec.add_zero, elem, BitVec.ofNat_mul]
    exact congrArg (base + ·) (BitVec.mul_comm _ _)
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
  simp only [ptx_eval, lo32_five, lo32_nat, BitVec.reduceOfInt, BitVec.reduceBEq, BitVec.reduceBNe, BitVec.reduceAnd, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceLT, BitVec.reduceEq, BitVec.reduceSLT, BitVec.reduceSLE, BitVec.reduceULT, BitVec.reduceULE, BitVec.reduceSetWidth, Bool.or_false, Bool.bne_false, K₀, E5rSpec.Original._Z9incKernelPiS_ii, launch, S, E5rSpec.domain, s0, Cfg.init]
  simp only [addr]
  split <;> (rename_i hcond; ptx_cond_simp hcond)
  all_goals (try simp only [hprod,hsum] at hcond)
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
    refine (wp_sound (f := 48) (cut := fun _ => false) ?_).weaken
      fun s m h => ⟨h.2.resolve_left (by simp),h.1⟩
    simp only [ptx_eval, lo32_five, lo32_nat, BitVec.reduceOfInt, BitVec.reduceBEq, BitVec.reduceBNe, BitVec.reduceAnd, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceLT, BitVec.reduceEq, BitVec.reduceSLT, BitVec.reduceSLE, BitVec.reduceULT, BitVec.reduceULE, BitVec.reduceSetWidth, Bool.or_false, Bool.bne_false, K₁, E5rSpec.Optimized._Z9incKernelPiS_ii, launch, S, E5rSpec.domain, s0, Cfg.init]
    simp only [addr]
    split <;> (rename_i hcond; ptx_cond_simp hcond)
    all_goals (try simp only [hprod,hsum] at hcond)
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
      have hi : t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat := hx.1
      first
      | (exfalso; omega)
      | (
        have read_frame (M : Mem) (v : Val) :
            rd32 (wr M (elem (A.base "_Z9incKernelPiS_ii_param_0")
              (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) .b4 v)
              (elem (A.base "_Z9incKernelPiS_ii_param_1")
                (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) =
            rd32 M (elem (A.base "_Z9incKernelPiS_ii_param_1")
              (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) :=
          input_read_frame A hp hi hi M v
        simp only [rd, lo32_cast, read_frame, wr_same_twice]
      )
    )
  )

theorem correct : E5rSpec.statement := by
  intro A m sh r p hp
  exact Relational.equivalent_of_paired rfl rfl (paired A hp m r p) (S.disjoint hp) sh
end E5rProof
