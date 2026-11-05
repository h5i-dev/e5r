/- e5r-proof ptx=a79f34aabc16683894018aa13556720f045e7dcc09e1bff21f4dc05990c0fbc5 spec=42d491e0425cda6ede5c3bfa8aec028025ed82011355322b046f8fe2741cb62d toolchain=leanprover/lean4:v4.35.0 -/
import E5rSpec
import Ptx.Auto.Tactic
import Ptx.Auto.Packing
set_option maxHeartbeats 2000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
namespace E5rProof
open Ptx Ptx.Auto Ptx.Auto.Stencil Ptx.Auto.Stencil.Spec
abbrev S := E5rSpec.domain
abbrev K₀ := E5rSpec.Original.stencil17
abbrev K₁ := E5rSpec.Optimized.stencil17

-- A continuation-parametric symbolic execution summary of the frozen program.
-- Its store expression is the actual instruction-tree normal form, not an
-- independently stated stencil specification. The direct relation below
-- instantiates the continuation with equality to the edited execution.
theorem original_execute (A : Stencil.Args) (hp : S.Pre A) (m : Mem) (t : Tid)
    (ht : t ∈ (S.launch A false).threads) (r : String → Val) (p : String → Bool)
    (Q : Mem → Prop)
    (hQ₀ : gid A.B t < A.n.toNat → Q (wr m (elem (A.base S.output) (gid A.B t))
      .b4 (ext32 ((rd32 m (elem (A.base S.input) (gid A.B t+16))) + ((rd32 m (elem (A.base S.input) (gid A.B t+15))) + ((rd32 m (elem (A.base S.input) (gid A.B t+14))) + ((rd32 m (elem (A.base S.input) (gid A.B t+13))) + ((rd32 m (elem (A.base S.input) (gid A.B t+12))) + ((rd32 m (elem (A.base S.input) (gid A.B t+11))) + ((rd32 m (elem (A.base S.input) (gid A.B t+10))) + ((rd32 m (elem (A.base S.input) (gid A.B t+9))) + ((rd32 m (elem (A.base S.input) (gid A.B t+8))) + ((rd32 m (elem (A.base S.input) (gid A.B t+7))) + ((rd32 m (elem (A.base S.input) (gid A.B t+6))) + ((rd32 m (elem (A.base S.input) (gid A.B t+5))) + ((rd32 m (elem (A.base S.input) (gid A.B t+4))) + ((rd32 m (elem (A.base S.input) (gid A.B t+3))) + ((rd32 m (elem (A.base S.input) (gid A.B t+2))) + ((rd32 m (elem (A.base S.input) (gid A.B t+1))) + (rd32 m (elem (A.base S.input) (gid A.B t+0))))))))))))))))))))))
    (hQ₁ : A.n.toNat ≤ gid A.B t → Q m) :
    Safe K₀ (S.launch A false).alloc ((S.launch A false).ctx t)
      (S.R A) (S.W₀ A (gid A.B t))
      (fun s M => action K₀ ((S.launch A false).ctx t) s = .done ∧ Q M) ⟨0,r,p⟩ m := by
  have hd := S.oneD₀ A
  obtain ⟨hc,htt,hy,hz,hty,htz⟩ := hd.thread ht
  have hg := hd.gid_lt ht
  obtain ⟨fi,fo,ai,ao,sep,hn₀,hm₀,hn₁,hm₁⟩ := hp
  have hp : S.Pre A := ⟨fi,fo,ai,ao,sep,hn₀,hm₀,hn₁,hm₁⟩
  have hn : A.n.toNat ≤ 2^31 := by omega
  have hBc : A.B.toNat * t.ctaid.x.toNat = t.ctaid.x.toNat * A.B.toNat := Nat.mul_comm _ _
  have hg32 := hd.gid_bv ht hm₀
  have hprod : t.ctaid.x.toNat * A.B.toNat % 4294967296 = t.ctaid.x.toNat * A.B.toNat :=
    Nat.mod_eq_of_lt (by unfold gid at hg; omega)
  have hsum : (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) % 4294967296 = t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat :=
    Nat.mod_eq_of_lt (by unfold gid at hg; omega)
  unfold gid at *
  refine (wp_sound (f := 150) (cut := fun _ => false) ?_).weaken
    fun s m h => ⟨h.2.resolve_left (by simp),h.1⟩
  simp only [ptx_eval,K₀,E5rSpec.Original.stencil17,launch,S,E5rSpec.domain]
  ptx_addrs [A.base "stencil17_param_0", A.base "stencil17_param_1"] [(t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+0, (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+1, (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+2, (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+3, (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+4, (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+5, (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+6, (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+7, (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+8, (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+9, (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+10, (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+11, (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+12, (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+13, (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+14, (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+15, (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+16]
  ptx_branches
  all_goals (try simp only [hprod,hsum] at *)
  all_goals (try and_intros)
  all_goals (try simp only [lo32_rd_b4])
  all_goals (first
    | (exact True.intro)
    | (simpa only [launch,S,E5rSpec.domain] using (access_input hp false (by omega)))
    | (simpa only [launch,S,E5rSpec.domain] using (access_output hp false (by omega)))
    | (exact load_foot (S := S) (by omega))
    | (exact store_foot₀ (S := S) (by omega))
    | (apply hQ₀; omega)
    | (apply hQ₁; omega)
    | skip)
  all_goals trace_state

theorem safe_original : S.SafeOriginal K₀ := by
  intro A hp m t ht r p
  exact original_execute A hp m t ht r p (fun _ => True) (fun _ => True.intro) (fun _ => True.intro)



-- Select the access lemma from the concrete address before unification;
-- avoid asking elaboration to guess an index relative to the wrong array.
open Lean Meta Elab Tactic
elab "stencil_access" "[" hp:term "," b:term "]" : tactic => withMainContext do
  let ty ← getMainTarget
  unless ty.isAppOfArity ``Eq 3 do throwError "not an access equality"
  let lhs := ty.getArg! 1
  unless lhs.isAppOfArity ``Ptx.accessOk 3 do throwError "not accessOk"
  let addr := lhs.getArg! 1
  unless addr.isAppOfArity ``Ptx.elem 2 do throwError "not an element address"
  let base := addr.getArg! 0
  let .lit (.strVal name) := base.getAppArgs.back! | throwError "not a named stencil pointer"
  let theoremName ← match name with
    | "stencil17_param_0" => pure ``Ptx.Auto.Stencil.Spec.access_input
    | "stencil17_param_1" => pure ``Ptx.Auto.Stencil.Spec.access_output
    | _ => throwError "unknown stencil pointer"
  let hp ← Term.elabTerm hp none
  let b ← Term.elabTerm b (some (mkConst ``Bool))
  let pf ← mkAppOptM theoremName #[none,none,some hp,some b,some (addr.getArg! 1)]
  let goals ← withTransparency .default do (← getMainGoal).apply pf
  replaceMainGoal goals

-- Instantiate the frozen program's execution continuation directly with
-- equality to the edited memory. This is a direct relation, not a common spec.
theorem reference_continuation (A : Stencil.Args) (hp : S.Pre A) (m : Mem)
    (r : Tid → String → Val) (p : Tid → String → Bool) (g : Nat) (M₁ : Mem)
    (eq : ∀ j < 4, 4*g+j < A.n.toNat →
      rd32 (wr m (elem (A.base S.output) (4*g+j)) .b4 (ext32 ((rd32 m (elem (A.base S.input) (4*g+j+16))) + ((rd32 m (elem (A.base S.input) (4*g+j+15))) + ((rd32 m (elem (A.base S.input) (4*g+j+14))) + ((rd32 m (elem (A.base S.input) (4*g+j+13))) + ((rd32 m (elem (A.base S.input) (4*g+j+12))) + ((rd32 m (elem (A.base S.input) (4*g+j+11))) + ((rd32 m (elem (A.base S.input) (4*g+j+10))) + ((rd32 m (elem (A.base S.input) (4*g+j+9))) + ((rd32 m (elem (A.base S.input) (4*g+j+8))) + ((rd32 m (elem (A.base S.input) (4*g+j+7))) + ((rd32 m (elem (A.base S.input) (4*g+j+6))) + ((rd32 m (elem (A.base S.input) (4*g+j+5))) + ((rd32 m (elem (A.base S.input) (4*g+j+4))) + ((rd32 m (elem (A.base S.input) (4*g+j+3))) + ((rd32 m (elem (A.base S.input) (4*g+j+2))) + ((rd32 m (elem (A.base S.input) (4*g+j+1))) + (rd32 m (elem (A.base S.input) (4*g+j+0)))))))))))))))))))))
        (elem (A.base S.output) (4*g+j)) = rd32 M₁ (elem (A.base S.output) (4*g+j))) :
    ∀ j < 4, let i := 4*g+j; i < A.n.toNat →
      let u := owner A.B i
      Safe K₀ (S.launch A false).alloc ((S.launch A false).ctx u) (S.R A) (S.W₀ A i)
        (fun s M₀ => action K₀ ((S.launch A false).ctx u) s = .done ∧
          rd32 M₀ (elem (A.base S.output) i) = rd32 M₁ (elem (A.base S.output) i))
        (s0 r p m u) m := by
  intro j hj
  dsimp only
  intro hi
  have hn := hp.2.2.2.2.2.1
  obtain ⟨ht,hgid⟩ := (S.oneD₀ A).owner_mem (i := 4*g+j) (by omega)
  have run := original_execute A hp m (owner A.B (4*g+j)) ht (r (owner A.B (4*g+j))) (p (owner A.B (4*g+j)))
    (fun M₀ => rd32 M₀ (elem (A.base S.output) (4*g+j)) = rd32 M₁ (elem (A.base S.output) (4*g+j)))
    (by intro _; simpa only [hgid] using eq j hj hi)
    (by intro h; exfalso; omega)
  simpa only [hgid,s0,Cfg.init] using run

theorem relation : S.ThreadRelation K₀ K₁ := by
  intro A hp m r p t ht
  have hd := S.oneD₁ A
  obtain ⟨hc,htt,hy,hz,hty,htz⟩ := hd.thread ht
  have hg := hd.gid_lt ht
  obtain ⟨fi,fo,ai,ao,sep,hn₀,hm₀,hn₁,hm₁⟩ := hp
  have hp : S.Pre A := ⟨fi,fo,ai,ao,sep,hn₀,hm₀,hn₁,hm₁⟩
  have hn : A.n.toNat ≤ 2^31 := by omega
  have hBc : A.B₁.toNat * t.ctaid.x.toNat = t.ctaid.x.toNat * A.B₁.toNat := Nat.mul_comm _ _
  have hg32 := hd.gid_bv ht hm₁
  have hprod : t.ctaid.x.toNat * A.B₁.toNat % 4294967296 = t.ctaid.x.toNat * A.B₁.toNat :=
    Nat.mod_eq_of_lt (by unfold gid at hg; omega)
  have hsum : (t.ctaid.x.toNat * A.B₁.toNat + t.tid.x.toNat) % 4294967296 = t.ctaid.x.toNat * A.B₁.toNat + t.tid.x.toNat :=
    Nat.mod_eq_of_lt (by unfold gid at hg; omega)
  have hn3 : (A.n.toNat+3)%4294967296 = A.n.toNat+3 := Nat.mod_eq_of_lt (by omega)
  let g := t.ctaid.x.toNat * A.B₁.toNat + t.tid.x.toNat
  let Q : Mem → Prop := fun M₁ => ∀ j < 4, let i := 4*g+j; i < A.n.toNat →
    let u := owner A.B i
    Safe K₀ (S.launch A false).alloc ((S.launch A false).ctx u) (S.R A) (S.W₀ A i)
      (fun s M₀ => action K₀ ((S.launch A false).ctx u) s = .done ∧
        rd32 M₀ (elem (A.base S.output) i) = rd32 M₁ (elem (A.base S.output) i))
      (s0 r p m u) m
  have frame (i j : Nat) (hi : i < A.n.toNat+16) (hj : j < A.n.toNat) (M : Mem) (v : Val) :
      rd32 (wr M (elem (A.base "stencil17_param_1") j) .b4 v)
        (elem (A.base "stencil17_param_0") i) = rd32 M (elem (A.base "stencil17_param_0") i) :=
    input_read_frame hp hi hj M v
  have writes (i j : Nat) (hi : i < A.n.toNat) (hj : j < A.n.toNat) (M : Mem) (v : Val) :
      rd32 (wr M (elem (A.base "stencil17_param_1") i) .b4 v)
        (elem (A.base "stencil17_param_1") j) = if i=j then lo32 v else rd32 M (elem (A.base "stencil17_param_1") j) :=
    Packing.Spec.rd32_wr_indices fo hi hj M v
  change Safe K₁ _ _ _ _ (fun s M => action K₁ ((S.launch A true).ctx t) s = .done ∧ Q M) _ _
  refine (wp_sound (f := 110) (cut := fun _ => false) ?_).weaken
    fun s m h => ⟨h.2.resolve_left (by simp),h.1⟩
  simp only [ptx_eval,K₁,E5rSpec.Optimized.stencil17,launch,S,E5rSpec.domain,s0,Cfg.init]
  ptx_branches
  all_goals (try simp only [hprod,hsum,hn3,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,
    BitVec.toNat_add,BitVec.toNat_mul,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,BitVec.reduceOfInt,lo32_ext32,
    (show lo32 (3#64) = (3#32) from rfl), (show min 2 32 = 2 from rfl),
    BitVec.reduceToNat,Nat.reducePow,Nat.reduceMod,gid] at *)
  all_goals (first
    | (change Q m; unfold Q; intro j hj; dsimp only; intro hi; exfalso; dsimp only [g] at hi; omega)
    | skip)
  all_goals (
    have hactive : g < (A.n.toNat+3)/4 := by dsimp only [g]; omega
    let ix : BitVec 32 := (t.ctaid.x*A.B₁+t.tid.x) <<< min (lo32 (2#64)).toNat 32
    have hidx : (t.ctaid.x*A.B₁+t.tid.x).toNat = g := hd.gid_bv ht hm₁
    have hix : ix.toNat = 4*g := by
      dsimp only [ix]
      simp only [lo32,BitVec.reduceOfInt,BitVec.reduceSetWidth,BitVec.reduceToNat,
        (show min 2 32 = 2 from rfl),BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.reducePow,hidx]
      omega
    have hIn : A.base "stencil17_param_0" + ext32 ix * ext32 (lo32 (4#64)) =
        elem (A.base "stencil17_param_0") (4*g) := by ptx_addr_eq
    have hOut : A.base "stencil17_param_1" + ext32 ix * ext32 (lo32 (4#64)) =
        elem (A.base "stencil17_param_1") (4*g) := by ptx_addr_eq
    dsimp only [ix] at hIn hOut
    simp (disch := decide) only [hIn,hOut,BitVec.reduceOfInt,elem_offset_val,BitVec.reduceToNat,
      Nat.reduceMod,Nat.reduceDiv,Nat.add_zero,BitVec.add_zero]
  )
  all_goals (try and_intros)
  all_goals (first
    | (exact True.intro)
    | (stencil_access [hp, true] <;> omega)
    | (apply load_foot (S := S); omega)
    | (apply store_foot₁ (S := S) (j := 0) (by decide); omega)
    | (apply store_foot₁ (S := S) (j := 1) (by decide); omega)
    | (apply store_foot₁ (S := S) (j := 2) (by decide); omega)
    | (apply store_foot₁ (S := S) (j := 3) (by decide); omega)
    | skip)
  all_goals (
    change Q _
    unfold Q
    apply reference_continuation A hp m r p g
    intro j hj hi
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases with h | h | h | h
    all_goals subst j
    all_goals (try (exfalso; dsimp only [g] at hi; omega))
    all_goals (simp only [S,E5rSpec.domain])
    all_goals (try simp (disch := omega) [rd32_wr_same,lo32_ext32,lo32_rd_b4,
      frame,writes,Nat.add_assoc])
    all_goals (grind only)

  )


theorem correct : E5rSpec.statement :=
  equivalent_of_threads rfl rfl safe_original relation
end E5rProof
