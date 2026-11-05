/- e5r-proof ptx=afd811056b3c911bca7ca74947c09739dc7d2066517975393f5ba12440cca5cd spec=d52c056cfe0cd1195a2afe63b3e85bb904d57227fefbdddc8e5ff7fed4fbe66d toolchain=leanprover/lean4:v4.35.0 -/
import E5rSpec
import Ptx.Auto.Tactic
import Ptx.Auto.Packing
set_option maxHeartbeats 2000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
namespace E5rProof
open Ptx Ptx.Auto Ptx.Auto.StencilPair Ptx.Auto.StencilPair.Spec
abbrev S := E5rSpec.domain
abbrev K₀ := E5rSpec.Original.stencil17
abbrev K₁ := E5rSpec.Optimized.stencil17

namespace Wide
 theorem append_lo (x y : BitVec 32) : lo32 (x ++ y) = y := by
  unfold lo32
  rw [BitVec.setWidth_append]
  simp
 theorem append_hi (x y : BitVec 32) : lo32 ((x ++ y) >>> 32) = x := by
  ext i hi
  simp (disch := omega) [lo32,BitVec.getElem_setWidth,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_append]
  rw [BitVec.getElem_append]
  simp [show ¬ 32+i < 32 from by omega]
 theorem read_lo (m : Mem) (a : Addr) (v : Val) : rd32 (wr m a .b8 v) a = lo32 v := by
  have h := congrArg lo32 (rd_wr_same m a .b8 v)
  simpa only [rd,rd64,append_lo] using h
 theorem read_hi (m : Mem) (a : Addr) (v : Val) : rd32 (wr m a .b8 v) (a+4) = lo32 (v >>> 32) := by
  have h := congrArg (fun w : Val => lo32 (w >>> 32)) (rd_wr_same m a .b8 v)
  simpa only [rd,rd64,append_hi] using h
 theorem pack_lo (x y : BitVec 32) : lo32 (ext32 x ||| (ext32 y <<< 32)) = x := by
  ext i hi
  simp (disch := omega) [lo32,ext32,BitVec.getElem_setWidth,BitVec.getLsbD_or,BitVec.getLsbD_shiftLeft,hi]
 theorem pack_hi (x y : BitVec 32) : lo32 ((ext32 x ||| (ext32 y <<< 32)) >>> 32) = y := by
  ext i hi
  simp (disch := omega) [lo32,ext32,BitVec.getElem_setWidth,BitVec.getLsbD_or,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight,hi]
end Wide

namespace Wide
open Ptx.Auto.StencilPair Ptx.Auto.StencilPair.Spec
 theorem align8 (a : Addr) (h : a &&& 7#64 = 0) : a.toNat%8=0 := by
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_and,BitVec.reduceToNat] at h'
  change a.toNat &&& (2^3-1) = 0 at h'
  simpa only [Nat.and_two_pow_sub_one_eq_mod] using h'
 theorem access8 {S : StencilPair.Spec} {A : StencilPair.Args} (hp : S.Pre A) (b : Bool) {i : Nat}
     (hi : i+1 < A.n.toNat) (hal : (elem (A.base S.output) i).toNat%8=0) :
     accessOk (S.launch A b).alloc (elem (A.base S.output) i) .b8 = true := by
  have hi0 : i < A.n.toNat := by omega
  have hh : (Region.mk (A.base S.output) (4*A.n.toNat)).holds (elem (A.base S.output) i) 8 = true := by
    simp only [Region.holds,decide_eq_true_eq,toNat_elem hp.2.1 hi0]
    omega
  simp [accessOk,launch,hal,hh]
 theorem covers8_pair {base : Addr} {N i : Nat} {x : Addr} (hf : Fits base N) (hi : i+1<N)
     (hx : covers (elem base i) 8 x) : covers (elem base i) 4 x ∨ covers (elem base (i+1)) 4 x := by
  have hi0 : i<N := by omega
  have ha : (elem base i).toNat+8 ≤ 2^64 := by rw [toNat_elem hf hi0]; unfold Fits at hf; omega
  rw [covers_iff ha,toNat_elem hf hi0] at hx
  by_cases h : x.toNat < base.toNat+4*i+4
  · exact .inl ((covers_elem hf hi0).2 ⟨hx.1,h⟩)
  · apply Or.inr
    rw [covers_elem hf hi]
    constructor <;> omega
 theorem foot8 {S : StencilPair.Spec} {A : StencilPair.Args} {g : Nat} (hp : S.Pre A) (hi : 2*g+1 < A.n.toNat) :
     InFoot (S.R A) (S.W₁ A g) ⟨.global,elem (A.base S.output) (2*g),.b8,.write⟩ := by
  refine ⟨rfl,nofun,?_⟩
  intro x hx
  apply Or.inl
  rcases covers8_pair hp.2.1 hi hx with h | h
  · exact ⟨0,by decide,by omega,by simpa using h⟩
  · exact ⟨1,by decide,hi,h⟩
 theorem read_hi_elem (m : Mem) (base : Addr) (i : Nat) (v : Val) :
      rd32 (wr m (elem base i) .b8 v) (elem base (i+1)) = lo32 (v >>> 32) := by
  have he := elem_offset_words base i 1
  simp only [Nat.mul_one] at he
  rw [←he]
  exact read_hi m (elem base i) v
end Wide


namespace Wide
 theorem rd_b8 (m : Mem) (a : Addr) : rd m a .b8 = rd64 m a := rfl
 theorem input_lo (m : Mem) (a : Addr) : lo32 (rd64 m a) = rd32 m a := by
  exact append_lo (rd32 m (a+4)) (rd32 m a)
 theorem input_hi (m : Mem) (a : Addr) : lo32 (rd64 m a >>> 32) = rd32 m (a+4) := by
  exact append_hi (rd32 m (a+4)) (rd32 m a)
 theorem input_hi_elem (m : Mem) (base : Addr) (i : Nat) :
     lo32 (rd64 m (elem base i) >>> 32) = rd32 m (elem base (i+1)) := by
  have he := Ptx.Auto.StencilPair.Spec.elem_offset_words base i 1
  simp only [Nat.mul_one] at he
  rw [←he]
  exact input_hi m (elem base i)
 theorem input_access8 {S : StencilPair.Spec} {A : StencilPair.Args} (hp : S.Pre A)
     (b : Bool) {i : Nat} (hi : i+1 < A.n.toNat+16)
     (hal : (elem (A.base S.input) i).toNat%8=0) :
     accessOk (S.launch A b).alloc (elem (A.base S.input) i) .b8 = true := by
  have hi0 : i < A.n.toNat+16 := by omega
  have hh : (Region.mk (A.base S.input) (4*(A.n.toNat+16))).holds (elem (A.base S.input) i) 8 = true := by
    simp only [Region.holds,decide_eq_true_eq,toNat_elem hp.1 hi0]
    omega
  simp [accessOk,StencilPair.Spec.launch,hal,hh]
 theorem input_foot8 {S : StencilPair.Spec} {A : StencilPair.Args} {i : Nat} {W : Addr → Prop}
     (hp : S.Pre A) (hi : i+1 < A.n.toNat+16) :
     InFoot (S.R A) W ⟨.global,elem (A.base S.input) i,.b8,.read⟩ := by
  refine ⟨rfl,nofun,?_⟩
  intro x hx
  apply Or.inr
  refine ⟨rfl,?_⟩
  rcases covers8_pair hp.1 hi hx with h | h
  · exact ⟨i,by omega,h⟩
  · exact ⟨i+1,hi,h⟩
 theorem even_input_align {S : StencilPair.Spec} {A : StencilPair.Args} {g i : Nat}
     (hp : S.Pre A) (h0 : 2*g < A.n.toNat+16) (hi : i < A.n.toNat+16)
     (he : i%2=0) (hm : elem (A.base S.input) (2*g) &&& 7#64 = 0) :
     (elem (A.base S.input) i).toNat%8=0 := by
  have h := align8 _ hm
  rw [toNat_elem hp.1 h0] at h
  rw [toNat_elem hp.1 hi]
  omega
end Wide

-- A continuation-parametric symbolic execution summary of the frozen program.
-- Its store expression is the actual instruction-tree normal form, not an
-- independently stated stencil specification. The direct relation below
-- instantiates the continuation with equality to the edited execution.
theorem original_execute (A : StencilPair.Args) (hp : S.Pre A) (m : Mem) (t : Tid)
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
  unless (lhs.getArg! 2).isConstOf ``Ptx.Size.b4 do throwError "not a word access"
  let addr := lhs.getArg! 1
  unless addr.isAppOfArity ``Ptx.elem 2 do throwError "not an element address"
  let base := addr.getArg! 0
  let .lit (.strVal name) := base.getAppArgs.back! | throwError "not a named stencil pointer"
  let theoremName ← match name with
    | "stencil17_param_0" => pure ``Ptx.Auto.StencilPair.Spec.access_input
    | "stencil17_param_1" => pure ``Ptx.Auto.StencilPair.Spec.access_output
    | _ => throwError "unknown stencil pointer"
  let hp ← Term.elabTerm hp none
  let b ← Term.elabTerm b (some (mkConst ``Bool))
  let pf ← mkAppOptM theoremName #[none,none,some hp,some b,some (addr.getArg! 1)]
  let goals ← withTransparency .default do (← getMainGoal).apply pf
  replaceMainGoal goals

-- Refuse mismatched access widths before definitional unification of accessOk.
elab "wide_only" : tactic => withMainContext do
  let ty ← getMainTarget
  let sz ← if ty.isAppOfArity ``Eq 3 then do
    let lhs := ty.getArg! 1
    unless lhs.isAppOfArity ``Ptx.accessOk 3 do throwError "not accessOk"
    pure (lhs.getArg! 2)
  else if ty.isAppOfArity ``Ptx.InFoot 3 then do
    let acc := ty.getArg! 2
    unless acc.isAppOfArity ``Ptx.Acc.mk 4 do throwError "not an access"
    pure (acc.getArg! 2)
  else throwError "not an access obligation"
  unless sz.isConstOf ``Ptx.Size.b8 do throwError "not an eight-byte access"

elab "wide_access_step" "[" hp:term "," g:term "," inEq:term "," outEq:term "]" : tactic => withMainContext do
  let ty ← getMainTarget
  unless ty.isAppOfArity ``Eq 3 do return
  let lhs := ty.getArg! 1
  unless lhs.isAppOfArity ``Ptx.accessOk 3 do return
  unless (lhs.getArg! 2).isConstOf ``Ptx.Size.b8 do return
  let addr := lhs.getArg! 1
  unless addr.isAppOfArity ``Ptx.elem 2 do throwError "not a normalized element address"
  let base := addr.getArg! 0
  let .lit (.strVal name) := base.getAppArgs.back! | throwError "not a named pointer"
  if name == "stencil17_param_0" then
    let ix ← Lean.PrettyPrinter.delab (addr.getArg! 1)
    evalTactic (← `(tactic| (
      apply Wide.input_access8 $hp:term true (i := $ix:term)
      · omega
      · apply Wide.even_input_align $hp:term (g := $g:term)
        · omega
        · omega
        · omega
        · dsimp only [S,E5rSpec.domain]
          rw [← $inEq:term]
          assumption)))
  else if name == "stencil17_param_1" then
    evalTactic (← `(tactic| (
      apply Wide.access8 $hp:term true (i := 2*$g:term)
      · omega
      · apply Wide.align8
        dsimp only [S,E5rSpec.domain]
        rw [← $outEq:term]
        assumption)))
  else throwError "unknown wide pointer"

-- Instantiate the frozen program's execution continuation directly with
-- equality to the edited memory. This is a direct relation, not a common spec.
theorem reference_continuation (A : StencilPair.Args) (hp : S.Pre A) (m : Mem)
    (r : Tid → String → Val) (p : Tid → String → Bool) (g : Nat) (M₁ : Mem)
    (eq : ∀ j < 2, 2*g+j < A.n.toNat →
      rd32 (wr m (elem (A.base S.output) (2*g+j)) .b4 (ext32 ((rd32 m (elem (A.base S.input) (2*g+j+16))) + ((rd32 m (elem (A.base S.input) (2*g+j+15))) + ((rd32 m (elem (A.base S.input) (2*g+j+14))) + ((rd32 m (elem (A.base S.input) (2*g+j+13))) + ((rd32 m (elem (A.base S.input) (2*g+j+12))) + ((rd32 m (elem (A.base S.input) (2*g+j+11))) + ((rd32 m (elem (A.base S.input) (2*g+j+10))) + ((rd32 m (elem (A.base S.input) (2*g+j+9))) + ((rd32 m (elem (A.base S.input) (2*g+j+8))) + ((rd32 m (elem (A.base S.input) (2*g+j+7))) + ((rd32 m (elem (A.base S.input) (2*g+j+6))) + ((rd32 m (elem (A.base S.input) (2*g+j+5))) + ((rd32 m (elem (A.base S.input) (2*g+j+4))) + ((rd32 m (elem (A.base S.input) (2*g+j+3))) + ((rd32 m (elem (A.base S.input) (2*g+j+2))) + ((rd32 m (elem (A.base S.input) (2*g+j+1))) + (rd32 m (elem (A.base S.input) (2*g+j+0)))))))))))))))))))))
        (elem (A.base S.output) (2*g+j)) = rd32 M₁ (elem (A.base S.output) (2*g+j))) :
    ∀ j < 2, let i := 2*g+j; i < A.n.toNat →
      let u := owner A.B i
      Safe K₀ (S.launch A false).alloc ((S.launch A false).ctx u) (S.R A) (S.W₀ A i)
        (fun s M₀ => action K₀ ((S.launch A false).ctx u) s = .done ∧
          rd32 M₀ (elem (A.base S.output) i) = rd32 M₁ (elem (A.base S.output) i))
        (s0 r p m u) m := by
  intro j hj
  dsimp only
  intro hi
  have hn := hp.2.2.2.2.2.1
  obtain ⟨ht,hgid⟩ := (S.oneD₀ A).owner_mem (i := 2*g+j) (by omega)
  have run := original_execute A hp m (owner A.B (2*g+j)) ht (r (owner A.B (2*g+j))) (p (owner A.B (2*g+j)))
    (fun M₀ => rd32 M₀ (elem (A.base S.output) (2*g+j)) = rd32 M₁ (elem (A.base S.output) (2*g+j)))
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
  have hn3 : (A.n.toNat+1)%4294967296 = A.n.toNat+1 := Nat.mod_eq_of_lt (by omega)
  let g := t.ctaid.x.toNat * A.B₁.toNat + t.tid.x.toNat
  let Q : Mem → Prop := fun M₁ => ∀ j < 2, let i := 2*g+j; i < A.n.toNat →
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
    (show lo32 (1#64) = (1#32) from rfl), (show min 1 32 = 1 from rfl),
    BitVec.reduceToNat,Nat.reducePow,Nat.reduceMod,gid] at *)
  all_goals (first
    | (have hinactive : (A.n.toNat+1)/2 ≤ g := by dsimp only [g]; omega
       change Q m; unfold Q; intro j hj; dsimp only; intro hi; exfalso; dsimp only [g] at hi; omega)
    | skip)
  all_goals (
    have hactive : g < (A.n.toNat+1)/2 := by dsimp only [g]; omega
    let ix : BitVec 32 := (t.ctaid.x*A.B₁+t.tid.x) <<< min (lo32 (1#64)).toNat 32
    have hidx : (t.ctaid.x*A.B₁+t.tid.x).toNat = g := hd.gid_bv ht hm₁
    have hix : ix.toNat = 2*g := by
      dsimp only [ix]
      simp only [lo32,BitVec.reduceOfInt,BitVec.reduceSetWidth,BitVec.reduceToNat,
        (show min 1 32 = 1 from rfl),BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.reducePow,hidx]
      omega
    have hIn : A.base "stencil17_param_0" + ext32 ix * ext32 (lo32 (4#64)) =
        elem (A.base "stencil17_param_0") (2*g) := by ptx_addr_eq
    have hOut : A.base "stencil17_param_1" + ext32 ix * ext32 (lo32 (4#64)) =
        elem (A.base "stencil17_param_1") (2*g) := by ptx_addr_eq
    dsimp only [ix] at hIn hOut
    simp only [(show min (lo32 (1#64)).toNat 32 = 1 from rfl)] at hIn hOut
    simp (disch := decide) only [hIn,hOut,BitVec.reduceOfInt,elem_offset_val,BitVec.reduceToNat,
      Nat.reduceMod,Nat.reduceDiv,Nat.add_zero,BitVec.add_zero]
  )
  all_goals (try and_intros)
  all_goals (wide_access_step [hp,g,hIn,hOut])

  all_goals (first
    | (exact True.intro)
    | (wide_only; apply Wide.input_foot8 hp; omega)
    | (wide_only; apply Wide.foot8 hp; omega)
    | (stencil_access [hp, true] <;> omega)
    | (apply load_foot (S := S); omega)
    | (apply store_foot₁ (S := S) (j := 0) (by decide); omega)
    | (apply store_foot₁ (S := S) (j := 1) (by decide); omega)
    | skip)
  all_goals (
    change Q _
    unfold Q
    apply reference_continuation A hp m r p g
    intro j hj hi
    have cases : j=0 ∨ j=1 := by omega
    rcases cases with h | h
    all_goals subst j
    all_goals (try (exfalso; dsimp only [g] at hi; omega))
    all_goals (simp only [S,E5rSpec.domain])
    all_goals (try simp (disch := omega) [rd32_wr_same,lo32_ext32,lo32_rd_b4,
      frame,writes,Nat.add_assoc,Wide.rd_b8,Wide.input_lo,Wide.input_hi_elem,Wide.read_lo,Wide.read_hi_elem,Wide.pack_lo,Wide.pack_hi,
      (show min (lo32 (32#64)).toNat 64 = 32 from rfl)])
    all_goals (set_option maxHeartbeats 100000 in grind only)

  )


theorem correct : E5rSpec.statement :=
  equivalent_of_threads rfl rfl safe_original relation
end E5rProof
