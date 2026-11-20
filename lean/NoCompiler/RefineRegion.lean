import NoCompiler.RefineCongr

/-
Regions: the unit of a changed interval (docs/isa/refine.md, items 3 and 4).

A region pairs an interval of B's code with an interval of A's: each has
one entry and one exit (a subtree of the block/loop tree, or a straight-line
run inside one), and the region says which registers are live at the entry
and at the exit. Inside, the two may differ arbitrarily: different
instructions, different numbers of them, different loop shapes.

`Region.Ok` is what has to be proved about one: a local refinement. From
any two states at the two entries that agree on `liveIn` (and on memory,
trace and exit status), where A's run through its interval is safe and
terminates, B's run through its interval is safe and terminates, and every
way B leaves it is matched by a way A leaves it: both at their exits,
agreeing on `liveOut`, with A's ra as it was; or both exited the process
with the same status and events. Every access inside is under the same
permission `P`, for every `P`: what B touches, A touches.

How a region is proved is open: by stepping both sides symbolically
(straight-line), by a relational loop invariant (same-shaped loops), by a
k:1 correspondence (an unrolled loop), or by local summaries. Facts about
the entry state that hold of A's runs but are not in `liveIn` (for example,
that two pointers do not alias) are not available; a region that needs one
is stated with it as an extra entry condition `pre`, which becomes a
reported precondition of the refinement.

The certificate of `NoCompiler/RefineLockstep.lean` pairs single, identical
instructions; a region pair stands for a whole changed interval in it, with
its `Region.Ok` proof as a hypothesis of the soundness theorem (next step).
-/
namespace NoCompiler

/-- A changed interval: B's code `domB` entered at `pb` and left at `pbExit`,
    A's code `domA` entered at `pa` and left at `paExit`. -/
structure RRegion where
  pb : Word
  pa : Word
  pbExit : Word
  paExit : Word
  domB : Dom
  domA : Dom
  liveIn : List Reg
  liveOut : List Reg
  deriving DecidableEq, Repr

/-- The range `x` lies inside one of `D`'s ranges (decidable). -/
def Dom.rangeIn (x : Word × Nat) (D : Dom) : Bool :=
  D.any fun y => decide ((x.1 - y.1).toNat + x.2 ≤ y.2)

theorem Dom.sub_of_rangeIn {E D : Dom} (h : E.all (fun x => Dom.rangeIn x D) = true) : E.sub D := by
  intro p hp
  unfold Dom.mem at hp ⊢
  obtain ⟨x, hx, hpx⟩ := List.any_eq_true.1 hp
  obtain ⟨y, hy, hxy⟩ := List.any_eq_true.1 (List.all_eq_true.1 h x hx)
  simp only [decide_eq_true_eq] at hpx hxy
  refine List.any_eq_true.2 ⟨y, hy, ?_⟩
  have hc : Region.covers ⟨y.1, y.2⟩ p 1 :=
    Region.covers_of_within (r := ⟨x.1, x.2⟩) (show (p - x.1).toNat + 1 ≤ x.2 by omega) hxy
  unfold Region.covers at hc
  simp only at hc
  simp only [decide_eq_true_eq]; omega

namespace RRegion

/-- How the two runs leave a region, seen from A's state `sa` at its entry. -/
def Exit (r : RRegion) (sa ta tb : State) : Prop :=
  (ta.exit = none ∧ ta.pc = r.paExit ∧ tb.pc = r.pbExit ∧ ta.reg 1 = sa.reg 1 ∧ Agree r.liveOut ta tb) ∨
  (ta.exit ≠ none ∧ Agree [] ta tb)

/-- What a region's proof establishes, under an entry condition `pre` on A's
    state (`fun _ => True` when the region needs none). -/
def Ok (cA cB : Code) (r : RRegion) (pre : State → Prop := fun _ => True) : Prop :=
  ∀ (P : Perm) (sa sb : State), sa.exit = none → sa.pc = r.pa → sb.pc = r.pb →
    Agree r.liveIn sa sb → pre sa →
    Exec cA P r.domA (fun _ => True) sa →
    Exec cB P r.domB (fun tb => ∃ ta, Run cA P r.domA sa ta ∧ Final r.domA ta ∧ r.Exit sa ta tb) sb

/-- The region checks a certificate needs of its shape, decided by the
    kernel: the entries lie in the intervals, the exits do not, and the
    intervals lie inside the functions' code. -/
def shapeOk (DA DB : Dom) (r : RRegion) : Bool :=
  decide (r.domB.mem r.pb) && decide (r.domA.mem r.pa) &&
  !decide (r.domB.mem r.pbExit) && !decide (r.domA.mem r.paExit) &&
  r.domB.all (fun x => Dom.rangeIn x DB) && r.domA.all (fun x => Dom.rangeIn x DA)

/-! ## A region of one instruction -/

/-- A one-instruction region whose two instructions (neither a syscall) have
    the same effect on agreeing states: the base case of a changed interval
    (a peephole). `hsem` is the equivalence, `hperm` that what B's
    instruction touches A's does too. -/
theorem Ok.of_instr {cA cB : Code} {r : RRegion} {iA iB : Instr}
    (hdA : r.domA = [(r.pa, 4)]) (hdB : r.domB = [(r.pb, 4)])
    (hxA : r.paExit = r.pa + 4) (hxB : r.pbExit = r.pb + 4)
    (hiA : cA.instr r.pa = some iA) (hiB : cB.instr r.pb = some iB)
    (hcA : iA ≠ .ecall) (hcB : iB ≠ .ecall)
    (hperm : ∀ P sa sb, Agree r.liveIn sa sb → InstrOk P iA sa → InstrOk P iB sb)
    (hsem : ∀ sa sb, sa.exit = none → Agree r.liveIn sa sb → ∀ sa', exec iA sa = some sa' →
      ∃ sb', exec iB sb = some sb' ∧ sa'.exit = none ∧ sa'.reg 1 = sa.reg 1 ∧
        sa'.pc = sa.pc + 4 ∧ sb'.pc = sb.pc + 4 ∧ Agree r.liveOut sa' sb') :
    r.Ok cA cB := by
  intro P sa sb hx hpa hpb hag _ hA
  have one : ∀ x : Word, Dom.mem [(x, 4)] x := fun x => by
    unfold Dom.mem; simp only [List.any_cons, List.any_nil, Bool.or_false]
    rw [show x - x = 0 from by bv_omega]; simp
  have next : ∀ x : Word, ¬ Dom.mem [(x, 4)] (x + 4) := fun x => by
    unfold Dom.mem; simp only [List.any_cons, List.any_nil, Bool.or_false]
    rw [show x + 4 - x = 4 from by bv_omega]; simp
  have memA : r.domA.mem sa.pc := by rw [hdA, hpa]; exact one _
  have memB : r.domB.mem sb.pc := by rw [hdB, hpb]; exact one _
  have outA : ∀ p, p = sa.pc + 4 → ¬ r.domA.mem p := by
    intro p hp; rw [hdA, hp, hpa]; exact next _
  have outB : ∀ p, p = sb.pc + 4 → ¬ r.domB.mem p := by
    intro p hp; rw [hdB, hp, hpb]; exact next _
  -- A's step, from A's safety
  obtain ⟨sa', hsa⟩ : ∃ sa', Step cA P sa sa' := by
    cases hA with
    | done hq => rcases hq.1 with h | h
                 · exact absurd memA h
                 · exact absurd hx h
    | step _ hex _ => exact hex
  cases hsa with
  | sys _ hi _ _ => rw [hpa, hiA] at hi; cases hi; exact absurd rfl hcA
  | exec _ hi hok hexa =>
    rw [hpa, hiA] at hi; cases hi
    obtain ⟨sb', hexb, hxa', hra', hpa', hpb', hag'⟩ := hsem sa sb hx hag sa' hexa
    have hxb : sb.exit = none := hag.exit ▸ hx
    have hiB' : cB.instr sb.pc = some iB := hpb ▸ hiB
    have hstB : Step cB P sb sb' := .exec hxb hiB' (hperm P sa sb hag hok) hexb
    refine .step memB ⟨sb', hstB⟩ (fun t ht => ?_)
    have ht' : t = sb' := by
      cases ht with
      | exec _ hi' _ he' => rw [hiB'] at hi'; cases hi'; rw [hexb] at he'; cases he'; rfl
      | sys _ hi' _ _ => rw [hiB'] at hi'; cases hi'; exact absurd rfl hcB
    subst ht'
    refine .done ⟨.inl (outB _ hpb'), sa', .step memA (.exec hx (hpa ▸ hiA) hok hexa) (.refl _),
      .inl (outA _ hpa'), .inl ⟨hxa', by rw [hpa', hpa, hxA], by rw [hpb', hpb, hxB], hra', hag'⟩⟩

end RRegion
end NoCompiler
