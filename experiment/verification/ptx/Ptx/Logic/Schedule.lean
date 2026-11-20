/-
Refutations with barriers: replaying one schedule of the whole launch.

A schedule is a list of choices, each running one thread for some steps or
releasing one CTA's barrier. `Cfg.exec` runs it and fails (`none`) as soon
as a choice is not a `Step` of the model; `exec_reach` turns a successful
run into `Reach`. The checks on the configurations it reaches (`faultsB`,
`doneB`, `raceB`) are Boolean so a refutation is one `decide` over a closed
term, evaluated by the Lean kernel; each comes with the lemma that turns
`true` into the property the class theorem denies.
-/
import Ptx.Logic.Refute

namespace Ptx

/-- Run thread `t` for `n` steps, or release CTA `b`'s barrier. -/
inductive Choice where
  | run (t : Tid) (n : Nat)
  | rel (b : Dim3)

def TRes.isWait : TRes → Bool
  | .wait => true
  | _ => false

def TRes.isHalted : TRes → Bool
  | .halted => true
  | _ => false

def TRes.isFault : TRes → Bool
  | .fault => true
  | _ => false

theorem TRes.isWait_eq {r : TRes} (h : r.isWait = true) : r = .wait := by
  cases r <;> simp_all [TRes.isWait]

theorem TRes.isHalted_eq {r : TRes} (h : r.isHalted = true) : r = .halted := by
  cases r <;> simp_all [TRes.isHalted]

theorem TRes.isFault_eq {r : TRes} (h : r.isFault = true) : r = .fault := by
  cases r <;> simp_all [TRes.isFault]

section
variable (K : Kernel) (L : Launch)

/-- One step of thread `t`, if it can make one. -/
def Cfg.stepT (c : Cfg) (t : Tid) : Option Cfg :=
  match c.res K L t with
  | .ok s h => some (c.write t s h)
  | _ => none

/-- `n` steps of thread `t`. -/
def Cfg.runT : Cfg → Tid → Nat → Option Cfg
  | c, _, 0 => some c
  | c, t, n + 1 =>
    match c.stepT K L t with
    | some c' => Cfg.runT c' t n
    | none => none

/-- `BarReady`, decided. -/
def barReadyB (c : Cfg) (b : Dim3) : Bool :=
  match L.threads.filter (fun t => t.ctaid = b) with
  | [] => false
  | t₀ :: rest => (t₀ :: rest).all fun t => (c.res K L t).isWait && (c.ts t).pc == (c.ts t₀).pc

/-- Run a schedule. -/
def Cfg.exec : Cfg → List Choice → Option Cfg
  | c, [] => some c
  | c, .run t n :: cs =>
    if t ∈ L.threads then
      match Cfg.runT K L c t n with
      | some c' => Cfg.exec c' cs
      | none => none
    else none
  | c, .rel b :: cs => if barReadyB K L c b then Cfg.exec (c.release b) cs else none

/-- Some thread faults, or a barrier has diverged. -/
def faultsB (c : Cfg) : Bool :=
  L.threads.any (fun t => (c.res K L t).isFault) ||
    L.threads.any fun t => L.threads.any fun u =>
      t.ctaid == u.ctaid && (c.res K L t).isWait &&
        ((c.res K L u).isHalted || ((c.res K L u).isWait && (c.ts u).pc != (c.ts t).pc))

/-- Every thread has finished. -/
def doneB (c : Cfg) : Bool := L.threads.all fun t => (c.res K L t).isHalted

/-- Access `x` of `t` in `c₁` and access `y` of `u` in `c₂` share byte `b`,
conflict, are not atomics on one location, and are not separated by a
barrier of one CTA. -/
def raceB (c₁ c₂ : Cfg) (t u : Tid) (b : Addr) : Bool :=
  decide (t ∈ L.threads) && decide (u ∈ L.threads) && decide (t ≠ u) &&
    match c₁.pending K L t, c₂.pending K L u with
    | some x, some y =>
      decide (x.sp = y.sp) && (decide (x.sp ≠ .shared) || decide (t.ctaid = u.ctaid)) &&
        (decide (x.kind ≠ .read) || decide (y.kind ≠ .read)) &&
        decide (covers x.a x.sz.bytes b) && decide (covers y.a y.sz.bytes b) &&
        !(decide (x.kind = .atomic ∧ y.kind = .atomic ∧ x.a = y.a ∧ x.sz = y.sz)) &&
        !(decide (t.ctaid = u.ctaid ∧ c₁.ph t.ctaid ≠ c₂.ph u.ctaid))
    | _, _ => false

end

section
variable {K : Kernel} {L : Launch}

theorem runT_reach {t : Tid} (ht : t ∈ L.threads) :
    ∀ n {c c' : Cfg}, Cfg.runT K L c t n = some c' → Reach K L c c' := by
  intro n
  induction n with
  | zero => intro c c' h; simp only [Cfg.runT, Option.some.injEq] at h; subst h; exact .refl _
  | succ n ih =>
    intro c c' h
    simp only [Cfg.runT] at h
    split at h
    · next c₁ h₁ =>
      have hs : Step K L c c₁ := by
        unfold Cfg.stepT at h₁
        split at h₁
        · next s' h' hr =>
          simp only [Option.some.injEq] at h₁
          exact .inl ⟨t, ht, s', h', hr, h₁.symm⟩
        all_goals exact absurd h₁ nofun
      exact Reach.trans (.tail (.refl _) hs) (ih h)
    · exact absurd h nofun

theorem barReadyB_spec {c : Cfg} {b : Dim3} (h : barReadyB K L c b = true) : BarReady K L c b := by
  unfold barReadyB at h
  split at h
  · exact absurd h nofun
  · next t₀ rest hf =>
    have h₀ : t₀ ∈ L.threads.filter (fun t => t.ctaid = b) := by rw [hf]; exact List.mem_cons_self
    rw [List.mem_filter] at h₀
    refine ⟨⟨t₀, h₀.1, by simpa using h₀.2⟩, (c.ts t₀).pc, fun t ht hb => ?_⟩
    have htf : t ∈ L.threads.filter (fun t => t.ctaid = b) := List.mem_filter.2 ⟨ht, by simpa using hb⟩
    rw [hf] at htf
    have := List.all_eq_true.1 h t htf
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨TRes.isWait_eq this.1, this.2⟩

theorem exec_reach : ∀ (cs : List Choice) {c c' : Cfg}, Cfg.exec K L c cs = some c' → Reach K L c c' := by
  intro cs
  induction cs with
  | nil => intro c c' h; simp only [Cfg.exec, Option.some.injEq] at h; subst h; exact .refl _
  | cons ch cs ih =>
    intro c c' h
    cases ch with
    | run t n =>
      simp only [Cfg.exec] at h
      split at h
      · next ht =>
        split at h
        · next c₁ h₁ => exact Reach.trans (runT_reach ht n h₁) (ih h)
        · exact absurd h nofun
      · exact absurd h nofun
    | rel b =>
      simp only [Cfg.exec] at h
      split at h
      · next hb => exact Reach.trans (.tail (.refl _) (.inr ⟨b, barReadyB_spec hb, rfl⟩)) (ih h)
      · exact absurd h nofun

/-- A configuration the schedule reaches passes check `p`. -/
theorem exec_any {c₀ : Cfg} {cs : List Choice} {p : Cfg → Bool}
    (h : (Cfg.exec K L c₀ cs).any p = true) : ∃ c, Reach K L c₀ c ∧ p c = true := by
  revert h
  cases hc : Cfg.exec K L c₀ cs with
  | none => intro h; exact absurd h nofun
  | some c => intro h; exact ⟨c, exec_reach cs hc, h⟩

theorem faultsB_spec {c : Cfg} (h : faultsB K L c = true) : Faults K L c := by
  unfold faultsB at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · obtain ⟨t, ht, hf⟩ := List.any_eq_true.1 h
    exact .inl ⟨t, ht, TRes.isFault_eq hf⟩
  · obtain ⟨t, ht, h'⟩ := List.any_eq_true.1 h
    obtain ⟨u, hu, h''⟩ := List.any_eq_true.1 h'
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h''
    obtain ⟨⟨hc, hw⟩, hor⟩ := h''
    refine .inr ⟨t, ht, u, hu, hc, TRes.isWait_eq hw, ?_⟩
    rcases hor with hh | ⟨hw', hpc⟩
    · exact .inl (TRes.isHalted_eq hh)
    · exact .inr ⟨TRes.isWait_eq hw', hpc⟩

theorem doneB_spec {c : Cfg} (h : doneB K L c = true) : Done K L c :=
  fun t ht => TRes.isHalted_eq (List.all_eq_true.1 h t ht)

/-- Two reachable configurations with a race refute race freedom. -/
theorem not_raceFree_of {c₀ c₁ c₂ : Cfg} {t u : Tid} {b : Addr} (h₁ : Reach K L c₀ c₁)
    (h₂ : Reach K L c₀ c₂) (h : raceB K L c₁ c₂ t u b = true) : ¬ RaceFree K L c₀ := by
  intro hrf
  unfold raceB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨ht, hu⟩, htu⟩, h⟩ := h
  revert h
  cases hx : c₁.pending K L t with
  | none => intro h; exact absurd h nofun
  | some x =>
    cases hy : c₂.pending K L u with
    | none => intro h; exact absurd h nofun
    | some y =>
      intro h
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not] at h
      obtain ⟨⟨⟨⟨⟨⟨hsp, hsh⟩, hk⟩, hcx⟩, hcy⟩, hna⟩, hnp⟩ := h
      have hc : Conflict t x u y := by
        refine ⟨hsp, fun hs => ?_, hk, b, hcx, hcy⟩
        rcases hsh with h | h
        · exact absurd hs h
        · exact h
      rcases hrf c₁ c₂ h₁ h₂ t ht u hu htu x y hx hy hc with h | h
      · exact hna h
      · exact hnp h

/-- A race between two prefixes of schedules refutes race freedom. -/
theorem race_of_exec {c₀ : Cfg} {cs₁ cs₂ : List Choice} {t u : Tid} {b : Addr}
    (h : (Cfg.exec K L c₀ cs₁).any (fun c₁ => (Cfg.exec K L c₀ cs₂).any fun c₂ =>
      raceB K L c₁ c₂ t u b) = true) : ¬ RaceFree K L c₀ := by
  obtain ⟨c₁, h₁, h'⟩ := exec_any h
  obtain ⟨c₂, h₂, h''⟩ := exec_any h'
  exact not_raceFree_of h₁ h₂ h''

end

end Ptx
