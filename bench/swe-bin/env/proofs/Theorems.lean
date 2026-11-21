import Spec
import H5iAppLib
import H5iAppLib.ReadOnly
open Aeneas Aeneas.Std Result Aeneas.Std.WP H5iAppLib swe_bin_kernel swe_bin_kernel.Spec

namespace swe_bin_kernel.Theorems

theorem list4_eq (l1 l2 : List U64) (h1 : l1.length = 4) (h2 : l2.length = 4) :
    l1 = l2 ↔ (l1[0]'(by omega) = l2[0]'(by omega) ∧ l1[1]'(by omega) = l2[1]'(by omega) ∧
      l1[2]'(by omega) = l2[2]'(by omega) ∧ l1[3]'(by omega) = l2[3]'(by omega)) := by
  match l1, l2, h1, h2 with
  | [a0, a1, a2, a3], [b0, b1, b2, b3], _, _ => simp

theorem hash_eq_spec (a b : Hash) : hash_eq a b ⦃ v => (v = true ↔ SameBinary a b) ⦄ := by
  unfold hash_eq SameBinary
  rw [list4_eq _ _ (by simp) (by simp)]
  step*

theorem kind_eq_spec (a b : ProofKind) : kind_eq a b ⦃ v => (v = true ↔ a = b) ⦄ := by
  cases a <;> cases b <;> simp [kind_eq]

theorem bonus_kind_eq (m : Mode) : bonus_kind m = ok (bonusKind m) := by
  cases m <;> simp [bonus_kind, bonusKind]

theorem all_pass_spec (t : Task) (tests : Option Tests) (h : Hash) :
    all_pass t tests h ⦃ v => (v = true ↔ AllPass t tests h) ⦄ := by
  unfold all_pass AllPass
  cases tests with
  | none => simp
  | some r =>
    have := hash_eq_spec r.binary h
    step*

theorem proof_ok_spec (t : Task) (proof : Option Proof) (h : Hash) :
    proof_ok t proof h ⦃ v => (v = true ↔ ProofOk t proof h) ⦄ := by
  unfold proof_ok ProofOk
  cases proof with
  | none => simp
  | some p =>
    have := hash_eq_spec p.binary h
    have := kind_eq_spec p.kind (bonusKind t.mode)
    simp only [bonus_kind_eq]
    step*
    all_goals skip

theorem reward_spec (t : Task) (tests : Option Tests) (proof : Option Proof) (h : Hash) :
    reward t tests proof h ⦃ r => r.val = Spec.reward t tests proof h ⦄ := by
  unfold reward Spec.reward
  have := all_pass_spec t tests h
  have := proof_ok_spec t proof h
  step*
  all_goals (simp_all [FULL_MILLI, BONUS_MILLI, FULL, BONUS]; try scalar_tac)

/-- The tasks `Reset` accepts. -/
def ValidTask (t : Task) : Prop := 1 ≤ t.f2p.val ∧ t.f2p.val ≤ 100000 ∧ t.p2p.val ≤ 100000

theorem valid_task_spec (t : Task) : valid_task t ⦃ v => (v = true ↔ ValidTask t) ⦄ := by
  unfold valid_task ValidTask
  simp only [MAX_TESTS]
  step* <;> simp_all <;> scalar_tac

/-- The snapshot after a command commits `w`. -/
def after (s : Snapshot) : Option Snapshot → Snapshot
  | none => s
  | some n => n

/-- `Submit` from a running episode: it ends the episode, records the binary, keeps the task and
the reports, and pays `Spec.reward` for the binary; the reply carries the same reward. -/
theorem submit_spec (s : Snapshot) (h : Hash) (hd : s.done = false) (hs : s.started = true) :
    transition () s (.Submit h) ⦃ r => ∃ s' rep, r = .Ok (some s', rep) ∧ s'.done = true ∧
      s'.submitted = some h ∧ s'.task = s.task ∧ s'.tests = s.tests ∧ s'.proof = s.proof ∧
      s'.reward_milli.val = Spec.reward s.task s.tests s.proof h ∧
      rep.reward_milli = s'.reward_milli ∧ rep.done = true ⦄ := by
  unfold transition reply
  have := reward_spec s.task s.tests s.proof h
  simp only [hd, hs]
  step*
  all_goals skip

theorem spec_reward_cases (t : Task) (tests : Option Tests) (proof : Option Proof) (h : Hash) :
    (FULL ≤ Spec.reward t tests proof h ↔ AllPass t tests h) ∧
    (FULL < Spec.reward t tests proof h ↔ AllPass t tests h ∧ ProofOk t proof h) ∧
    (Spec.reward t tests proof h = 0 ∨ Spec.reward t tests proof h = FULL ∨
      Spec.reward t tests proof h = FULL + BONUS) := by
  unfold Spec.reward
  by_cases ha : AllPass t tests h <;> by_cases hp : ProofOk t proof h <;> simp [ha, hp, FULL, BONUS]

/-- **The full reward iff all tests pass**: a submission earns at least `FULL` exactly when the
last test report is about the submitted binary and every FAIL_TO_PASS and PASS_TO_PASS test
passed. In both modes. -/
theorem full_reward_iff_all_pass (s : Snapshot) (h : Hash) (hd : s.done = false)
    (hs : s.started = true) :
    transition () s (.Submit h) ⦃ r => ∃ s' rep, r = .Ok (some s', rep) ∧
      (FULL ≤ s'.reward_milli.val ↔ AllPass s.task s.tests h) ⦄ := by
  apply WP.spec_mono (submit_spec s h hd hs)
  rintro r ⟨s', rep, hr, -, -, -, -, -, hrew, -, -⟩
  exact ⟨s', rep, hr, by rw [hrew]; exact (spec_reward_cases _ _ _ _).1⟩

/-- **The bonus only with a checked proof**: a submission earns more than `FULL` exactly when,
besides every test passing, the last proof result is a checked proof about the submitted
binary, of the kind the episode's mode asks for. -/
theorem bonus_only_with_proof (s : Snapshot) (h : Hash) (hd : s.done = false)
    (hs : s.started = true) :
    transition () s (.Submit h) ⦃ r => ∃ s' rep, r = .Ok (some s', rep) ∧
      (FULL < s'.reward_milli.val ↔ AllPass s.task s.tests h ∧ ProofOk s.task s.proof h) ⦄ := by
  apply WP.spec_mono (submit_spec s h hd hs)
  rintro r ⟨s', rep, hr, -, -, -, -, -, hrew, -, -⟩
  exact ⟨s', rep, hr, by rw [hrew]; exact (spec_reward_cases _ _ _ _).2.1⟩

/-- A submission pays 0, `FULL` or `FULL + BONUS`, nothing else. -/
theorem reward_values (s : Snapshot) (h : Hash) (hd : s.done = false) (hs : s.started = true) :
    transition () s (.Submit h) ⦃ r => ∃ s' rep, r = .Ok (some s', rep) ∧
      (s'.reward_milli.val = 0 ∨ s'.reward_milli.val = FULL ∨
        s'.reward_milli.val = FULL + BONUS) ⦄ := by
  apply WP.spec_mono (submit_spec s h hd hs)
  rintro r ⟨s', rep, hr, -, -, -, -, -, hrew, -, -⟩
  exact ⟨s', rep, hr, by rw [hrew]; exact (spec_reward_cases _ _ _ _).2.2⟩

/-- Patch mode: the bonus needs a checked `Refines` proof about the submitted binary. -/
theorem patch_bonus_needs_refines (s : Snapshot) (h : Hash) (hd : s.done = false)
    (hs : s.started = true) (hm : s.task.mode = .Patch) :
    transition () s (.Submit h) ⦃ r => ∀ s' rep, r = .Ok (some s', rep) →
      FULL < s'.reward_milli.val →
      ∃ p, s.proof = some p ∧ p.checked = true ∧ SameBinary p.binary h ∧ p.kind = .Refines ⦄ := by
  apply WP.spec_mono (bonus_only_with_proof s h hd hs)
  rintro r ⟨s', rep, hr, hiff⟩ s'' rep' he hlt
  rw [hr] at he
  simp only [core.result.Result.Ok.injEq, Prod.mk.injEq, Option.some.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨-, p, hp, hc, hb, hk⟩ := hiff.1 hlt
  exact ⟨p, hp, hc, hb, by rw [hk, hm]; rfl⟩

/-- Scratch mode: the bonus needs a checked `Verified` proof (against a non-vacuous spec) about
the submitted binary. -/
theorem scratch_bonus_needs_verified (s : Snapshot) (h : Hash) (hd : s.done = false)
    (hs : s.started = true) (hm : s.task.mode = .Scratch) :
    transition () s (.Submit h) ⦃ r => ∀ s' rep, r = .Ok (some s', rep) →
      FULL < s'.reward_milli.val →
      ∃ p, s.proof = some p ∧ p.checked = true ∧ SameBinary p.binary h ∧ p.kind = .Verified ⦄ := by
  apply WP.spec_mono (bonus_only_with_proof s h hd hs)
  rintro r ⟨s', rep, hr, hiff⟩ s'' rep' he hlt
  rw [hr] at he
  simp only [core.result.Result.Ok.injEq, Prod.mk.injEq, Option.some.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨-, p, hp, hc, hb, hk⟩ := hiff.1 hlt
  exact ⟨p, hp, hc, hb, by rw [hk, hm]; rfl⟩

/-- A snapshot that pays has ended with a submission. -/
def Paid (s : Snapshot) : Prop := s.reward_milli.val ≠ 0 → s.done = true ∧ s.submitted.isSome

theorem initial_paid : initial ⦃ s => Paid s ∧ s.started = false ⦄ := by
  unfold initial Paid; simp

/-- **No reward without a submission**: every command keeps `Paid`, and a reply that carries a
reward comes with a recorded submission. Only `Submit` sets a reward. -/
theorem no_reward_without_submission (s : Snapshot) (c : Command) (hi : Paid s) :
    transition () s c ⦃ r => ∀ w rep, r = .Ok (w, rep) →
      Paid (after s w) ∧ (rep.reward_milli.val ≠ 0 → (after s w).submitted.isSome) ⦄ := by
  unfold transition reply
  cases c with
  | Reset t =>
    have := valid_task_spec t
    step* <;> simp_all [after, Paid]
  | RecordTests t => step* <;> simp_all [after, Paid]
  | RecordProof p => step* <;> simp_all [after, Paid]
  | Submit h =>
    have := reward_spec s.task s.tests s.proof h
    step* <;> simp_all [after, Paid]
  | State => step* <;> simp_all [after, Paid]

/-- Only `Submit` changes the reward or `done` (besides `Reset`, which starts a new episode),
and it sets `done`. -/
theorem only_submit_pays (s : Snapshot) (c : Command) (hc : ∀ h, c ≠ .Submit h)
    (hr : ∀ t, c ≠ .Reset t) :
    transition () s c ⦃ r => ∀ w rep, r = .Ok (w, rep) →
      (after s w).reward_milli = s.reward_milli ∨ (after s w).reward_milli.val = 0 ⦄ := by
  unfold transition reply
  cases c with
  | Reset t => exact absurd rfl (hr t)
  | Submit h => exact absurd rfl (hc h)
  | RecordTests t => step* <;> simp_all [after]
  | RecordProof p => step* <;> simp_all [after]
  | State => step* <;> simp_all [after]

/-- **Done is final**: once an episode has ended, every report and every submission is refused,
and nothing is committed. (`Reset` starts a new episode; `State` only reads.) -/
theorem done_is_final (s : Snapshot) (hd : s.done = true) :
    (∀ t, transition () s (.RecordTests t) = ok (.Err .Done)) ∧
    (∀ p, transition () s (.RecordProof p) = ok (.Err .Done)) ∧
    (∀ h, transition () s (.Submit h) = ok (.Err .Done)) ∧
    transition () s .State = ok (.Ok (none, { reward_milli := s.reward_milli, done := true })) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> unfold transition reply <;> simp [hd]

/-- No command but `Reset` changes the task, so the mode and the test counts are fixed for the
whole episode. -/
theorem task_is_fixed (s : Snapshot) (c : Command) (hr : ∀ t, c ≠ .Reset t) :
    transition () s c ⦃ r => ∀ w rep, r = .Ok (w, rep) → (after s w).task = s.task ⦄ := by
  unfold transition reply
  cases c with
  | Reset t => exact absurd rfl (hr t)
  | Submit h =>
    have := reward_spec s.task s.tests s.proof h
    step* <;> simp_all [after]
  | RecordTests t => step* <;> simp_all [after]
  | RecordProof p => step* <;> simp_all [after]
  | State => step* <;> simp_all [after]

/-- `Reset` with a valid task starts a running episode in the task's mode with nothing
recorded and no reward. -/
theorem reset_spec (s : Snapshot) (t : Task) (hv : ValidTask t) :
    transition () s (.Reset t) ⦃ r => ∃ s' rep, r = .Ok (some s', rep) ∧ s'.task = t ∧
      s'.started = true ∧ s'.done = false ∧ s'.tests = none ∧ s'.proof = none ∧
      s'.submitted = none ∧ s'.reward_milli.val = 0 ⦄ := by
  unfold transition reply
  have := valid_task_spec t
  step* <;> simp_all

/-- The kernel never fails: no panic or overflow, for any input. -/
theorem transition_total (a : Unit) (s : Snapshot) (c : Command) :
    ∃ r, transition a s c = ok r := by
  have h : transition a s c ⦃ _ => True ⦄ := by
    unfold transition reply
    cases c with
    | Reset t =>
      have := valid_task_spec t
      step*
    | Submit h =>
      have := reward_spec s.task s.tests s.proof h
      step*
    | RecordTests t => step*
    | RecordProof p => step*
    | State => step*
  obtain ⟨r, hr, -⟩ := (WP.spec_equiv_exists _ _).1 h
  exact ⟨r, hr⟩

/-- Panic freedom, as `H5iAppLib.Obligation.PanicFree` states it. -/
theorem panic_free : H5iAppLib.Obligation.PanicFree transition :=
  H5iAppLib.Obligation.panicFree_of_total transition_total

def writesOf : Option Snapshot → List Snapshot
  | none => []
  | some s => [s]

/-- `State`, the only command `read_only` admits, writes nothing. -/
theorem read_only_sound : H5iAppLib.Obligation.ReadOnlySound read_only transition writesOf := by
  apply H5iAppLib.ReadOnly.sound_of_spec
  intro a s c hro
  cases c <;> simp [read_only] at hro
  unfold transition reply
  simp [H5iAppLib.OnOk, writesOf]

end swe_bin_kernel.Theorems
