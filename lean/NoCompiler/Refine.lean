import NoCompiler.Spec

/-
Refinement: a function B refines a function A (docs/isa/refine.md).

A is the specification. No postcondition is written by hand: the claim is
that on every entry state where A runs safely and terminates under a
permission `P`, B run from the same state (at its own entry) under the SAME
permission is safe and terminates too, and every way B can end is a way A
can end, up to what the caller cannot observe.

* **Observations** (`Obs`). On return: the pc, the return registers a0 and
  a1, the registers a callee must preserve (sp, gp, tp, s0 to s11), the event
  trace, and all of memory except the dead stack, the `n` bytes below the
  entry sp the permission lets the function use. On exit: the exit status and
  the trace (which ends with the exit event). Caller-saved registers other
  than a0/a1, and the dead stack, may differ.
* **Nondeterminism.** The machine is deterministic except for syscalls,
  whose outcomes the environment chooses (NoCompiler/Env.lean). Refinement is
  trace refinement: for every run of B there is SOME run of A (`Run`) with the
  same observations. Since the trace records what each `write` accepted and
  what each `read` returned, the environment's choices are matched through it.
* **Failure.** An abort (exit with a status) is an observation, so wherever
  A aborts B must abort with the same status after the same events. Where A
  fails (no step: a fault, an access outside `P`, a syscall the model does not
  admit) or does not terminate, the claim says nothing: such states are not
  "entry states where A runs". So the permission and the precondition are
  part of the claim, and a permission too small for A would make it vacuous.
  Each use is meant to come with a proof that A runs under it (for example a
  `VerifiedImg` of A, or an `Exec` at a sample state).

`Refines.verified` turns a refinement and a proof about A into the same proof
about B, so everything stated for verified functions (the call rule, the
adequacy theorems of NoCompiler/Adequacy.lean) applies to B unchanged.
`Refines.of_sim` is the proof method: a simulation relation, checked step by
step, with B's termination inherited from A's.
-/
namespace NoCompiler

/-! ## Runs -/

/-- Some run: a path of `P`-steps, each from a state inside `D`, from `s` to
    `t`. Unlike `Reach` (every run), it says one run exists. -/
inductive Run (c : Code) (P : Perm) (D : Dom) : State → State → Prop
  | refl (s : State) : Run c P D s s
  | step {s s' t : State} : D.mem s.pc → Step c P s s' → Run c P D s' t → Run c P D s t

namespace Run
variable {c : Code} {P : Perm} {D : Dom}

theorem trans {s t u : State} (h : Run c P D s t) (h' : Run c P D t u) : Run c P D s u := by
  induction h with
  | refl => exact h'
  | step hd hs _ ih => exact .step hd hs (ih h')

/-- No step leaves a final state. -/
theorem of_final {s t : State} (hf : Final D s) (h : Run c P D s t) : t = s := by
  cases h with
  | refl => rfl
  | step hd hs _ =>
    obtain ⟨_, _, _, hx⟩ := hs.instrOk
    rcases hf with h | h
    · exact absurd hd h
    · exact absurd hx h
end Run

namespace Reach
variable {c : Code} {P : Perm} {D : Dom}

/-- Every state `Reach` ends in is reached by some run. -/
theorem run {Q : State → Prop} {s : State} (h : Reach c P D Q s) :
    Reach c P D (fun t => Q t ∧ Run c P D s t) s := by
  induction h with
  | done hq => exact .done ⟨hq, .refl _⟩
  | step hd hex _ ih =>
    exact .step hd hex (fun s' h' =>
      Reach.mono (fun t ⟨hq, hr⟩ => ⟨hq, .step hd h' hr⟩) (ih s' h'))
end Reach

namespace Exec
variable {c : Code} {P : Perm} {D : Dom}

/-- A run of `Exec` that ends at a final state ends where `Exec` says. -/
theorem run_final {Q : State → Prop} {s t : State} (h : Exec c P D Q s)
    (hr : Run c P D s t) (hf : Final D t) : Q t := by
  induction h generalizing t with
  | done hq =>
    obtain ⟨hfs, hq⟩ := hq
    rw [hr.of_final hfs]; exact hq
  | step hd hex _ ih =>
    cases hr with
    | refl =>
      obtain ⟨_, hs⟩ := hex
      obtain ⟨_, _, _, hx⟩ := hs.instrOk
      rcases hf with h | h
      · exact absurd hd h
      · exact absurd hx h
    | step _ hs hr' => exact ih _ hs hr' hf
end Exec

/-! ## Observations -/

/-- The return registers. -/
def retRegs : List Reg := [10, 11]

/-- What the caller can see of a final state `tb`, compared with `ta`: the
    same events and exit status; on return also the pc, a0, a1, the preserved
    registers, and memory outside `dead`. -/
def Obs (dead : Region) (ta tb : State) : Prop :=
  ta.trace = tb.trace ∧ ta.exit = tb.exit ∧
  (ta.exit = none →
    ta.pc = tb.pc ∧ (∀ r ∈ retRegs ++ preservedRegs, ta.reg r = tb.reg r) ∧
    ∀ x, ¬ dead.mem x → ta.mem x = tb.mem x)

namespace Obs
theorem refl (dead : Region) (t : State) : Obs dead t t :=
  ⟨rfl, rfl, fun _ => ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩⟩

theorem trans {dead : Region} {ta tb tc : State} (h₁ : Obs dead ta tb) (h₂ : Obs dead tb tc) :
    Obs dead ta tc := by
  obtain ⟨t₁, x₁, h₁⟩ := h₁
  obtain ⟨t₂, x₂, h₂⟩ := h₂
  refine ⟨t₁.trans t₂, x₁.trans x₂, fun hx => ?_⟩
  obtain ⟨p₁, r₁, m₁⟩ := h₁ hx
  obtain ⟨p₂, r₂, m₂⟩ := h₂ (x₁ ▸ hx)
  exact ⟨p₁.trans p₂, fun r hr => (r₁ r hr).trans (r₂ r hr), fun y hy => (m₁ y hy).trans (m₂ y hy)⟩
end Obs

/-! ## Refinement -/

/-- The dead stack of a function with specification `sp` entered at `s`. -/
def Spec.dead {α : Type} (sp : Spec α) (s : State) : Region := Spec.stackRegion s sp.stack

/-- The relational part of a refinement: wherever A runs safely and ends, B
    (code `cB`, region `DB`, entry `eB`) does too and ends as some run of A
    (`cA`, `DA`, `eA`) does, for the entries `sp.pre` allows, under the
    permission `sp.perm` (the postcondition of `sp` plays no part). On its own
    it is CONDITIONAL on A's run, and so vacuous for an A that never runs:
    a refinement is stated as `Refines`, which also carries `ARuns`. The
    proof methods (`of_sim`, `of_bigSim`, `of_cert`) prove this part. -/
def RefinesRel {α : Type} (sp : Spec α) (cA : Code) (DA : Dom) (eA : Word)
    (cB : Code) (DB : Dom) (eB : Word) : Prop :=
  ∀ a s, Entry DA eA s → ¬ DB.mem (s.reg Reg.ra) → sp.pre a s →
    Exec cA (sp.perm a s) DA (fun _ => True) s →
    Exec cB (sp.perm a s) DB
      (fun tb => ∃ ta, Run cA (sp.perm a s) DA s ta ∧ Final DA ta ∧ Obs (sp.dead s) ta tb)
      (s.setPc eB)

/-- A runs: from every entry `sp` allows, A runs safely under `sp.perm` and
    ends (leaves `DA` or exits). Decision 2026-11-21 (3): a refinement is only
    stated together with this. -/
def ARuns {α : Type} (sp : Spec α) (cA : Code) (DA : Dom) (eA : Word) : Prop :=
  ∀ a s, Entry DA eA s → sp.pre a s → Exec cA (sp.perm a s) DA (fun _ => True) s

/-- B refines A (docs/isa/refine.md): A runs from every entry `sp` allows
    (`runs`), and wherever it does, B runs too and ends as A does (`rel`). -/
structure Refines {α : Type} (sp : Spec α) (cA : Code) (DA : Dom) (eA : Word)
    (cB : Code) (DB : Dom) (eB : Word) : Prop where
  runs : ARuns sp cA DA eA
  rel : RefinesRel sp cA DA eA cB DB eB

/-- A verified function runs. -/
theorem ARuns.of_verified {α : Type} {sp : Spec α} {c : Code} {D : Dom} {e : Word}
    (h : VerifiedImg c D e sp) : ARuns sp c D e :=
  fun a s he hp => Exec.mono (fun _ _ => trivial) (h a s he hp)

@[simp] theorem State.setPc_self (s : State) : s.setPc s.pc = s := rfl
@[simp] theorem State.setPc_setPc (s : State) (p q : Word) : (s.setPc p).setPc q = s.setPc q := rfl
@[simp] theorem State.reg_setPc (s : State) (p : Word) (r : Reg) : (s.setPc p).reg r = s.reg r := rfl

section
variable {α : Type} {sp : Spec α}

theorem Spec.perm_setPc (a : α) (s : State) (p : Word) (h : ∀ a s p, sp.reads a (s.setPc p) = sp.reads a s)
    (h' : ∀ a s p, sp.writes a (s.setPc p) = sp.writes a s) : sp.perm a (s.setPc p) = sp.perm a s := by
  simp only [Spec.perm, Spec.stackRegion, State.reg_setPc, h, h']

theorem RefinesRel.refl (c : Code) (D : Dom) (e : Word) : RefinesRel sp c D e c D e := by
  intro a s he _ _ hA
  rw [← he.pc, State.setPc_self]
  exact Reach.mono (fun t ⟨⟨hf, _⟩, hr⟩ => ⟨hf, t, hr, hf, Obs.refl _ t⟩) hA.run

/-- Every function that runs refines itself. -/
theorem Refines.refl {c : Code} {D : Dom} {e : Word} (h : ARuns sp c D e) : Refines sp c D e c D e :=
  ⟨h, RefinesRel.refl c D e⟩

theorem RefinesRel.trans {cA cB cC : Code} {DA DB DC : Dom} {eA eB eC : Word}
    (h₁ : RefinesRel sp cA DA eA cB DB eB) (h₂ : RefinesRel sp cB DB eB cC DC eC)
    (hB : ∀ s, Entry DA eA s → ¬ DC.mem (s.reg Reg.ra) → Entry DB eB (s.setPc eB))
    (hpre : ∀ a s, sp.pre a s → sp.pre a (s.setPc eB))
    (hperm : ∀ a s, sp.perm a (s.setPc eB) = sp.perm a s) :
    RefinesRel sp cA DA eA cC DC eC := by
  intro a s he hC hp hA
  have hEB := hB s he hC
  have hBx := h₁ a s he hEB.ret hp hA
  have hBsafe : Exec cB (sp.perm a (s.setPc eB)) DB (fun _ => True) (s.setPc eB) := by
    rw [hperm]; exact Exec.mono (fun _ _ => trivial) hBx
  have hCx := h₂ a (s.setPc eB) hEB (by simpa using hC) (hpre a s hp) hBsafe
  rw [hperm, State.setPc_setPc] at hCx
  refine Exec.mono (fun tc ⟨tb, hrb, hfb, hob⟩ => ?_) hCx
  obtain ⟨ta, hra, hfa, hoa⟩ := hBx.run_final hrb hfb
  exact ⟨ta, hra, hfa, hoa.trans (by simpa [Spec.dead, Spec.stackRegion] using hob)⟩

/-- Refinement composes: a sequence of edits, each proved, is proved. The
    middle function has to be enterable wherever the outer two are. -/
theorem Refines.trans {cA cB cC : Code} {DA DB DC : Dom} {eA eB eC : Word}
    (h₁ : Refines sp cA DA eA cB DB eB) (h₂ : Refines sp cB DB eB cC DC eC)
    (hB : ∀ s, Entry DA eA s → ¬ DC.mem (s.reg Reg.ra) → Entry DB eB (s.setPc eB))
    (hpre : ∀ a s, sp.pre a s → sp.pre a (s.setPc eB))
    (hperm : ∀ a s, sp.perm a (s.setPc eB) = sp.perm a s) :
    Refines sp cA DA eA cC DC eC :=
  ⟨h₁.runs, h₁.rel.trans h₂.rel hB hpre hperm⟩

/-- A specification that does not look at the entry pc. -/
structure Spec.PcFree (sp : Spec α) : Prop where
  pre : ∀ a s p, sp.pre a (s.setPc p) ↔ sp.pre a s
  post : ∀ a s p t, sp.post a (s.setPc p) t ↔ sp.post a s t
  onExit : ∀ a s p t, sp.onExit a (s.setPc p) t ↔ sp.onExit a s t
  reads : ∀ a s p, sp.reads a (s.setPc p) = sp.reads a s
  writes : ∀ a s p, sp.writes a (s.setPc p) = sp.writes a s

/-- A specification whose postcondition sees only observations: what it says
    of a final state it says of every state with the same observations. -/
def Spec.ObsInv (sp : Spec α) : Prop :=
  ∀ a s ta tb, Obs (sp.dead s) ta tb → sp.Done a s ta → sp.Done a s tb

/-- `sp`, entered only with a return address outside `D`. -/
def Spec.avoid (sp : Spec α) (D : Dom) : Spec α :=
  { sp with pre := fun a s => sp.pre a s ∧ ¬ D.mem (s.reg Reg.ra) }

/-- A proof about A is a proof about every B that refines it, for the
    entries whose return address is not in A's code (A's proof says nothing
    about the others: there, A's return would run A again). At a concrete
    call site that is decidable; when B replaces A in place it holds of every
    caller outside both. -/
theorem Refines.verified {cA cB : Code} {DA DB : Dom} {eA eB : Word}
    (hr : Refines sp cA DA eA cB DB eB) (hv : VerifiedImg cA DA eA sp)
    (hpc : sp.PcFree) (hobs : sp.ObsInv) :
    VerifiedImg cB DB eB (sp.avoid DA) := by
  rintro a s he ⟨hp, hra⟩
  have hperm : sp.perm a (s.setPc eA) = sp.perm a s := Spec.perm_setPc a s eA hpc.reads hpc.writes
  have hEA : Entry DA eA (s.setPc eA) :=
    ⟨rfl, he.live, hra, he.retAligned, he.sp⟩
  have hpA : sp.pre a (s.setPc eA) := (hpc.pre a s eA).2 hp
  have hA := hv a _ hEA hpA
  have hB := hr.rel a _ hEA (by simpa using he.ret) hpA (Exec.mono (fun _ _ => trivial) hA)
  rw [hperm, State.setPc_setPc, ← he.pc, State.setPc_self] at hB
  show Exec cB (sp.perm a s) DB (sp.Done a s) s
  refine Exec.mono (fun tb ⟨ta, hrun, hf, ho⟩ => ?_) hB
  have hd : sp.Done a (s.setPc eA) ta := hA.run_final (hperm ▸ hrun) hf
  have hd' : sp.Done a s ta := by
    unfold Spec.Done at hd ⊢
    simpa only [State.reg_setPc, hpc.post, hpc.onExit, Preserved] using hd
  exact hobs a s ta tb (by simpa [Spec.dead, Spec.stackRegion] using ho) hd'

end

/-! ## The proof method: simulation -/

section Sim
variable {cA cB : Code} {P : Perm} {DA DB : Dom}

/-- A simulation between runs of A and runs of B under one permission `P`.
    From related states `R sa sb`: if B has finished, A can finish with the
    same observations; otherwise B can step, and every B step is matched by
    one or more A steps into related states, or by none (a stutter) with the
    measure `μ` on B's state decreasing. Both obligations may use that A, at
    `sa`, has finished or can step: A's run is safe. -/
structure Sim (cA : Code) (DA : Dom) (cB : Code) (DB : Dom) (P : Perm) (dead : Region)
    (R : State → State → Prop) (μ : State → Nat) : Prop where
  fin : ∀ sa sb, R sa sb → Final DB sb →
    ∃ ta, Run cA P DA sa ta ∧ Final DA ta ∧ Obs dead ta sb
  progress : ∀ sa sb, R sa sb → ¬ Final DB sb → (Final DA sa ∨ ∃ sa', Step cA P sa sa') →
    ∃ sb', Step cB P sb sb'
  step : ∀ sa sb, R sa sb → ¬ Final DB sb → (Final DA sa ∨ ∃ sa', Step cA P sa sa') →
    ∀ sb', Step cB P sb sb' →
    (∃ s₁ sa', DA.mem sa.pc ∧ Step cA P sa s₁ ∧ Run cA P DA s₁ sa' ∧ R sa' sb') ∨
    (R sa sb' ∧ μ sb' < μ sb)

theorem not_final {D : Dom} {s : State} (h : ¬ Final D s) : D.mem s.pc ∧ s.exit = none := by
  unfold Final at h
  exact ⟨Classical.byContradiction fun hm => h (.inl hm),
    Classical.byContradiction fun hx => h (.inr hx)⟩

/-- A simulation turns A's safe, terminating run into B's, with every way B
    ends matched by a way A ends. B's termination comes from A's: every B step
    either advances A, whose runs are finite, or decreases `μ`. -/
theorem Sim.exec {dead : Region} {R : State → State → Prop} {μ : State → Nat}
    (hs : Sim cA DA cB DB P dead R μ) {s₀ : State} {Q : State → Prop}
    (hA : Exec cA P DA Q s₀) :
    ∀ sb, R s₀ sb →
      Exec cB P DB (fun tb => ∃ ta, Run cA P DA s₀ ta ∧ Final DA ta ∧ Obs dead ta tb) sb := by
  -- Φ sa: from every state A can reach from sa (and from s₀), every related B state is fine.
  suffices H : ∀ sa, Reach cA P DA (fun s => Final DA s ∧ Q s) sa → ∀ sx, Run cA P DA sa sx →
      Run cA P DA s₀ sx → ∀ sb, R sx sb →
      Exec cB P DB (fun tb => ∃ ta, Run cA P DA s₀ ta ∧ Final DA ta ∧ Obs dead ta tb) sb from
    fun sb hr => H s₀ hA s₀ (.refl _) (.refl _) sb hr
  intro sa hA
  induction hA with
  | @done sa hq =>
    intro sx hrun h0 sb hr
    rw [hrun.of_final hq.1] at hr h0
    induction hm : μ sb using Nat.strongRecOn generalizing sb with
    | _ n ih =>
      by_cases hf : Final DB sb
      · obtain ⟨ta, hra, hfa, ho⟩ := hs.fin _ _ hr hf
        exact .done ⟨hf, ta, h0.trans hra, hfa, ho⟩
      · obtain ⟨hd, _⟩ := not_final hf
        refine .step hd (hs.progress _ _ hr hf (.inl hq.1)) (fun sb' h' => ?_)
        rcases hs.step _ _ hr hf (.inl hq.1) sb' h' with ⟨s₁, _, hd', hst, _, _⟩ | ⟨hr', hlt⟩
        · obtain ⟨_, _, _, hx⟩ := hst.instrOk
          rcases hq.1 with h | h
          · exact absurd hd' h
          · exact absurd hx h
        · exact ih _ (hm ▸ hlt) sb' hr' rfl
  | @step sa hdA hex _ ih =>
    intro sx hrun h0 sb hr
    cases hrun with
    | step _ hst hrun' => exact ih _ hst sx hrun' h0 sb hr
    | refl =>
      induction hm : μ sb using Nat.strongRecOn generalizing sb with
      | _ n ihm =>
        by_cases hf : Final DB sb
        · obtain ⟨ta, hra, hfa, ho⟩ := hs.fin _ _ hr hf
          exact .done ⟨hf, ta, h0.trans hra, hfa, ho⟩
        · obtain ⟨hd, _⟩ := not_final hf
          refine .step hd (hs.progress _ _ hr hf (.inr hex)) (fun sb' h' => ?_)
          rcases hs.step _ _ hr hf (.inr hex) sb' h' with ⟨s₁, sa', _, hst, hrun₁, hr'⟩ | ⟨hr', hlt⟩
          · exact ih s₁ hst sa' hrun₁ (h0.trans (.step hdA hst hrun₁)) sb' hr'
          · exact ihm _ (hm ▸ hlt) sb' hr' rfl

/-- `RefinesRel` from a simulation that relates every entry state of A to
    the same state at B's entry. -/
theorem RefinesRel.of_sim {α : Type} {sp : Spec α} {eA eB : Word}
    (R : α → State → State → State → Prop) (μ : State → Nat)
    (hsim : ∀ a s, Entry DA eA s → ¬ DB.mem (s.reg Reg.ra) → sp.pre a s →
      Sim cA DA cB DB (sp.perm a s) (sp.dead s) (R a s) μ)
    (hR : ∀ a s, Entry DA eA s → sp.pre a s → R a s s (s.setPc eB)) :
    RefinesRel sp cA DA eA cB DB eB := by
  intro a s he hb hp hA
  exact (hsim a s he hb hp).exec hA _ (hR a s he hp)

/-- `Refines` from A's run and a simulation. -/
theorem Refines.of_sim {α : Type} {sp : Spec α} {eA eB : Word} (hA : ARuns sp cA DA eA)
    (R : α → State → State → State → Prop) (μ : State → Nat)
    (hsim : ∀ a s, Entry DA eA s → ¬ DB.mem (s.reg Reg.ra) → sp.pre a s →
      Sim cA DA cB DB (sp.perm a s) (sp.dead s) (R a s) μ)
    (hR : ∀ a s, Entry DA eA s → sp.pre a s → R a s s (s.setPc eB)) :
    Refines sp cA DA eA cB DB eB :=
  ⟨hA, RefinesRel.of_sim R μ hsim hR⟩

end Sim

/-! ## Big-step simulation -/

section BigSim
variable {cA cB : Code} {P : Perm} {DA DB : Dom}

/-- One or more `P`-steps of A inside `DA`. -/
def RunPlus (c : Code) (P : Perm) (D : Dom) (s t : State) : Prop :=
  ∃ s₁, D.mem s.pc ∧ Step c P s s₁ ∧ Run c P D s₁ t

/-- A big-step simulation: from related states, if B has finished then A can
    finish with the same observations; otherwise B's run (every run) reaches
    states related to states A reaches by one or more steps. `F` relates the
    final states: `Obs` for a function, `RRegion.Exit` for a region. Single steps,
    straight-line blocks and whole regions are all instances. The obligation
    may use that A's run from `sa` is safe and terminates. -/
structure BigSim (cA : Code) (DA : Dom) (cB : Code) (DB : Dom) (P : Perm)
    (F : State → State → Prop) (R : State → State → Prop) : Prop where
  fin : ∀ sa sb, R sa sb → Final DB sb →
    ∃ ta, Run cA P DA sa ta ∧ Final DA ta ∧ F ta sb
  move : ∀ sa sb, R sa sb → ¬ Final DB sb → Exec cA P DA (fun _ => True) sa →
    Reach cB P DB (fun tb => ∃ ta, RunPlus cA P DA sa ta ∧ R ta tb) sb

theorem RunPlus.not_final {c : Code} {P : Perm} {D : Dom} {s t : State} (h : RunPlus c P D s t) :
    ¬ Final D s := by
  obtain ⟨_, hd, hs, _⟩ := h
  obtain ⟨_, _, _, hx⟩ := hs.instrOk
  intro hf; rcases hf with h | h
  · exact h hd
  · exact h hx

theorem BigSim.exec {F : State → State → Prop} {R : State → State → Prop}
    (hs : BigSim cA DA cB DB P F R) {s₀ : State} {Q : State → Prop}
    (hA : Exec cA P DA Q s₀) :
    ∀ sb, R s₀ sb →
      Exec cB P DB (fun tb => ∃ ta, Run cA P DA s₀ ta ∧ Final DA ta ∧ F ta tb) sb := by
  suffices H : ∀ sa, Reach cA P DA (fun s => Final DA s ∧ Q s) sa → ∀ sx, Run cA P DA sa sx →
      Run cA P DA s₀ sx → ∀ sb, R sx sb →
      Exec cB P DB (fun tb => ∃ ta, Run cA P DA s₀ ta ∧ Final DA ta ∧ F ta tb) sb from
    fun sb hr => H s₀ hA s₀ (.refl _) (.refl _) sb hr
  intro sa hA
  induction hA with
  | @done sa hq =>
    intro sx hrun h0 sb hr
    rw [hrun.of_final hq.1] at hr h0
    by_cases hf : Final DB sb
    · obtain ⟨ta, hra, hfa, ho⟩ := hs.fin _ _ hr hf
      exact .done ⟨hf, ta, h0.trans hra, hfa, ho⟩
    · exact Reach.mono (fun _ ⟨_, hp, _⟩ => absurd hq.1 hp.not_final)
        (hs.move _ _ hr hf (.done ⟨hq.1, trivial⟩))
  | @step sa hdA hex hall ih =>
    intro sx hrun h0 sb hr
    cases hrun with
    | step _ hst hrun' => exact ih _ hst sx hrun' h0 sb hr
    | refl =>
      by_cases hf : Final DB sb
      · obtain ⟨ta, hra, hfa, ho⟩ := hs.fin _ _ hr hf
        exact .done ⟨hf, ta, h0.trans hra, hfa, ho⟩
      · have hA' : Exec cA P DA (fun _ => True) sa :=
          Exec.mono (fun _ _ => trivial) (Reach.step hdA hex hall)
        refine Reach.trans (hs.move _ _ hr hf hA') (fun tb ⟨ta, ⟨s₁, _, hst, hrun₁⟩, hr'⟩ => ?_)
        exact ih s₁ hst ta hrun₁ (h0.trans (.step hdA hst hrun₁)) tb hr'

theorem RefinesRel.of_bigSim {α : Type} {sp : Spec α} {eA eB : Word}
    (R : α → State → State → State → Prop)
    (hsim : ∀ a s, Entry DA eA s → ¬ DB.mem (s.reg Reg.ra) → sp.pre a s →
      BigSim cA DA cB DB (sp.perm a s) (Obs (sp.dead s)) (R a s))
    (hR : ∀ a s, Entry DA eA s → sp.pre a s → R a s s (s.setPc eB)) :
    RefinesRel sp cA DA eA cB DB eB := by
  intro a s he hb hp hA
  exact (hsim a s he hb hp).exec hA _ (hR a s he hp)

theorem Refines.of_bigSim {α : Type} {sp : Spec α} {eA eB : Word} (hA : ARuns sp cA DA eA)
    (R : α → State → State → State → Prop)
    (hsim : ∀ a s, Entry DA eA s → ¬ DB.mem (s.reg Reg.ra) → sp.pre a s →
      BigSim cA DA cB DB (sp.perm a s) (Obs (sp.dead s)) (R a s))
    (hR : ∀ a s, Entry DA eA s → sp.pre a s → R a s s (s.setPc eB)) :
    Refines sp cA DA eA cB DB eB :=
  ⟨hA, RefinesRel.of_bigSim R hsim hR⟩

/-- A safe run in `D` is a safe run in any `E ⊆ D`, stopped at `E`'s exit. -/
theorem Exec.restrict {c : Code} {P : Perm} {D E : Dom} {Q : State → Prop} {s : State}
    (h : Exec c P D Q s) (hE : E.sub D) : Exec c P E (fun _ => True) s := by
  induction h with
  | done hq =>
    refine .done ⟨?_, trivial⟩
    rcases hq.1 with h | h
    · exact .inl (fun hm => h (hE _ hm))
    · exact .inr h
  | @step s hd hex _ ih =>
    by_cases hm : E.mem s.pc
    · exact .step hm hex ih
    · exact .done ⟨.inl hm, trivial⟩

/-- A run inside `E ⊆ D` is a run inside `D`. -/
theorem Run.mono_dom {c : Code} {P : Perm} {D E : Dom} {s t : State} (h : Run c P E s t)
    (hE : E.sub D) : Run c P D s t := by
  induction h with
  | refl => exact .refl _
  | step hd hs _ ih => exact .step (hE _ hd) hs ih

end BigSim

end NoCompiler
