import NoCompiler.Lemmas

/-
What an `Exec` proof says about the machine (`HwStep`), which fetches its
instructions from memory and checks no permission.

Given that memory holds the code image (`Code.Loaded`, established by the
loader) and that nothing `P` lets the program write overlaps the code
(`Protected`, so the image stays loaded), every machine execution from the
starting state that has not yet left the region `D`:

* `Exec.hw_safe`: can take a step (no fault, no instruction outside the
  profile, no unmodeled syscall), and every step it can take is a step
  `P` allows: memory safety;
* `Exec.hw_final`: satisfies the postcondition when it leaves `D` or exits;
* `Exec.hw_terminates`: cannot stay in `D` forever.

These are the statements every function proof inherits. They are proved once,
here, for every program.
-/
namespace NoCompiler

/-- Writable memory and code do not overlap. -/
def Protected (c : Code) (P : Perm) : Prop := ∀ x, P.writable x → ¬ c.mem x

/-- A machine execution from `s` to `t` whose every state before `t` is in `D`. -/
inductive HwRun (D : Dom) : State → State → Prop
  | refl {s : State} : HwRun D s s
  | step {s s₁ t : State} : D.mem s.pc → HwStep s s₁ → HwRun D s₁ t → HwRun D s t

theorem Code.fetch_mem {c : Code} {pc : Word} {w : BitVec 32} (h : c.fetch pc = some w) :
    ∀ k, k < 4 → c.mem (pc + BitVec.ofNat 64 k) := by
  intro k hk
  unfold Code.fetch at h
  dsimp only at h
  split at h
  · rename_i hal
    have hlt : (pc - c.base).toNat / 4 < c.words.size := by
      refine Classical.byContradiction fun hn => ?_
      rw [Array.getElem?_eq_none (by omega)] at h; cases h
    unfold Code.mem
    have e : pc + BitVec.ofNat 64 k - c.base = (pc - c.base) + BitVec.ofNat 64 k := by bv_omega
    rw [e, BitVec.toNat_add]
    have : (BitVec.ofNat 64 k).toNat = k := by simp; omega
    rw [this]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
  · cases h

/-- With the image loaded, the machine fetches what the image says. -/
theorem Code.fetchMem_eq {c : Code} {m : Word → Byte} (hl : c.Loaded m) {pc : Word} {w : BitVec 32}
    (h : c.fetch pc = some w) : fetchMem m pc = w := hl pc w h

theorem Code.loaded_preserved {c : Code} {m m' : Word → Byte} (hl : c.Loaded m)
    (h : ∀ x, c.mem x → m' x = m x) : c.Loaded m' := by
  intro pc w hf
  rw [← hl pc w hf]
  unfold read32
  rw [readLE_congr (m := m') (m' := m) (fun k hk => h _ (Code.fetch_mem hf k hk))]

theorem Step.loaded {c : Code} {P : Perm} {s s' : State} (h : Step c P s s')
    (hp : Protected c P) (hl : c.Loaded s.mem) : c.Loaded s'.mem :=
  Code.loaded_preserved hl fun x hx => h.frame x (fun hw => hp x hw hx)

/-- A machine step from a state where `P` allows a step is a `P`-step. -/
theorem HwStep.toStep {c : Code} {P : Perm} {s s₁ s' : State} (hl : c.Loaded s.mem)
    (hP : Step c P s s₁) (h : HwStep s s') : Step c P s s' := by
  obtain ⟨i, hi, hok, hx⟩ := hP.instrOk
  have hf : ∃ w, c.fetch s.pc = some w ∧ decode w = some i := by
    unfold Code.instr at hi
    cases hfe : c.fetch s.pc with
    | none => rw [hfe] at hi; cases hi
    | some w => rw [hfe] at hi; exact ⟨w, rfl, hi⟩
  obtain ⟨w, hfw, hdw⟩ := hf
  have hm := Code.fetchMem_eq hl hfw
  cases h with
  | exec _ _ hd hxs =>
    rw [hm, hdw] at hd; cases hd; exact .exec hx hi hok hxs
  | sys _ _ hd hy =>
    rw [hm, hdw] at hd; cases hd; exact .sys hx hi hok hy

/-- A `P`-step is a machine step, when the image is 4-byte aligned. -/
theorem Step.toHw {c : Code} {P : Perm} {s s' : State} (hl : c.Loaded s.mem)
    (hb : aligned c.base 4) (h : Step c P s s') : HwStep s s' := by
  have fetch_of {i} (hi : c.instr s.pc = some i) :
      aligned s.pc 4 ∧ decode (fetchMem s.mem s.pc) = some i := by
    unfold Code.instr at hi
    cases hfe : c.fetch s.pc with
    | none => rw [hfe] at hi; cases hi
    | some w =>
      rw [hfe] at hi
      refine ⟨?_, by rw [Code.fetchMem_eq hl hfe]; exact hi⟩
      unfold Code.fetch at hfe
      dsimp only at hfe
      split at hfe
      · rename_i hal
        unfold aligned at *
        have e : s.pc = (s.pc - c.base) + c.base := by bv_omega
        rw [e, BitVec.toNat_add]; omega
      · cases hfe
  cases h with
  | exec hx hi _ hxs => obtain ⟨ha, hd⟩ := fetch_of hi; exact .exec hx ha hd hxs
  | sys hx hi _ hy => obtain ⟨ha, hd⟩ := fetch_of hi; exact .sys hx ha hd hy

section
variable {c : Code} {P : Perm} {D : Dom} {Q : State → Prop}

/-- Every state a machine execution reaches inside `D` still satisfies `Exec`. -/
theorem Exec.hw_run {s t : State} (h : Exec c P D Q s) (hl : c.Loaded s.mem)
    (hp : Protected c P) (hr : HwRun D s t) : Exec c P D Q t ∧ c.Loaded t.mem := by
  induction hr with
  | refl => exact ⟨h, hl⟩
  | step hd hs _ ih =>
    cases h with
    | done hq =>
      rcases hq.1 with hn | hn
      · exact absurd hd hn
      · cases hs <;> contradiction
    | step _ hex hall =>
      obtain ⟨s₁, h₁⟩ := hex
      have hstep := hs.toStep hl h₁
      exact ih (hall _ hstep) (hstep.loaded hp hl)

/-- No fault and memory safety: inside `D`, the machine can always step, and
    every step it can take is one `P` allows. -/
theorem Exec.hw_safe {s t : State} (h : Exec c P D Q s) (hl : c.Loaded s.mem)
    (hp : Protected c P) (hb : aligned c.base 4) (hr : HwRun D s t) (hd : D.mem t.pc)
    (hx : t.exit = none) :
    (∃ t', HwStep t t') ∧ ∀ t', HwStep t t' → Step c P t t' := by
  obtain ⟨ht, hlt⟩ := h.hw_run hl hp hr
  cases ht with
  | done hq =>
    rcases hq.1 with hn | hn
    · exact absurd hd hn
    · exact absurd hx hn
  | step _ hex _ =>
    obtain ⟨t₁, h₁⟩ := hex
    exact ⟨⟨t₁, h₁.toHw hlt hb⟩, fun t' h' => h'.toStep hlt h₁⟩

/-- Leaving `D` (returning) or exiting, the postcondition holds. -/
theorem Exec.hw_final {s t : State} (h : Exec c P D Q s) (hl : c.Loaded s.mem)
    (hp : Protected c P) (hr : HwRun D s t) (hf : Final D t) : Q t := by
  obtain ⟨ht, _⟩ := h.hw_run hl hp hr
  cases ht with
  | done hq => exact hq.2
  | step hd hex _ =>
    obtain ⟨_, h₁⟩ := hex
    obtain ⟨_, _, _, hx⟩ := h₁.instrOk
    rcases hf with hn | hn
    · exact absurd hd hn
    · exact absurd hx hn

/-- Termination: no machine execution stays in `D` forever. -/
theorem Exec.hw_terminates {s : State} (h : Exec c P D Q s) (hl : c.Loaded s.mem)
    (hp : Protected c P) :
    ¬ ∃ f : Nat → State, f 0 = s ∧ ∀ n, D.mem (f n).pc ∧ HwStep (f n) (f (n + 1)) := by
  rintro ⟨f, hf0, hf⟩
  suffices ∀ u, Exec c P D Q u → ∀ k, f k = u → c.Loaded u.mem → False from
    this s h 0 hf0 hl
  intro u hu
  induction hu with
  | done hq =>
    intro k hk _
    obtain ⟨hd, hs⟩ := hf k
    rw [hk] at hd hs
    rcases hq.1 with hn | hn
    · exact hn hd
    · cases hs <;> contradiction
  | step _ hex _ ih =>
    intro k hk hl'
    obtain ⟨_, h₁⟩ := hex
    obtain ⟨_, hs⟩ := hf k
    rw [hk] at hs
    have hstep := hs.toStep hl' h₁
    exact ih _ hstep (k + 1) rfl (hstep.loaded hp hl')

end

end NoCompiler
