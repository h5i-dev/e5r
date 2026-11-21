import NoCompiler.Linux.Startup
import NoCompiler.Step
import NoCompiler.Spec

/-
The whole process: the machine (the trusted `exec`, NoCompiler/Machine.lean)
and the Linux layer for `ecall` (Linux/Startup.lean), over `State × Kern`.

* Accesses: a load or store, or a `read`/`write` buffer, must lie in the
  mapped ranges (`Kern.perm`, from `Kern.maps`); outside them the process has
  no step: it faults (decision 2026-11-21, Q5 (a): a layer over the trusted
  `Step`, which is unchanged).
* `PStep.step`: at an instruction other than `ecall`, and at an `ecall` of a
  syscall the trusted model has (read, write, exit, exit_group), a process
  step is a step of the trusted `Step c k.perm`. So what is proved of
  `Step` holds of the process.
* `PStep.progress`: wherever `Step c k.perm` can move (and the `ecall`, if
  any, is one of those four), the process can move too. The process layer
  never loses a step there: on a closed fd it answers EBADF. So `Reach`'s
  progress obligations carry over too.
-/
namespace NoCompiler.Linux

/-- The trusted model's syscalls. -/
def OldSys (s : State) : Prop :=
  s.reg Reg.a7 = sysRead ∨ s.reg Reg.a7 = sysWrite ∨ s.reg Reg.a7 = sysExit ∨ s.reg Reg.a7 = sysExitGroup

/-- What the process may touch: every mapped range, read and write (the
    protection bits are not modelled). A load or store outside it, or a
    `read`/`write` buffer outside it, faults: the process has no step. -/
def Kern.perm (k : Kern) : Perm := { rd := [], wr := k.maps.map fun p => ⟨p.1, p.2⟩ }

inductive PStep (c : Code) : State × Kern → State × Kern → Prop
  | exec {s s' : State} {k : Kern} {i : Instr} :
      s.exit = none → c.instr s.pc = some i → InstrOk k.perm i s → exec i s = some s' →
      PStep c (s, k) (s', k)
  | sys {s s' : State} {k k' : Kern} :
      s.exit = none → c.instr s.pc = some .ecall → SysOk k.perm s → ProcStep4 (s, k) (s', k') →
      PStep c (s, k) (s', k')

theorem OldSys.ne {s : State} (h : OldSys s) :
    s.reg Reg.a7 ≠ sysClose ∧ s.reg Reg.a7 ≠ sysBrk ∧ s.reg Reg.a7 ≠ sysMmap ∧
    s.reg Reg.a7 ≠ sysMunmap ∧ s.reg Reg.a7 ≠ sysWritev ∧ s.reg Reg.a7 ≠ sysSetTidAddress ∧
    s.reg Reg.a7 ≠ sysRtSigprocmask ∧ s.reg Reg.a7 ≠ sysIoctl := by
  rcases h with h | h | h | h <;> rw [h] <;> decide

theorem PStep.step {c : Code} {s s' : State} {k k' : Kern} (h : PStep c (s, k) (s', k'))
    (hold : c.instr s.pc = some .ecall → OldSys s) : Step c k.perm s s' := by
  cases h with
  | exec hx hi hok he => exact .exec hx hi hok he
  | sys hx hi hok hp =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := (hold hi).ne
    exact .sys hx hi hok (ProcStep4.sys hp h1 h2 h3 h4 h5 h6 h7 h8)

/-- A `Sys` transition is an outcome of the basic spec. -/
theorem outcome_of_sys {s s' : State} (h : Sys s s') : ∃ o, spec (SyscallInput.of s) o ∧ o.apply s = s' := by
  obtain ⟨hs⟩ := basic_iff_sys.2 h
  exact ⟨_, hs, rfl⟩

theorem PStep.progress {c : Code} {s s₁ : State} (k : Kern) (h : Step c k.perm s s₁)
    (hold : c.instr s.pc = some .ecall → OldSys s) : ∃ s' k', PStep c (s, k) (s', k') := by
  cases h with
  | exec hx hi hok he => exact ⟨_, _, .exec hx hi hok he⟩
  | sys hx hi hok hy =>
    have ho := hold hi
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ho.ne
    have hno : (SyscallInput.of s).sysno = s.reg Reg.a7 := rfl
    obtain ⟨o, hspec, -⟩ := outcome_of_sys hy
    -- The fd layer's outcome: the basic one on an open fd, EBADF on a closed one.
    have : ∃ o' k', fdSpec k (SyscallInput.of s) o' k' := by
      unfold fdSpec
      by_cases hrw : (SyscallInput.of s).sysno = sysRead ∨ (SyscallInput.of s).sysno = sysWrite
      · simp only [hrw, ↓reduceIte]
        by_cases hfd : (SyscallInput.of s).arg 0 ∈ k.fds
        · exact ⟨o, k, by simp only [hfd, ↓reduceIte]; exact ⟨hspec, trivial⟩⟩
        · exact ⟨_, k, by simp only [hfd, ↓reduceIte]; exact ⟨rfl, trivial⟩⟩
      · have hcl : ¬ (SyscallInput.of s).sysno = sysClose := by rw [hno]; exact h1
        simp only [hrw, hcl, ↓reduceIte]
        exact ⟨o, k, hspec, rfl⟩
    obtain ⟨o', k', hfd⟩ := this
    refine ⟨_, k', .sys hx hi hok (ProcStep4.step (o := o') ?_)⟩
    simp only [procSpec4, procSpec3, procSpec2, procSpec, hno, h2, h3, h4, h5, h6, h7, h8, ↓reduceIte]
    exact hfd

/-- The process reaches `Q` safely inside `D`: like `Reach`, over the process
    step. -/
inductive PReach (c : Code) (D : Dom) (Q : State → Prop) : State × Kern → Prop
  | done {s : State} {k : Kern} : Q s → PReach c D Q (s, k)
  | step {s : State} {k : Kern} :
      D.mem s.pc → (∃ s' k', PStep c (s, k) (s', k')) →
      (∀ s' k', PStep c (s, k) (s', k') → PReach c D Q (s', k')) → PReach c D Q (s, k)

/-- A trusted step at an `ecall` is one of the four syscalls: `Sys` has no other. -/
theorem oldSys_of_step {c : Code} {P : Perm} {s s₁ : State} (h : Step c P s s₁)
    (hi : c.instr s.pc = some .ecall) : OldSys s := by
  cases h with
  | exec _ hi' _ hx => rw [hi] at hi'; cases hi'; simp [exec_ecall] at hx
  | sys _ _ _ hy =>
    cases hy with
    | writeOk _ h => exact .inr (.inl h)
    | writeErr _ h => exact .inr (.inl h)
    | readOk _ h => exact .inl h
    | readErr _ h => exact .inl h
    | exit h => rcases h with h | h
                · exact .inr (.inr (.inl h))
                · exact .inr (.inr (.inr h))

/-- At an instruction or an `OldSys` call, the kernel state does not change. -/
theorem PStep.kern_eq {c : Code} {s s' : State} {k k' : Kern} (h : PStep c (s, k) (s', k'))
    (hold : c.instr s.pc = some .ecall → OldSys s) : k' = k := by
  cases h with
  | exec => rfl
  | sys _ hi _ hp =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := (hold hi).ne
    cases hp with
    | step hs =>
      have hno : (SyscallInput.of s).sysno = s.reg Reg.a7 := rfl
      simp only [procSpec4, procSpec3, procSpec2, procSpec, hno, h2, h3, h4, h5, h6, h7, h8,
        ↓reduceIte] at hs
      unfold fdSpec at hs
      simp only [hno, h1, ↓reduceIte] at hs
      split at hs
      · split at hs
        · exact hs.2
        · exact hs.2
      · exact hs.2

/-- What is proved of the trusted `Step` holds of the process: a safe run to
    `Q` under the process's permission is a safe process run to `Q`. (A trusted
    run only ever makes the four syscalls `Sys` has, which leave the mapped
    ranges alone.) -/
theorem PReach.of_reach {c : Code} {D : Dom} {Q : State → Prop} {s : State} {k : Kern}
    (h : Reach c k.perm D Q s) : PReach c D Q (s, k) := by
  induction h with
  | done hq => exact .done hq
  | step hd hex _ ih =>
    obtain ⟨s₁, st⟩ := hex
    have hold := oldSys_of_step st
    refine .step hd (PStep.progress k st hold) (fun s' k' hp => ?_)
    have hk := PStep.kern_eq hp hold
    subst hk
    exact ih s' (PStep.step hp hold)

/-- A safe run under `P` is a safe run under any larger permission: the
    transitions are the same, only their side conditions get weaker. -/
theorem Reach.widen {c : Code} {P P' : Perm} {D : Dom} {Q : State → Prop} {s : State}
    (hle : P.le P') (h : Reach c P D Q s) : Reach c P' D Q s := by
  induction h with
  | done hq => exact .done hq
  | step hd hex _ ih =>
    obtain ⟨s₁, st⟩ := hex
    exact .step hd ⟨s₁, Step.mono hle st⟩ (fun s' st' => ih s' (Step.restrict st st'))

/-- A spec whose permission lies inside the mapped ranges: its proof is a
    proof about the process. -/
theorem PReach.of_reach_le {c : Code} {D : Dom} {Q : State → Prop} {s : State} {k : Kern} {P : Perm}
    (hle : P.le k.perm) (h : Reach c P D Q s) : PReach c D Q (s, k) :=
  PReach.of_reach (Reach.widen hle h)

/-- Control: with nothing mapped, a load faults: `ld a0, 0(a1)` has no
    process step. -/
theorem load_unmapped_faults (s : State) (hpc : s.pc = 0x1000#64) :
    let c : Code := ⟨0x1000#64, #[0x0005b503#32]⟩
    ¬ ∃ s' k', PStep c (s, Kern.init) (s', k') := by
  intro c
  have hi : c.instr s.pc = some (.load .ld 10 11 0) := by rw [hpc]; decide
  rintro ⟨s', k', h⟩
  cases h with
  | exec _ hi' hok _ =>
    rw [hi] at hi'; cases hi'
    rcases hok with h0 | ⟨r, hr, _⟩
    · simp [LdOp.width] at h0
    · simp [Kern.perm, Kern.init] at hr
  | sys _ hi' _ _ => rw [hi] at hi'; cases hi'

end NoCompiler.Linux
