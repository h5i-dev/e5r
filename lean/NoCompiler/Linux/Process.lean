import NoCompiler.Linux.Startup
import NoCompiler.Step

/-
The whole process: the machine (the trusted `exec`, NoCompiler/Machine.lean)
and the Linux layer for `ecall` (Linux/Startup.lean), over `State × Kern`.

* `PStep.step`: at an instruction other than `ecall`, and at an `ecall` of a
  syscall the trusted model has (read, write, exit, exit_group), a process
  step is a step of the trusted `Step c Perm.top`. So what is proved of
  `Step` holds of the process.
* `PStep.progress`: wherever `Step c Perm.top` can move (and the `ecall`, if
  any, is one of those four), the process can move too. The process layer
  never loses a step there: on a closed fd it answers EBADF. So `Reach`'s
  progress obligations carry over too.
-/
namespace NoCompiler.Linux

/-- The trusted model's syscalls. -/
def OldSys (s : State) : Prop :=
  s.reg Reg.a7 = sysRead ∨ s.reg Reg.a7 = sysWrite ∨ s.reg Reg.a7 = sysExit ∨ s.reg Reg.a7 = sysExitGroup

inductive PStep (c : Code) : State × Kern → State × Kern → Prop
  | exec {s s' : State} {k : Kern} {i : Instr} :
      s.exit = none → c.instr s.pc = some i → InstrOk Perm.top i s → exec i s = some s' →
      PStep c (s, k) (s', k)
  | sys {s s' : State} {k k' : Kern} :
      s.exit = none → c.instr s.pc = some .ecall → SysOk Perm.top s → ProcStep4 (s, k) (s', k') →
      PStep c (s, k) (s', k')

theorem OldSys.ne {s : State} (h : OldSys s) :
    s.reg Reg.a7 ≠ sysClose ∧ s.reg Reg.a7 ≠ sysBrk ∧ s.reg Reg.a7 ≠ sysMmap ∧
    s.reg Reg.a7 ≠ sysMunmap ∧ s.reg Reg.a7 ≠ sysWritev ∧ s.reg Reg.a7 ≠ sysSetTidAddress ∧
    s.reg Reg.a7 ≠ sysRtSigprocmask ∧ s.reg Reg.a7 ≠ sysIoctl := by
  rcases h with h | h | h | h <;> rw [h] <;> decide

theorem PStep.step {c : Code} {s s' : State} {k k' : Kern} (h : PStep c (s, k) (s', k'))
    (hold : c.instr s.pc = some .ecall → OldSys s) : Step c Perm.top s s' := by
  cases h with
  | exec hx hi hok he => exact .exec hx hi hok he
  | sys hx hi hok hp =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := (hold hi).ne
    exact .sys hx hi hok (ProcStep4.sys hp h1 h2 h3 h4 h5 h6 h7 h8)

/-- A `Sys` transition is an outcome of the basic spec. -/
theorem outcome_of_sys {s s' : State} (h : Sys s s') : ∃ o, spec (SyscallInput.of s) o ∧ o.apply s = s' := by
  obtain ⟨hs⟩ := basic_iff_sys.2 h
  exact ⟨_, hs, rfl⟩

theorem PStep.progress {c : Code} {s s₁ : State} (k : Kern) (h : Step c Perm.top s s₁)
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

/-- What is proved of the trusted `Step` holds of the process: a safe run to
    `Q` under `Perm.top` is a safe process run to `Q`, from any kernel state,
    when every `ecall` in the code is one of the trusted model's syscalls. -/
theorem PReach.of_reach {c : Code} {D : Dom} {Q : State → Prop}
    (hold : ∀ u : State, c.instr u.pc = some .ecall → OldSys u) {s : State}
    (h : Reach c Perm.top D Q s) (k : Kern) : PReach c D Q (s, k) := by
  induction h generalizing k with
  | done hq => exact .done hq
  | step hd hex _ ih =>
    obtain ⟨s₁, st⟩ := hex
    exact .step hd (PStep.progress k st (hold _)) (fun s' k' hp => ih s' (PStep.step hp (hold _)) k')

end NoCompiler.Linux
