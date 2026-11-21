import NoCompiler.Linux.Prot
import NoCompiler.Step
import NoCompiler.Spec

/-
The whole process: the machine (the trusted `exec`, NoCompiler/Machine.lean)
and the Linux layer for `ecall` (Linux/Prot.lean), over `State × Kern`.

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

/-- What the process may touch: the mapped ranges, read-write except where an
    overlay says read-only (`Kern.ro`, kept inside the mapped ranges) or no
    access (`Kern.noacc`). A load outside the readable ranges, a store outside
    the writable ones, or a `read`/`write` buffer outside them, faults: the
    process has no step. -/
def Kern.perm (k : Kern) : Perm :=
  { rd := (cutAll (interAll k.maps k.ro) k.noacc).map fun p => ⟨p.1, p.2⟩,
    wr := (cutAll (cutAll k.maps k.ro) k.noacc).map fun p => ⟨p.1, p.2⟩ }

theorem cutAll_nil (l : List (Word × Nat)) : cutAll l [] = l := rfl

/-- With no overlays, every mapped range is read-write (the permission before
    protections were modelled). -/
theorem Kern.perm_plain (k : Kern) (hro : k.ro = []) (hna : k.noacc = []) :
    k.perm = { rd := [], wr := k.maps.map fun p => ⟨p.1, p.2⟩ } := by
  simp [Kern.perm, hro, hna, cutAll_nil, interAll]

inductive PStep (c : Code) : State × Kern → State × Kern → Prop
  | exec {s s' : State} {k : Kern} {i : Instr} :
      s.exit = none → c.instr s.pc = some i → InstrOk k.perm i s → exec i s = some s' →
      PStep c (s, k) (s', k)
  | sys {s s' : State} {k k' : Kern} :
      s.exit = none → c.instr s.pc = some .ecall → SysOk k.perm s → ProcStep7 (s, k) (s', k') →
      PStep c (s, k) (s', k')

theorem PStep.step {c : Code} {s s' : State} {k k' : Kern} (h : PStep c (s, k) (s', k'))
    (hold : c.instr s.pc = some .ecall → OldSys s) : Step c k.perm s s' := by
  cases h with
  | exec hx hi hok he => exact .exec hx hi hok he
  | sys hx hi hok hp =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := (hold hi).ne
    obtain ⟨hr, hl⟩ := (hold hi).ne6
    exact .sys hx hi hok (ProcStep7.sys hp (hold hi).ne7 hr hl h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)

/-- A `Sys` transition is an outcome of the basic spec. -/
theorem outcome_of_sys {s s' : State} (h : Sys s s') : ∃ o, spec (SyscallInput.of s) o ∧ o.apply s = s' := by
  obtain ⟨hs⟩ := basic_iff_sys.2 h
  exact ⟨_, hs, rfl⟩

theorem PStep.progress {c : Code} {s s₁ : State} (k : Kern) (h : Step c k.perm s s₁)
    (hold : c.instr s.pc = some .ecall → OldSys s) : ∃ s' k', PStep c (s, k) (s', k') := by
  cases h with
  | exec hx hi hok he => exact ⟨_, _, .exec hx hi hok he⟩
  | sys hx hi hok hy =>
    obtain ⟨o, k', h⟩ := procSpec7_exists k (hold hi) hy
    exact ⟨_, k', .sys hx hi hok (ProcStep7.step h)⟩

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

/-- At an instruction or an `OldSys` call, the mapped ranges and their
    protections do not change (a file read moves its offset only), so neither
    does the permission. -/
theorem PStep.mem_eq {c : Code} {s s' : State} {k k' : Kern} (h : PStep c (s, k) (s', k'))
    (hold : c.instr s.pc = some .ecall → OldSys s) : k'.maps = k.maps ∧ k'.ro = k.ro ∧ k'.noacc = k.noacc := by
  cases h with
  | exec => exact ⟨rfl, rfl, rfl⟩
  | sys _ hi _ hp => exact ProcStep7.mem_old hp (hold hi)

theorem PStep.perm_eq {c : Code} {s s' : State} {k k' : Kern} (h : PStep c (s, k) (s', k'))
    (hold : c.instr s.pc = some .ecall → OldSys s) : k'.perm = k.perm := by
  obtain ⟨h1, h2, h3⟩ := PStep.mem_eq h hold
  simp only [Kern.perm, h1, h2, h3]

/-- What is proved of the trusted `Step` holds of the process: a safe run to
    `Q` under the process's permission is a safe process run to `Q`. (A trusted
    run only ever makes the four syscalls `Sys` has, which leave the mapped
    ranges alone.) -/
theorem PReach.of_reach' {c : Code} {D : Dom} {Q : State → Prop} {P : Perm} {s : State}
    (h : Reach c P D Q s) : ∀ k : Kern, k.perm = P → PReach c D Q (s, k) := by
  induction h with
  | done hq => exact fun _ _ => .done hq
  | step hd hex _ ih =>
    intro k hk
    subst hk
    obtain ⟨s₁, st⟩ := hex
    have hold := oldSys_of_step st
    refine .step hd (PStep.progress k st hold) (fun s' k' hp => ?_)
    have he := PStep.perm_eq hp hold
    exact ih s' (PStep.step hp hold) k' he

theorem PReach.of_reach {c : Code} {D : Dom} {Q : State → Prop} {s : State} {k : Kern}
    (h : Reach c k.perm D Q s) : PReach c D Q (s, k) :=
  PReach.of_reach' h k rfl

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
    · simp [Kern.perm, Kern.init, cutAll, interAll] at hr
  | sys _ hi' _ _ => rw [hi] at hi'; cases hi'

/-- One page at 0x1000 mapped read-only (`mmap` with PROT_READ, or `mprotect`). -/
def kRo : Kern := { Kern.init with maps := [(0x1000, 4096)], ro := [(0x1000, 4096)] }

/-- The same page with no access (PROT_NONE). -/
def kNone : Kern := { Kern.init with maps := [(0x1000, 4096)], noacc := [(0x1000, 4096)] }

/-- Control: a store to a read-only page faults: `sd a0, 0(a1)` with a1 in it
    has no process step. -/
theorem store_readonly_faults (s : State) (hpc : s.pc = 0x2000#64) (ha : s.reg 11 = 0x1000#64) :
    let c : Code := ⟨0x2000#64, #[0x00a5b023#32]⟩
    ¬ ∃ s' k', PStep c (s, kRo) (s', k') := by
  intro c
  have hi : c.instr s.pc = some (.store .sd 11 10 0) := by rw [hpc]; decide
  have hw : kRo.perm.wr = [] := by decide
  rintro ⟨s', k', h⟩
  cases h with
  | exec _ hi' hok _ =>
    rw [hi] at hi'; cases hi'
    rcases hok with h0 | ⟨r, hr, _⟩
    · simp [StOp.width] at h0
    · rw [hw] at hr; exact List.not_mem_nil hr
  | sys _ hi' _ _ => rw [hi] at hi'; cases hi'

/-- And a load from it is allowed: the readable ranges hold the page. -/
theorem readonly_readable : kRo.perm.rd.map (fun r => (r.base, r.size)) = [(0x1000, 4096)] := by decide

/-- Control: a load from a PROT_NONE page faults. -/
theorem load_none_faults (s : State) (hpc : s.pc = 0x2000#64) :
    let c : Code := ⟨0x2000#64, #[0x0005b503#32]⟩
    ¬ ∃ s' k', PStep c (s, kNone) (s', k') := by
  intro c
  have hi : c.instr s.pc = some (.load .ld 10 11 0) := by rw [hpc]; decide
  have hr0 : kNone.perm.rd = [] ∧ kNone.perm.wr = [] := by decide
  rintro ⟨s', k', h⟩
  cases h with
  | exec _ hi' hok _ =>
    rw [hi] at hi'; cases hi'
    rcases hok with h0 | ⟨r, hr, _⟩
    · simp [LdOp.width] at h0
    · rw [hr0.1, hr0.2] at hr; exact List.not_mem_nil hr
  | sys _ hi' _ _ => rw [hi] at hi'; cases hi'

end NoCompiler.Linux
