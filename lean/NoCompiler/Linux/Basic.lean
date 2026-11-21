import NoCompiler.Linux.Effect

/-
The Linux layer's first syscalls: `read` (63), `write` (64), `exit` (93) and
`exit_group` (94), as LPS models a syscall (theories/LinuxProcessSem/
Sys/SyscallTable.v): a specification per syscall number that says which
outcomes (`Outcome`, Linux/Effect.lean) the kernel may give for an input,
and one step relation over all of them.

`basic_iff_sys`: this layer, for these four syscalls, admits exactly the
transitions of the trusted environment model `Sys` (Env.lean). So every
proof about `Sys` is a proof about this layer, and the next steps (an fd
table, the process start state, brk/mmap; docs/design/prior-art-lps.md)
extend it without changing what is already proved.

What these four do not model yet, and LPS does: file descriptors (here, as in
`Sys`, any fd may be written or read), EFAULT for unmapped buffers (our
memory is total), and which errno a failure returns (here any 1..4095, as in
`Sys`).
-/
namespace NoCompiler.Linux

/-- `write(fd, buf, n)`: `r` bytes accepted, `0 ≤ r ≤ min n MAX_RW_COUNT`,
    `r ≥ 1` when `n ≥ 1`, the event `write fd (first r bytes)`; or an error. -/
def writeSpec (i : SyscallInput) : Outcome → Prop
  | .ret e ev => e.writes = [] ∧ e.zeros = [] ∧
    ((∃ r : Nat, r ≤ (i.arg 2).toNat ∧ r ≤ maxRW ∧ (0 < (i.arg 2).toNat → 0 < r) ∧
        e.ret = BitVec.ofNat 64 r ∧ ev = some (.write (i.arg 0) (readBytes i.mem (i.arg 1) r))) ∨
      (∃ n : Nat, 1 ≤ n ∧ n ≤ 4095 ∧ e.ret = -(BitVec.ofNat 64 n) ∧ ev = none))
  | .exit _ => False

/-- `read(fd, buf, n)`: any bytes `ds`, `|ds| ≤ min n MAX_RW_COUNT`, stored at
    `buf`, the event `read fd ds`; or an error. -/
def readSpec (i : SyscallInput) : Outcome → Prop
  | .ret e ev => e.zeros = [] ∧
    ((∃ ds : List Byte, ds.length ≤ (i.arg 2).toNat ∧ ds.length ≤ maxRW ∧
        e.writes = [(i.arg 1, ds)] ∧ e.ret = BitVec.ofNat 64 ds.length ∧
        ev = some (.read (i.arg 0) ds)) ∨
      (∃ n : Nat, 1 ≤ n ∧ n ≤ 4095 ∧ e.writes = [] ∧ e.ret = -(BitVec.ofNat 64 n) ∧ ev = none))
  | .exit _ => False

/-- `exit(code)`, `exit_group(code)`: the process ends with status a0. -/
def exitSpec (i : SyscallInput) : Outcome → Prop
  | .exit c => c = i.arg 0
  | .ret .. => False

/-- The modelled surface, by syscall number (LPS `spec_table`). A number not
    listed has no outcome: the process cannot step. -/
def spec (i : SyscallInput) (o : Outcome) : Prop :=
  if i.sysno = sysRead then readSpec i o
  else if i.sysno = sysWrite then writeSpec i o
  else if i.sysno = sysExit ∨ i.sysno = sysExitGroup then exitSpec i o
  else False

/-- An `ecall` at `s` under this layer: some outcome the spec allows, applied. -/
inductive Basic : State → State → Prop
  | step {s : State} {o : Outcome} : spec (SyscallInput.of s) o → Basic s (o.apply s)

theorem basic_iff_sys {s s' : State} : Basic s s' ↔ Sys s s' := by
  have hno : (SyscallInput.of s).sysno = s.reg Reg.a7 := rfl
  have hr : sysRead ≠ sysWrite := by decide
  constructor
  · rintro ⟨h⟩
    rename_i o
    simp only [spec, hno] at h
    by_cases h63 : s.reg Reg.a7 = sysRead
    · simp only [h63, ↓reduceIte] at h
      cases o with
      | exit _ => exact h.elim
      | ret e ev =>
        obtain ⟨hz, ⟨ds, h1, h2, hw, he, hev⟩ | ⟨n, h1, h2, hw, he, hev⟩⟩ := h
        · subst hev
          have hm : e.mem s.mem = writeBytes s.mem (s.reg Reg.a1) ds := by
            simp only [Effect.mem, hz, hw, applyZeros, applyWrites]; rfl
          simp only [Outcome.apply, hm, he]
          exact Sys.readOk ds h63 h1 h2
        · subst hev
          have hm : e.mem s.mem = s.mem := by simp only [Effect.mem, hz, hw, applyZeros, applyWrites]
          simp only [Outcome.apply, hm, he]
          exact Sys.readErr n h63 h1 h2
    simp only [h63, ↓reduceIte] at h
    by_cases h64 : s.reg Reg.a7 = sysWrite
    · simp only [h64, ↓reduceIte] at h
      cases o with
      | exit _ => exact h.elim
      | ret e ev =>
        obtain ⟨hw, hz, ⟨r, h1, h2, h3, he, hev⟩ | ⟨n, h1, h2, he, hev⟩⟩ := h
        · subst hev
          have hm : e.mem s.mem = s.mem := by simp only [Effect.mem, hz, hw, applyZeros, applyWrites]
          simp only [Outcome.apply, hm, he]
          exact Sys.writeOk r h64 h1 h2 h3
        · subst hev
          have hm : e.mem s.mem = s.mem := by simp only [Effect.mem, hz, hw, applyZeros, applyWrites]
          simp only [Outcome.apply, hm, he]
          exact Sys.writeErr n h64 h1 h2
    simp only [h64, ↓reduceIte] at h
    by_cases hex : s.reg Reg.a7 = sysExit ∨ s.reg Reg.a7 = sysExitGroup
    · simp only [hex, ↓reduceIte] at h
      cases o with
      | ret _ _ => exact h.elim
      | exit c =>
        simp only [exitSpec, SyscallInput.arg] at h
        subst h
        exact Sys.exit hex
    · simp only [hex, ↓reduceIte] at h
  · intro h
    cases h with
    | writeOk r ha h1 h2 h3 =>
      refine Basic.step (o := .ret { ret := BitVec.ofNat 64 r }
        (some (.write (s.reg Reg.a0) (readBytes s.mem (s.reg Reg.a1) r)))) ?_
      simp only [spec, hno, ha, Ne.symm hr, ↓reduceIte]
      exact ⟨rfl, rfl, .inl ⟨r, h1, h2, h3, rfl, rfl⟩⟩
    | writeErr n ha h1 h2 =>
      refine Basic.step (o := .ret { ret := -(BitVec.ofNat 64 n) } none) ?_
      simp only [spec, hno, ha, Ne.symm hr, ↓reduceIte]
      exact ⟨rfl, rfl, .inr ⟨n, h1, h2, rfl, rfl⟩⟩
    | readOk ds ha h1 h2 =>
      refine Basic.step (o := .ret { ret := BitVec.ofNat 64 ds.length, writes := [(s.reg Reg.a1, ds)] }
        (some (.read (s.reg Reg.a0) ds))) ?_
      simp only [spec, hno, ha, ↓reduceIte]
      exact ⟨rfl, .inl ⟨ds, h1, h2, rfl, rfl, rfl⟩⟩
    | readErr n ha h1 h2 =>
      refine Basic.step (o := .ret { ret := -(BitVec.ofNat 64 n) } none) ?_
      simp only [spec, hno, ha, ↓reduceIte]
      exact ⟨rfl, .inr ⟨n, h1, h2, rfl, rfl, rfl⟩⟩
    | exit hx =>
      have h1 : s.reg Reg.a7 ≠ sysRead := by rcases hx with h | h <;> rw [h] <;> decide
      have h2 : s.reg Reg.a7 ≠ sysWrite := by rcases hx with h | h <;> rw [h] <;> decide
      refine Basic.step (o := .exit (s.reg Reg.a0)) ?_
      simp only [spec, hno, h1, h2, hx, ↓reduceIte]
      rfl

/-- Control: a syscall outside the table (here `close`, 57) has no outcome, so
    the process cannot step: the layer claims nothing about it. -/
theorem no_step_unmodeled {s s' : State} (h : s.reg Reg.a7 = 57) : ¬ Basic s s' := by
  rintro ⟨hs⟩
  have hno : (SyscallInput.of s).sysno = 57 := h
  have h1 : (57 : Word) ≠ sysRead := by decide
  have h2 : (57 : Word) ≠ sysWrite := by decide
  have h3 : ¬ ((57 : Word) = sysExit ∨ (57 : Word) = sysExitGroup) := by decide
  simp only [spec, hno, h1, h2, h3, ↓reduceIte] at hs

end NoCompiler.Linux
