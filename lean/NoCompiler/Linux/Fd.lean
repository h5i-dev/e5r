import NoCompiler.Linux.Basic

/-
The Linux layer, second step: a file-descriptor table (LPS `FdState`,
theories/LinuxProcessSem/State.v#L3591, there an association list of entries;
here, for now, the set of open descriptor numbers).

* `read`/`write` on an open fd behave as in Linux/Basic.lean; on a closed fd
  the only outcome is EBADF (-9), as Linux's `fdget` failure
  (fs/read_write.c, ksys_read/ksys_write, v6.18.46).
* `close(fd)` (57): 0 and the fd removed if it is open, EBADF otherwise
  (fs/open.c, close_fd). It is the first syscall beyond the trusted `Sys`.
* A process starts with 0, 1, 2 open (`Kern.init`).

`FdStep.sys`: every step of this layer at a syscall other than `close` is a
step of `Sys` (Env.lean), so it only removes behaviours there, and every
proof about `Sys` covers it.
-/
namespace NoCompiler.Linux

/-- The kernel's state of the process, so far: its open descriptors. -/
structure Kern where
  fds : List Word
  /-- The program break's start and current value (Linux/Brk.lean); 0 until the loader sets them. -/
  startBrk : Word := 0
  brk : Word := 0

def Kern.init : Kern := { fds := [0, 1, 2] }

def sysClose : Word := 57

/-- EBADF, as a return value. -/
def ebadf : Word := -(BitVec.ofNat 64 9)

/-- The outcomes and next kernel state the layer allows for an input. -/
def fdSpec (k : Kern) (i : SyscallInput) (o : Outcome) (k' : Kern) : Prop :=
  if i.sysno = sysRead ∨ i.sysno = sysWrite then
    if i.arg 0 ∈ k.fds then spec i o ∧ k' = k
    else o = .ret { ret := ebadf } none ∧ k' = k
  else if i.sysno = sysClose then
    if i.arg 0 ∈ k.fds then o = .ret { ret := 0 } none ∧ k' = { k with fds := k.fds.erase (i.arg 0) }
    else o = .ret { ret := ebadf } none ∧ k' = k
  else spec i o ∧ k' = k

/-- An `ecall` with the fd table. -/
inductive FdStep : State × Kern → State × Kern → Prop
  | step {s : State} {k k' : Kern} {o : Outcome} :
      fdSpec k (SyscallInput.of s) o k' → FdStep (s, k) (o.apply s, k')

theorem FdStep.sys {s s' : State} {k k' : Kern} (h : FdStep (s, k) (s', k'))
    (hc : s.reg Reg.a7 ≠ sysClose) : Sys s s' := by
  cases h with
  | step h =>
    rename_i o
    have hno : (SyscallInput.of s).sysno = s.reg Reg.a7 := rfl
    have hbasic : spec (SyscallInput.of s) o → Sys s (o.apply s) :=
      fun h => basic_iff_sys.1 (Basic.step h)
    simp only [fdSpec, hno, hc, ↓reduceIte] at h
    by_cases hrw : s.reg Reg.a7 = sysRead ∨ s.reg Reg.a7 = sysWrite
    · simp only [hrw, ↓reduceIte] at h
      by_cases hfd : (SyscallInput.of s).arg 0 ∈ k.fds
      · simp only [hfd, ↓reduceIte] at h
        exact hbasic h.1
      · simp only [hfd, ↓reduceIte] at h
        obtain ⟨rfl, -⟩ := h
        show Sys s ((s.sysRet ebadf).setMem s.mem)
        rcases hrw with hr | hw
        · exact Sys.readErr 9 hr (by decide) (by decide)
        · exact Sys.writeErr 9 hw (by decide) (by decide)
    · simp only [hrw, ↓reduceIte] at h
      exact hbasic h.1

/-- Control: in a fresh process, writing to fd 5 can only fail with EBADF. -/
theorem write_closed_fd {s : State} {o : Outcome} {k' : Kern} (hw : s.reg Reg.a7 = sysWrite)
    (h5 : s.reg 10 = 5) (h : fdSpec Kern.init (SyscallInput.of s) o k') :
    o = .ret { ret := ebadf } none := by
  have hno : (SyscallInput.of s).sysno = s.reg Reg.a7 := rfl
  have ha : (SyscallInput.of s).arg 0 = 5 := h5
  have hn : (5 : Word) ∉ Kern.init.fds := by decide
  simp only [fdSpec, hno, hw, ha, hn, or_true, ↓reduceIte] at h
  exact h.1

/-- Control: after `close(1)`, fd 1 is no longer open. -/
example : (1 : Word) ∉ (Kern.init.fds.erase 1) := by decide

end NoCompiler.Linux
