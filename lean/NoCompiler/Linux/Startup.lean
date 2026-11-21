import NoCompiler.Linux.Writev

/-
The Linux layer: the other calls a static musl program makes around `main`
(musl src/env/__init_tls.c, __libc_start_main; src/stdio/__stdout_write.c).

* `set_tid_address(p)` (96): the thread id, some t with 1 ≤ t ≤ 4194304
  (PID_MAX_LIMIT; kernel/fork.c). The pid is not tracked: any is allowed.
* `rt_sigprocmask(how, set, oldset, 8)` (135): 0, and if `oldset ≠ 0` some 8
  bytes written there (the old mask is not tracked: any is allowed; no signal
  handler runs in this model). EINVAL when the size is not 8 or `set ≠ 0`
  with `how ∉ {0, 1, 2}` (kernel/signal.c).
* `ioctl(fd, TIOCGWINSZ, p)` (29, 0x5413), what musl's stdout asks to decide
  line buffering: on an open fd, ENOTTY (-25, not a terminal) or 0 with some
  8-byte `winsize` at `p`; on a closed fd EBADF. Every other ioctl: no outcome.

Each over-approximates Linux where the model has no state (sound for proofs
over every outcome). `ProcStep4.sys`: at every other syscall a step is a `Sys`
step.
-/
namespace NoCompiler.Linux

def sysSetTidAddress : Word := 96
def sysRtSigprocmask : Word := 135
def sysIoctl : Word := 29
def tiocgwinsz : Word := 0x5413
def enotty : Word := -(BitVec.ofNat 64 25)

def setTidSpec (o : Outcome) : Prop :=
  ∃ t : Nat, 1 ≤ t ∧ t ≤ 4194304 ∧ o = .ret { ret := BitVec.ofNat 64 t } none

def sigprocmaskSpec (i : SyscallInput) (o : Outcome) : Prop :=
  if i.arg 3 = 8 ∧ (i.arg 1 = 0 ∨ i.arg 0 = 0 ∨ i.arg 0 = 1 ∨ i.arg 0 = 2) then
    if i.arg 2 = 0 then o = .ret { ret := 0 } none
    else ∃ old : List Byte, old.length = 8 ∧ o = .ret { ret := 0, writes := [(i.arg 2, old)] } none
  else o = .ret { ret := einval } none

def ioctlSpec (k : Kern) (i : SyscallInput) (o : Outcome) : Prop :=
  if i.arg 1 = tiocgwinsz then
    if i.arg 0 ∈ k.fds then
      o = .ret { ret := enotty } none ∨
        ∃ ws : List Byte, ws.length = 8 ∧ o = .ret { ret := 0, writes := [(i.arg 2, ws)] } none
    else o = .ret { ret := ebadf } none
  else False

def procSpec4 (k : Kern) (i : SyscallInput) (o : Outcome) (k' : Kern) : Prop :=
  if i.sysno = sysSetTidAddress then setTidSpec o ∧ k' = k
  else if i.sysno = sysRtSigprocmask then sigprocmaskSpec i o ∧ k' = k
  else if i.sysno = sysIoctl then ioctlSpec k i o ∧ k' = k
  else procSpec3 k i o k'

inductive ProcStep4 : State × Kern → State × Kern → Prop
  | step {s : State} {k k' : Kern} {o : Outcome} :
      procSpec4 k (SyscallInput.of s) o k' → ProcStep4 (s, k) (o.apply s, k')

theorem ProcStep4.sys {s s' : State} {k k' : Kern} (h : ProcStep4 (s, k) (s', k'))
    (hc : s.reg Reg.a7 ≠ sysClose) (hb : s.reg Reg.a7 ≠ sysBrk) (hm : s.reg Reg.a7 ≠ sysMmap)
    (hu : s.reg Reg.a7 ≠ sysMunmap) (hv : s.reg Reg.a7 ≠ sysWritev)
    (ht : s.reg Reg.a7 ≠ sysSetTidAddress) (hg : s.reg Reg.a7 ≠ sysRtSigprocmask)
    (hi : s.reg Reg.a7 ≠ sysIoctl) : Sys s s' := by
  cases h with
  | step h =>
    have hno : (SyscallInput.of s).sysno = s.reg Reg.a7 := rfl
    simp only [procSpec4, hno, ht, hg, hi, ↓reduceIte] at h
    exact ProcStep3.sys (ProcStep3.step h) hc hb hm hu hv

/-- `rt_sigprocmask` with no old-set pointer and size 8 just returns 0. -/
theorem sigprocmask_no_old {i : SyscallInput} {o : Outcome} (h8 : i.arg 3 = 8) (hset : i.arg 1 = 0)
    (hold : i.arg 2 = 0) (h : sigprocmaskSpec i o) : o = .ret { ret := 0 } none := by
  simp only [sigprocmaskSpec, h8, hset, hold, true_or, and_self, ↓reduceIte] at h
  exact h

/-- Control: an ioctl other than TIOCGWINSZ has no outcome. -/
theorem ioctl_other_none {k : Kern} {i : SyscallInput} {o : Outcome} (h : i.arg 1 = 0x5401) :
    ¬ ioctlSpec k i o := by
  have hn : ¬ (i.arg 1 = tiocgwinsz) := by rw [h]; decide
  intro hp
  unfold ioctlSpec at hp
  simp only [hn, ↓reduceIte] at hp

end NoCompiler.Linux
