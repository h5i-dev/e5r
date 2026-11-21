import NoCompiler.Linux.Mmap

/-
The Linux layer, `writev` (66), the call musl's stdio makes for `printf` and
`puts` (Linux v6.18.46 fs/read_write.c do_writev, vfs_writev; LPS
Sys/Fs/ReadWrite.v).

`writev(fd, iov, iovcnt)` gathers `iovcnt` buffers, each an `iovec` of two
words (`iov_base`, `iov_len`) at `iov + 16 j`. On an open fd, with
`iovcnt ≤ 1024` (UIO_MAXIOV), the outcome is what `write` of the gathered
bytes gives: `r` bytes accepted, `r ≤ min total MAX_RW_COUNT`, `r ≥ 1` when
`total ≥ 1`, the event `write fd (first r bytes)`; or an error. More than
1024 iovecs: EINVAL (-22). A closed fd: EBADF (-9).

`writev_one`: with one iovec, `writev` has exactly the outcomes `write` of that
buffer has (`writeSpec`, Linux/Basic.lean).
-/
namespace NoCompiler.Linux

def sysWritev : Word := 66

/-- The `j`-th iovec's buffer. -/
def iovBuf (m : Word → Byte) (iov : Word) (j : Nat) : List Byte :=
  readBytes m (read64 m (iov + BitVec.ofNat 64 (16 * j)))
    (read64 m (iov + BitVec.ofNat 64 (16 * j + 8))).toNat

/-- The bytes of `n` iovecs, in order. -/
def gather (m : Word → Byte) (iov : Word) (n : Nat) : List Byte :=
  (List.range n).flatMap (iovBuf m iov)

/-- The outcomes `write` of the bytes `bs` to `fd` allows. -/
def writeBytesSpec (fd : Word) (bs : List Byte) : Outcome → Prop
  | .ret e ev => e.writes = [] ∧ e.zeros = [] ∧
    ((∃ r : Nat, r ≤ bs.length ∧ r ≤ maxRW ∧ (0 < bs.length → 0 < r) ∧
        e.ret = BitVec.ofNat 64 r ∧ ev = some (.write fd (bs.take r))) ∨
      (∃ n : Nat, 1 ≤ n ∧ n ≤ 4095 ∧ e.ret = -(BitVec.ofNat 64 n) ∧ ev = none))
  | .exit _ => False

def writevSpec (k : Kern) (i : SyscallInput) (o : Outcome) (k' : Kern) : Prop :=
  k' = k ∧
  if i.arg 0 ∈ k.fds then
    if 1024 < (i.arg 2).toNat then o = .ret { ret := einval } none
    else writeBytesSpec (i.arg 0) (gather i.mem (i.arg 1) (i.arg 2).toNat) o
  else o = .ret { ret := ebadf } none

/-- The process layer with `writev`. -/
def procSpec3 (k : Kern) (i : SyscallInput) (o : Outcome) (k' : Kern) : Prop :=
  if i.sysno = sysWritev then writevSpec k i o k' else procSpec2 k i o k'

inductive ProcStep3 : State × Kern → State × Kern → Prop
  | step {s : State} {k k' : Kern} {o : Outcome} :
      procSpec3 k (SyscallInput.of s) o k' → ProcStep3 (s, k) (o.apply s, k')

/-- At every syscall but close/brk/mmap/munmap/writev, a step is a `Sys` step. -/
theorem ProcStep3.sys {s s' : State} {k k' : Kern} (h : ProcStep3 (s, k) (s', k'))
    (hc : s.reg Reg.a7 ≠ sysClose) (hb : s.reg Reg.a7 ≠ sysBrk) (hm : s.reg Reg.a7 ≠ sysMmap)
    (hu : s.reg Reg.a7 ≠ sysMunmap) (hv : s.reg Reg.a7 ≠ sysWritev) : Sys s s' := by
  cases h with
  | step h =>
    have hno : (SyscallInput.of s).sysno = s.reg Reg.a7 := rfl
    simp only [procSpec3, hno, hv, ↓reduceIte] at h
    exact ProcStep2.sys (ProcStep2.step h) hc hb hm hu

theorem readBytes_take' (m : Word → Byte) (a : Word) (n r : Nat) (h : r ≤ n) :
    (readBytes m a n).take r = readBytes m a r := by
  induction r generalizing a n with
  | zero => simp [readBytes]
  | succ r ih =>
    cases n with
    | zero => omega
    | succ n => simp only [readBytes, List.take_succ_cons, ih _ n (by omega)]

theorem readBytes_length'' (m : Word → Byte) (a : Word) (n : Nat) : (readBytes m a n).length = n := by
  induction n generalizing a <;> simp [readBytes, *]

/-- With one iovec, `writev` is `write` of that buffer. -/
theorem writev_one {i : SyscallInput} {o : Outcome} (h1 : i.arg 2 = 1) :
    writeBytesSpec (i.arg 0) (gather i.mem (i.arg 1) (i.arg 2).toNat) o ↔
    writeSpec ⟨sysWrite, [i.arg 0, read64 i.mem (i.arg 1), read64 i.mem (i.arg 1 + 8), 0, 0, 0], i.mem⟩ o := by
  have hg : gather i.mem (i.arg 1) (i.arg 2).toNat =
      readBytes i.mem (read64 i.mem (i.arg 1)) (read64 i.mem (i.arg 1 + 8)).toNat := by
    rw [h1]; simp [gather, iovBuf]
  rw [hg]
  cases o with
  | exit _ => simp [writeBytesSpec, writeSpec]
  | ret e ev =>
    simp only [writeBytesSpec, writeSpec, SyscallInput.arg, List.getD_cons_zero, List.getD_cons_succ,
      readBytes_length'']
    constructor
    · rintro ⟨hw, hz, ⟨r, hr1, hr2, hr3, he, hev⟩ | herr⟩
      · exact ⟨hw, hz, .inl ⟨r, hr1, hr2, hr3, he, by rw [hev, readBytes_take' _ _ _ _ hr1]⟩⟩
      · exact ⟨hw, hz, .inr herr⟩
    · rintro ⟨hw, hz, ⟨r, hr1, hr2, hr3, he, hev⟩ | herr⟩
      · exact ⟨hw, hz, .inl ⟨r, hr1, hr2, hr3, he, by rw [hev, readBytes_take' _ _ _ _ hr1]⟩⟩
      · exact ⟨hw, hz, .inr herr⟩

/-- Control: more than 1024 iovecs give only EINVAL. -/
theorem writev_too_many {k k' : Kern} {i : SyscallInput} {o : Outcome} (hfd : i.arg 0 ∈ k.fds)
    (hn : 1024 < (i.arg 2).toNat) (h : writevSpec k i o k') : o = .ret { ret := einval } none := by
  simp only [writevSpec, hfd, hn, ↓reduceIte] at h
  exact h.2

end NoCompiler.Linux
