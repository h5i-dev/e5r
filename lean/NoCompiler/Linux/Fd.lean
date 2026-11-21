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

/-- An open regular file (Linux/Fs.lean): its contents and the file offset. -/
structure OpenFile where
  data : List Byte
  off : Nat

/-- The kernel's state of the process, so far: its open descriptors. -/
structure Kern where
  fds : List Word
  /-- The program break's start and current value (Linux/Brk.lean); 0 until the loader sets them. -/
  startBrk : Word := 0
  brk : Word := 0
  /-- The mapped ranges, (base, size), each below TASK_SIZE: what a load or a
      store may touch (Linux/Process.lean). The loader's image and stack, the
      heap `brk` grows, the pages `mmap` maps; `munmap` and a `brk` shrink cut
      them out again. -/
  maps : List (Word × Nat) := []
  /-- The read-only in-memory file system (Linux/Fs.lean): path bytes (no NUL) and contents. -/
  fs : List (List Byte × List Byte) := []
  /-- The descriptors `openat` opened on files of `fs`, with their offsets. -/
  files : List (Word × OpenFile) := []
  /-- Protection overlays on `maps` (Linux/Prot.lean): ranges that are read-only
      (PROT_READ or PROT_EXEC without PROT_WRITE), and ranges with no access
      (PROT_NONE). Everything else mapped is read-write. -/
  ro : List (Word × Nat) := []
  noacc : List (Word × Nat) := []

def Kern.init : Kern := { fds := [0, 1, 2] }

/-- What is left of the range `p` once `[a, a + n)` is cut out of it (as numbers). -/
def cutRange (a n : Nat) (p : Word × Nat) : List (Word × Nat) :=
  let b := p.1.toNat
  let e := b + p.2
  (if b < a then [(p.1, min e a - b)] else []) ++
  (if a + n < e then [(BitVec.ofNat 64 (max b (a + n)), e - max b (a + n))] else [])

/-- The mapped ranges with `[a, a + n)` unmapped (Linux `do_vmi_munmap`: every
    range that meets it is cut, not only one). -/
def unmapRanges (maps : List (Word × Nat)) (a : Word) (n : Nat) : List (Word × Nat) :=
  maps.flatMap (cutRange a.toNat n)

/-- After unmapping `[a, a + n)`, no range covers an address in it (all ranges
    below 2^63, so their bases are exact as numbers). -/
theorem unmap_gone {maps : List (Word × Nat)} {a : Word} {n x : Nat}
    (hb : ∀ p ∈ maps, p.1.toNat + p.2 < 2 ^ 63) (hx1 : a.toNat ≤ x) (hx2 : x < a.toNat + n) :
    ∀ q ∈ unmapRanges maps a n, ¬ (q.1.toNat ≤ x ∧ x < q.1.toNat + q.2) := by
  intro q hq
  simp only [unmapRanges, List.mem_flatMap] at hq
  obtain ⟨p, hp, hq⟩ := hq
  have hlt := hb p hp
  simp only [cutRange, List.mem_append] at hq
  rcases hq with hq | hq
  · split at hq
    · simp only [List.mem_singleton] at hq; subst hq; dsimp only; omega
    · simp at hq
  · split at hq
    · simp only [List.mem_singleton] at hq; subst hq; dsimp only
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    · simp at hq

/-- The ranges `l` with every range of `cs` cut out. -/
def cutAll (l cs : List (Word × Nat)) : List (Word × Nat) :=
  cs.foldl (fun acc c => unmapRanges acc c.1 c.2) l

/-- The part of `q` inside `p` (as numbers; empty when they do not meet). -/
def interRange (p q : Word × Nat) : List (Word × Nat) :=
  let b := max p.1.toNat q.1.toNat
  let e := min (p.1.toNat + p.2) (q.1.toNat + q.2)
  if b < e then [(BitVec.ofNat 64 b, e - b)] else []

/-- The parts of the ranges `qs` inside some range of `ps`. -/
def interAll (ps qs : List (Word × Nat)) : List (Word × Nat) :=
  qs.flatMap fun q => ps.flatMap fun p => interRange p q

/-- `[a, a + n)` unmapped: cut out of the mapped ranges and the overlays. -/
def Kern.unmap (k : Kern) (a : Word) (n : Nat) : Kern :=
  { k with maps := unmapRanges k.maps a n, ro := unmapRanges k.ro a n, noacc := unmapRanges k.noacc a n }

@[simp] theorem Kern.unmap_maps (k : Kern) (a : Word) (n : Nat) :
    (k.unmap a n).maps = unmapRanges k.maps a n := rfl

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
