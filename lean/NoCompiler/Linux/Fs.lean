import NoCompiler.Linux.Startup

/-
The Linux layer: files, for the fuzz-driver shape `prog FILE` (step 4 of the
port, docs/design/prior-art-lps.md; LPS theories/LinuxProcessSem/Fs/). A
read-only file system in memory (`Kern.fs`, given at the start), and:

* `openat(dirfd, path, flags, mode)` (56): `path` a NUL-terminated string of
  at most PATH_MAX (4096) bytes; `dirfd` AT_FDCWD (-100) or the path
  absolute; flags read-only (`flags & O_ACCMODE = 0`) without O_CREAT,
  O_TRUNC or O_DIRECTORY. A path in `fs`: the lowest free descriptor
  (fs/file.c, alloc_fd), EMFILE (-24) from 1024 on (RLIMIT_NOFILE's default
  soft limit); a path not in `fs`: ENOENT (-2). Anything else (writing,
  creating, other dirfds): no outcome, the process cannot step.
* `read(fd, buf, n)` on a file descriptor: exactly the next
  `min n MAX_RW_COUNT` bytes of the file from its offset (fewer at the end,
  0 at end of file), the offset advanced. This is one of the outcomes the
  trusted `Sys` already allows (`fileRead_sys`): a file read only removes
  behaviours.
* `fstat(fd, buf)` (80): on an open fd, some 128-byte `struct stat` (the
  riscv64 asm-generic layout) whose `st_size` (bytes 48-55) is the file's
  length for a file fd; any for 0/1/2; EBADF on a closed fd.
* `close(fd)` also forgets the file.

`ProcStep5.sys`: at every syscall but the new ones and those of the earlier
layers, a step is a `Sys` step, read included.
-/
namespace NoCompiler.Linux

def sysOpenat : Word := 56
def sysFstat : Word := 80
def atFdcwd : Word := -(BitVec.ofNat 64 100)
def enoent : Word := -(BitVec.ofNat 64 2)
def emfile : Word := -(BitVec.ofNat 64 24)

/-- The NUL-terminated string at `a`, at most `n` bytes before the NUL. -/
def cString (m : Word → Byte) (a : Word) : Nat → Option (List Byte)
  | 0 => none
  | n + 1 => if m a = 0 then some [] else (cString m (a + 1) n).map (m a :: ·)

/-- The lowest descriptor number not open (alloc_fd). -/
def lowestFree (fds : List Word) : Nat :=
  ((List.range (fds.length + 1)).find? fun n => BitVec.ofNat 64 n ∉ fds).getD fds.length

/-- O_ACCMODE | O_CREAT | O_TRUNC | O_DIRECTORY (asm-generic/fcntl.h). -/
def openBadFlags : Word := 0x3 ||| 0x40 ||| 0x200 ||| 0x10000

def openatSpec (k : Kern) (i : SyscallInput) (o : Outcome) (k' : Kern) : Prop :=
  match cString i.mem (i.arg 1) 4096 with
  | none => False
  | some p =>
    (i.arg 0 = atFdcwd ∨ p.head? = some 0x2f) ∧ i.arg 2 &&& openBadFlags = 0 ∧
    match k.fs.lookup p with
    | none => o = .ret { ret := enoent } none ∧ k' = k
    | some d =>
      let n := lowestFree k.fds
      if n < 1024 then
        o = .ret { ret := BitVec.ofNat 64 n } none ∧
          k' = { k with fds := k.fds ++ [BitVec.ofNat 64 n],
                        files := (BitVec.ofNat 64 n, ⟨d, 0⟩) :: k.files }
      else o = .ret { ret := emfile } none ∧ k' = k

/-- The bytes a read of `n` gets from an open file. -/
def OpenFile.chunk (f : OpenFile) (n : Nat) : List Byte := (f.data.drop f.off).take (min n maxRW)

def fileReadOutcome (i : SyscallInput) (f : OpenFile) : Outcome :=
  let ds := f.chunk (i.arg 2).toNat
  .ret { ret := BitVec.ofNat 64 ds.length, writes := [(i.arg 1, ds)] } (some (.read (i.arg 0) ds))

/-- The 8 little-endian bytes of `n`. -/
def le64 (n : Nat) : List Byte := (List.range 8).map fun j => BitVec.ofNat 8 (n >>> (8 * j))

def fstatSpec (k : Kern) (i : SyscallInput) (o : Outcome) : Prop :=
  if i.arg 0 ∈ k.fds then
    ∃ st : List Byte, st.length = 128 ∧
      (∀ f, k.files.lookup (i.arg 0) = some f → (st.drop 48).take 8 = le64 f.data.length) ∧
      o = .ret { ret := 0, writes := [(i.arg 1, st)] } none
  else o = .ret { ret := ebadf } none

def procSpec5 (k : Kern) (i : SyscallInput) (o : Outcome) (k' : Kern) : Prop :=
  if i.sysno = sysOpenat then openatSpec k i o k'
  else if i.sysno = sysFstat then fstatSpec k i o ∧ k' = k
  else if i.sysno = sysRead then
    match k.files.lookup (i.arg 0) with
    | some f =>
      o = fileReadOutcome i f ∧
        k' = { k with files := k.files.map fun p =>
          if p.1 = i.arg 0 then (p.1, { p.2 with off := p.2.off + (f.chunk (i.arg 2).toNat).length })
          else p }
    | none => procSpec4 k i o k'
  else if i.sysno = sysClose then
    -- `procSpec4`'s `close`, the file forgotten
    ∃ k₁, procSpec4 k i o k₁ ∧ k' = { k₁ with files := k.files.filter (·.1 ≠ i.arg 0) }
  else procSpec4 k i o k'

inductive ProcStep5 : State × Kern → State × Kern → Prop
  | step {s : State} {k k' : Kern} {o : Outcome} :
      procSpec5 k (SyscallInput.of s) o k' → ProcStep5 (s, k) (o.apply s, k')

/-- A file read is one of the reads the trusted model allows. -/
theorem fileRead_sys {s : State} (f : OpenFile) (h : s.reg Reg.a7 = sysRead) :
    Sys s ((fileReadOutcome (SyscallInput.of s) f).apply s) := by
  refine basic_iff_sys.1 (Basic.step ?_)
  have hno : (SyscallInput.of s).sysno = s.reg Reg.a7 := rfl
  simp only [spec, hno, h, ↓reduceIte, fileReadOutcome, readSpec]
  refine ⟨trivial, .inl ⟨_, ?_, ?_, rfl, rfl, rfl⟩⟩ <;>
    simp only [OpenFile.chunk, List.length_take] <;> omega

theorem ProcStep5.sys {s s' : State} {k k' : Kern} (h : ProcStep5 (s, k) (s', k'))
    (ho : s.reg Reg.a7 ≠ sysOpenat) (hf : s.reg Reg.a7 ≠ sysFstat)
    (hc : s.reg Reg.a7 ≠ sysClose) (hb : s.reg Reg.a7 ≠ sysBrk) (hm : s.reg Reg.a7 ≠ sysMmap)
    (hu : s.reg Reg.a7 ≠ sysMunmap) (hv : s.reg Reg.a7 ≠ sysWritev)
    (ht : s.reg Reg.a7 ≠ sysSetTidAddress) (hg : s.reg Reg.a7 ≠ sysRtSigprocmask)
    (hi : s.reg Reg.a7 ≠ sysIoctl) : Sys s s' := by
  cases h with
  | step h =>
    have hno : (SyscallInput.of s).sysno = s.reg Reg.a7 := rfl
    simp only [procSpec5, hno, ho, hf, hc, ↓reduceIte] at h
    by_cases hr : s.reg Reg.a7 = sysRead
    · simp only [hr, ↓reduceIte] at h
      split at h
      · rename_i f _
        obtain ⟨rfl, -⟩ := h
        exact fileRead_sys f hr
      · exact ProcStep4.sys (ProcStep4.step h) hc hb hm hu hv ht hg hi
    · simp only [hr, ↓reduceIte] at h
      exact ProcStep4.sys (ProcStep4.step h) hc hb hm hu hv ht hg hi

/-- The trusted model's syscalls: read, write, exit, exit_group. -/
def OldSys (s : State) : Prop :=
  s.reg Reg.a7 = sysRead ∨ s.reg Reg.a7 = sysWrite ∨ s.reg Reg.a7 = sysExit ∨ s.reg Reg.a7 = sysExitGroup

theorem OldSys.ne {s : State} (h : OldSys s) :
    s.reg Reg.a7 ≠ sysOpenat ∧ s.reg Reg.a7 ≠ sysFstat ∧
    s.reg Reg.a7 ≠ sysClose ∧ s.reg Reg.a7 ≠ sysBrk ∧ s.reg Reg.a7 ≠ sysMmap ∧
    s.reg Reg.a7 ≠ sysMunmap ∧ s.reg Reg.a7 ≠ sysWritev ∧ s.reg Reg.a7 ≠ sysSetTidAddress ∧
    s.reg Reg.a7 ≠ sysRtSigprocmask ∧ s.reg Reg.a7 ≠ sysIoctl := by
  rcases h with h | h | h | h <;> rw [h] <;> decide

/-- At the trusted model's syscalls the earlier layers leave `Kern` alone. -/
theorem procSpec4_old {s : State} {k k' : Kern} {o : Outcome} (ho : OldSys s)
    (h : procSpec4 k (SyscallInput.of s) o k') : k' = k := by
  obtain ⟨-, -, h1, h2, h3, h4, h5, h6, h7, h8⟩ := ho.ne
  have hno : (SyscallInput.of s).sysno = s.reg Reg.a7 := rfl
  simp only [procSpec4, procSpec3, procSpec2, procSpec, hno, h2, h3, h4, h5, h6, h7, h8,
    ↓reduceIte] at h
  unfold fdSpec at h
  simp only [hno, h1, ↓reduceIte] at h
  split at h
  · split at h
    · exact h.2
    · exact h.2
  · exact h.2

/-- At the trusted model's syscalls the mapped ranges do not change (a file
    read moves only its offset). -/
theorem ProcStep5.maps_old {s s' : State} {k k' : Kern} (h : ProcStep5 (s, k) (s', k'))
    (ho : OldSys s) : k'.maps = k.maps := by
  cases h with
  | step h =>
    obtain ⟨h1, h2, h3, -⟩ := ho.ne
    have hno : (SyscallInput.of s).sysno = s.reg Reg.a7 := rfl
    simp only [procSpec5, hno, h1, h2, h3, ↓reduceIte] at h
    split at h
    · split at h
      · rw [h.2]
      · rw [procSpec4_old ho h]
    · rw [procSpec4_old ho h]

/-- Where the trusted model has a syscall step, this layer has an outcome:
    on a file, the file read; on a closed fd, EBADF; else the same. -/
theorem procSpec5_exists {s s₁ : State} (k : Kern) (ho : OldSys s) (hy : Sys s s₁) :
    ∃ o k', procSpec5 k (SyscallInput.of s) o k' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := ho.ne
  have hno : (SyscallInput.of s).sysno = s.reg Reg.a7 := rfl
  obtain ⟨o, hspec⟩ : ∃ o, spec (SyscallInput.of s) o := by
    obtain ⟨hs⟩ := basic_iff_sys.2 hy
    exact ⟨_, hs⟩
  have h4' : ∃ o' k', procSpec4 k (SyscallInput.of s) o' k' := by
    have : ∃ o' k', fdSpec k (SyscallInput.of s) o' k' := by
      unfold fdSpec
      by_cases hrw : (SyscallInput.of s).sysno = sysRead ∨ (SyscallInput.of s).sysno = sysWrite
      · simp only [hrw, ↓reduceIte]
        by_cases hfd : (SyscallInput.of s).arg 0 ∈ k.fds
        · exact ⟨o, k, by simp only [hfd, ↓reduceIte]; exact ⟨hspec, trivial⟩⟩
        · exact ⟨_, k, by simp only [hfd, ↓reduceIte]; exact ⟨rfl, trivial⟩⟩
      · have hcl : ¬ (SyscallInput.of s).sysno = sysClose := by rw [hno]; exact h3
        simp only [hrw, hcl, ↓reduceIte]
        exact ⟨o, k, hspec, rfl⟩
    obtain ⟨o', k', hfd⟩ := this
    refine ⟨o', k', ?_⟩
    simp only [procSpec4, procSpec3, procSpec2, procSpec, hno, h4, h5, h6, h7, h8, h9, h10, ↓reduceIte]
    exact hfd
  simp only [procSpec5, hno, h1, h2, h3, ↓reduceIte]
  by_cases hr : s.reg Reg.a7 = sysRead
  · simp only [hr, ↓reduceIte]
    split
    · exact ⟨_, _, rfl, rfl⟩
    · exact h4'
  · simp only [hr, ↓reduceIte]
    exact h4'

/-- The lowest free descriptor: 3 in a fresh process, 1 once fd 1 is closed. -/
example : lowestFree [0, 1, 2] = 3 := by decide
example : lowestFree [0, 2] = 1 := by decide

/-- A read gets the next bytes of the file; at the end, none. -/
example : OpenFile.chunk ⟨[1, 2, 3], 1⟩ 10 = [2, 3] := by decide
example : OpenFile.chunk ⟨[1, 2, 3], 3⟩ 10 = [] := by decide

/-- The path at `0x100` is "in" (0x69 0x6e, then NUL). -/
def memIn : Word → Byte := fun a => if a = 0x100 then 0x69 else if a = 0x101 then 0x6e else 0

example : cString memIn 0x100 4096 = some [0x69, 0x6e] := by decide

/-- `openat(AT_FDCWD, "in", O_RDONLY)` in a fresh process with "in" in the
    file system: fd 3, open on the file at offset 0. -/
theorem openat_in {o : Outcome} {k' : Kern}
    (h : openatSpec { Kern.init with fs := [([0x69, 0x6e], [7, 8, 9])] }
      ⟨sysOpenat, [atFdcwd, 0x100, 0, 0, 0, 0], memIn⟩ o k') :
    o = .ret { ret := 3 } none ∧ k'.files = [(3, ⟨[7, 8, 9], 0⟩)] := by
  have hs : cString memIn 0x100 4096 = some [0x69, 0x6e] := by decide
  simp only [openatSpec, SyscallInput.arg, List.getD, hs] at h
  obtain ⟨-, -, h⟩ := h
  have hl : List.lookup [0x69, 0x6e] [(([0x69, 0x6e] : List Byte), ([7, 8, 9] : List Byte))] =
      some [7, 8, 9] := by decide
  have hf : lowestFree Kern.init.fds = 3 := by decide
  simp only [hl, hf] at h
  simp only [show (3 : Nat) < 1024 by decide, ↓reduceIte] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

/-- Control: a path not in the file system: ENOENT, nothing opened. -/
theorem openat_missing {o : Outcome} {k' : Kern}
    (h : openatSpec Kern.init ⟨sysOpenat, [atFdcwd, 0x100, 0, 0, 0, 0], memIn⟩ o k') :
    o = .ret { ret := enoent } none ∧ k' = Kern.init := by
  have hs : cString memIn 0x100 4096 = some [0x69, 0x6e] := by decide
  simp only [openatSpec, SyscallInput.arg, List.getD, hs] at h
  exact h.2.2

/-- Control: opening for writing (O_WRONLY) has no outcome: the process cannot step. -/
theorem openat_write_none {k k' : Kern} {o : Outcome} (m : Word → Byte) (d p : Word) :
    ¬ openatSpec k ⟨sysOpenat, [d, p, 1, 0, 0, 0], m⟩ o k' := by
  intro h
  unfold openatSpec at h
  split at h
  · exact h
  · have h1 : (1 : Word) &&& openBadFlags ≠ 0 := by decide
    exact h1 h.2.1

end NoCompiler.Linux
