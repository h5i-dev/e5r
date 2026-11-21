import NoCompiler.Linux.Fs

/-
The Linux layer, tenth step: the rest of what musl's stdio does to a file
(src/stdio/__stdio_read.c reads with `readv`; `fseek` and `ftell` call
`lseek`). Linux v6.18.46 fs/read_write.c (do_readv, vfs_readv; ksys_lseek,
generic_file_llseek).

* `readv(fd, iov, iovcnt)` (65): on a file, the next `min total MAX_RW_COUNT`
  bytes, scattered over the iovecs in order, the offset advanced; on another
  open fd, any bytes of at most that length, scattered the same way (as
  `read`), or an error; more than 1024 iovecs: EINVAL; a closed fd: EBADF.
* `lseek(fd, off, whence)` (62): on a file, SEEK_SET/CUR/END to `off`,
  `cur + off`, `len + off` (signed), EINVAL outside `[0, 2^63)`; past the end
  is allowed. SEEK_DATA/SEEK_HOLE as on a file with no holes (`seekTo`);
  another `whence`: EINVAL. On fds 0/1/2 (a terminal, a pipe or a
  file: not known) ESPIPE or any offset. A closed fd: EBADF.

`ProcStep6.sys`, `ProcStep6.maps_old`, `procSpec6_exists`: as for the layer
below, so Process.lean's theorems carry over.
-/
namespace NoCompiler.Linux

def sysReadv : Word := 65
def sysLseek : Word := 62
def espipe : Word := -(BitVec.ofNat 64 29)

/-- The `j`-th iovec: its base and length. -/
def iovAt (m : Word → Byte) (iov : Word) (j : Nat) : Word × Nat :=
  (read64 m (iov + BitVec.ofNat 64 (16 * j)), (read64 m (iov + BitVec.ofNat 64 (16 * j + 8))).toNat)

def iovs (m : Word → Byte) (iov : Word) (n : Nat) : List (Word × Nat) := (List.range n).map (iovAt m iov)

/-- `ds` spread over the buffers in order: each gets the next bytes, at most its length. -/
def scatter : List (Word × Nat) → List Byte → List (Word × List Byte)
  | [], _ => []
  | (b, n) :: vs, ds => (b, ds.take n) :: scatter vs (ds.drop n)

def iovTotal (vs : List (Word × Nat)) : Nat := (vs.map (·.2)).sum

def readvSpec (k : Kern) (i : SyscallInput) (o : Outcome) (k' : Kern) : Prop :=
  if i.arg 0 ∈ k.fds then
    if 1024 < (i.arg 2).toNat then o = .ret { ret := einval } none ∧ k' = k
    else
      let vs := iovs i.mem (i.arg 1) (i.arg 2).toNat
      match k.files.lookup (i.arg 0) with
      | some f =>
        let ds := f.chunk (iovTotal vs)
        o = .ret { ret := BitVec.ofNat 64 ds.length, writes := scatter vs ds } (some (.read (i.arg 0) ds)) ∧
          k' = { k with files := k.files.map fun p =>
            if p.1 = i.arg 0 then (p.1, { p.2 with off := p.2.off + ds.length }) else p }
      | none =>
        k' = k ∧
        ((∃ ds : List Byte, ds.length ≤ iovTotal vs ∧ ds.length ≤ maxRW ∧
            o = .ret { ret := BitVec.ofNat 64 ds.length, writes := scatter vs ds } (some (.read (i.arg 0) ds))) ∨
          (∃ n : Nat, 1 ≤ n ∧ n ≤ 4095 ∧ o = .ret { ret := -(BitVec.ofNat 64 n) } none))
  else o = .ret { ret := ebadf } none ∧ k' = k

def enxio : Word := -(BitVec.ofNat 64 6)

/-- What `lseek` returns on a file, and the new offset if it moves
    (generic_file_llseek_size, v6.18.46 fs/read_write.c): SEEK_SET/CUR/END
    to a result in `[0, 2^63)` (MAX_LFS_FILESIZE), else EINVAL; SEEK_DATA (3)
    and SEEK_HOLE (4) on a file with no holes: `off` and the length when
    `0 ≤ off < length`, else ENXIO; another `whence`: EINVAL. -/
def seekTo (f : OpenFile) (off whence : Word) : Word × Option Nat :=
  let len : Int := f.data.length
  let o : Int := off.toInt
  let go (t : Int) : Word × Option Nat :=
    if 0 ≤ t ∧ t < 2 ^ 63 then (BitVec.ofNat 64 t.toNat, some t.toNat) else (einval, none)
  if whence = 0 then go o
  else if whence = 1 then go (f.off + o)
  else if whence = 2 then go (len + o)
  else if whence = 3 then (if 0 ≤ o ∧ o < len then go o else (enxio, none))
  else if whence = 4 then (if 0 ≤ o ∧ o < len then go len else (enxio, none))
  else (einval, none)

def lseekSpec (k : Kern) (i : SyscallInput) (o : Outcome) (k' : Kern) : Prop :=
  if i.arg 0 ∈ k.fds then
    match k.files.lookup (i.arg 0) with
    | some f =>
      let r := seekTo f (i.arg 1) (i.arg 2)
      o = .ret { ret := r.1 } none ∧
      match r.2 with
      | some t => k' = { k with files := k.files.map fun p => if p.1 = i.arg 0 then (p.1, { p.2 with off := t }) else p }
      | none => k' = k
    | none => k' = k ∧ (o = .ret { ret := espipe } none ∨ ∃ t : Nat, t < 2 ^ 63 ∧ o = .ret { ret := BitVec.ofNat 64 t } none)
  else o = .ret { ret := ebadf } none ∧ k' = k

def procSpec6 (k : Kern) (i : SyscallInput) (o : Outcome) (k' : Kern) : Prop :=
  if i.sysno = sysReadv then readvSpec k i o k'
  else if i.sysno = sysLseek then lseekSpec k i o k'
  else procSpec5 k i o k'

inductive ProcStep6 : State × Kern → State × Kern → Prop
  | step {s : State} {k k' : Kern} {o : Outcome} :
      procSpec6 k (SyscallInput.of s) o k' → ProcStep6 (s, k) (o.apply s, k')

theorem OldSys.ne6 {s : State} (h : OldSys s) : s.reg Reg.a7 ≠ sysReadv ∧ s.reg Reg.a7 ≠ sysLseek := by
  rcases h with h | h | h | h <;> rw [h] <;> decide

theorem procSpec6_old {s : State} {k k' : Kern} {o : Outcome} (ho : OldSys s) :
    procSpec6 k (SyscallInput.of s) o k' ↔ procSpec5 k (SyscallInput.of s) o k' := by
  obtain ⟨h1, h2⟩ := ho.ne6
  have hno : (SyscallInput.of s).sysno = s.reg Reg.a7 := rfl
  simp only [procSpec6, hno, h1, h2, ↓reduceIte]

theorem ProcStep6.sys {s s' : State} {k k' : Kern} (h : ProcStep6 (s, k) (s', k'))
    (hr : s.reg Reg.a7 ≠ sysReadv) (hl : s.reg Reg.a7 ≠ sysLseek)
    (ho : s.reg Reg.a7 ≠ sysOpenat) (hf : s.reg Reg.a7 ≠ sysFstat)
    (hc : s.reg Reg.a7 ≠ sysClose) (hb : s.reg Reg.a7 ≠ sysBrk) (hm : s.reg Reg.a7 ≠ sysMmap)
    (hu : s.reg Reg.a7 ≠ sysMunmap) (hv : s.reg Reg.a7 ≠ sysWritev)
    (ht : s.reg Reg.a7 ≠ sysSetTidAddress) (hg : s.reg Reg.a7 ≠ sysRtSigprocmask)
    (hi : s.reg Reg.a7 ≠ sysIoctl) : Sys s s' := by
  cases h with
  | step h =>
    have hno : (SyscallInput.of s).sysno = s.reg Reg.a7 := rfl
    simp only [procSpec6, hno, hr, hl, ↓reduceIte] at h
    exact ProcStep5.sys (ProcStep5.step h) ho hf hc hb hm hu hv ht hg hi

theorem ProcStep6.maps_old {s s' : State} {k k' : Kern} (h : ProcStep6 (s, k) (s', k'))
    (ho : OldSys s) : k'.maps = k.maps := by
  cases h with
  | step h => exact ProcStep5.maps_old (ProcStep5.step ((procSpec6_old ho).1 h)) ho

theorem procSpec6_exists {s s₁ : State} (k : Kern) (ho : OldSys s) (hy : Sys s s₁) :
    ∃ o k', procSpec6 k (SyscallInput.of s) o k' := by
  obtain ⟨o, k', h⟩ := procSpec5_exists k ho hy
  exact ⟨o, k', (procSpec6_old ho).2 h⟩

/-- Two iovecs of 2 and 3 bytes get "ab" and "cde" of "abcdef" (6 bytes, so
    the file's last byte waits for the next read). -/
example : scatter [(0x100, 2), (0x200, 3)] ((OpenFile.chunk ⟨[0x61, 0x62, 0x63, 0x64, 0x65, 0x66], 0⟩ 5)) =
    [(0x100, [0x61, 0x62]), (0x200, [0x63, 0x64, 0x65])] := by decide

/-- `fseek(f, -2, SEEK_END)` on a 6-byte file: offset 4. `lseek(fd, -1, SEEK_SET)`: EINVAL. -/
example : seekTo ⟨[0, 0, 0, 0, 0, 0], 1⟩ (-2) 2 = (4, some 4) := by decide
example : seekTo ⟨[0, 0, 0, 0, 0, 0], 1⟩ (-1) 0 = (einval, none) := by decide
/-- SEEK_DATA at 2 of 6: 2; SEEK_HOLE at 2: 6 (the end); SEEK_DATA at 6: ENXIO. -/
example : seekTo ⟨[0, 0, 0, 0, 0, 0], 1⟩ 2 3 = (2, some 2) := by decide
example : seekTo ⟨[0, 0, 0, 0, 0, 0], 1⟩ 2 4 = (6, some 6) := by decide
example : seekTo ⟨[0, 0, 0, 0, 0, 0], 1⟩ 6 3 = (enxio, none) := by decide
/-- Control: `whence` 5 does not exist: EINVAL, the offset unchanged. -/
example : seekTo ⟨[0, 0, 0, 0, 0, 0], 1⟩ 0 5 = (einval, none) := by decide

/-- Control: `lseek` on a closed fd gives only EBADF. -/
theorem lseek_closed {k k' : Kern} {i : SyscallInput} {o : Outcome} (h0 : i.arg 0 ∉ k.fds)
    (h : lseekSpec k i o k') : o = .ret { ret := ebadf } none := by
  simp only [lseekSpec, h0, ↓reduceIte] at h
  exact h.1

end NoCompiler.Linux
