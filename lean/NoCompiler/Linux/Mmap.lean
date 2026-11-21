import NoCompiler.Linux.Brk

/-
The Linux layer, anonymous `mmap` (222), after LPS Sys/Mm/Mmap.v (Linux
v6.18.46 mm/mmap.c do_mmap, mm/util.c vm_mmap_pgoff).

* `mmap(0, len, prot, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0)` with `len > 0`:
  some page-aligned address `a` such that the `PAGE_ALIGN(len)` bytes from
  `a` lie below TASK_SIZE (0x800000000000, Sv48) and meet no earlier
  mapping, zero-filled; or ENOMEM. Linux chooses one address
  (generic_get_unmapped_area_topdown, which LPS runs); any free one is
  allowed here, which over-approximates Linux and is sound for proofs that
  hold for every outcome.
* `munmap` (215): the pages cut out of `Kern.maps` (Linux/Fd.lean), so a
  later access faults (Linux/Process.lean); EINVAL for an unaligned address
  or a zero length.
* Every other `mmap` (a file, MAP_FIXED, an address hint): NO outcome, fail
  closed.
* `prot`: the new pages are read-write with PROT_WRITE, read-only with
  PROT_READ or PROT_EXEC alone, no access with PROT_NONE (`withProt`;
  Linux/Process.lean's permission); a bit beyond the three: no outcome.
-/
namespace NoCompiler.Linux

def sysMmap : Word := 222
def sysMunmap : Word := 215
def mapPrivateAnon : Word := 0x22
def taskSize : Nat := 0x800000000000
def enomem : Word := -(BitVec.ofNat 64 12)
def einval : Word := -(BitVec.ofNat 64 22)

/-- `[a, a + n)` and `[b, b + m)` share no byte (as numbers; both below TASK_SIZE). -/
def disjointNat (a : Nat) (n : Nat) (b : Nat) (m : Nat) : Prop := a + n ≤ b ∨ b + m ≤ a

/-- PROT_READ, PROT_WRITE, PROT_EXEC (asm-generic/mman-common.h). -/
def protWrite : Word := 2
def protReadExec : Word := 1 ||| 4

/-- `[a, a + n)` with the protection `prot`, over whatever overlay it had:
    read-write with PROT_WRITE (on RISC-V a writable page is readable),
    read-only with PROT_READ or PROT_EXEC alone, no access with PROT_NONE. -/
def withProt (prot a : Word) (n : Nat) (k : Kern) : Kern :=
  let ro := unmapRanges k.ro a n
  let na := unmapRanges k.noacc a n
  if prot &&& protWrite ≠ 0 then { k with ro := ro, noacc := na }
  else if prot &&& protReadExec ≠ 0 then { k with ro := (a, n) :: ro, noacc := na }
  else { k with ro := ro, noacc := (a, n) :: na }

def mmapSpec (k : Kern) (i : SyscallInput) (o : Outcome) (k' : Kern) : Prop :=
  let len := pageUp (i.arg 1)
  if i.arg 0 = 0 ∧ i.arg 3 = mapPrivateAnon ∧ i.arg 4 = -1 ∧ i.arg 5 = 0 ∧ 0 < (i.arg 1).toNat ∧
      (i.arg 2).toNat < 8 then
    (∃ a : Word, a.toNat % 4096 = 0 ∧ a.toNat + len ≤ taskSize ∧
        (∀ p ∈ k.maps, disjointNat a.toNat len p.1.toNat p.2) ∧
        o = .ret { ret := a, zeros := [(a, len)] } none ∧ k' = withProt (i.arg 2) a len { k with maps := (a, len) :: k.maps }) ∨
      (o = .ret { ret := enomem } none ∧ k' = k)
  else False

/-- `munmap(addr, len)`: 0, with the page-rounded range cut out of the mapped
    ranges, for a page-aligned `addr` and `len > 0`; EINVAL otherwise
    (mm/mmap.c, do_vmi_munmap). Unmapping a range that holds no mapping
    succeeds too, as in Linux. -/
def munmapSpec (k : Kern) (i : SyscallInput) (o : Outcome) (k' : Kern) : Prop :=
  if (i.arg 0).toNat % 4096 = 0 ∧ 0 < (i.arg 1).toNat then
    o = .ret { ret := 0 } none ∧ k' = k.unmap (i.arg 0) (pageUp (i.arg 1))
  else o = .ret { ret := einval } none ∧ k' = k

/-- The process layer with `mmap` and `munmap`. -/
def procSpec2 (k : Kern) (i : SyscallInput) (o : Outcome) (k' : Kern) : Prop :=
  if i.sysno = sysMmap then mmapSpec k i o k'
  else if i.sysno = sysMunmap then munmapSpec k i o k'
  else procSpec k i o k'

inductive ProcStep2 : State × Kern → State × Kern → Prop
  | step {s : State} {k k' : Kern} {o : Outcome} :
      procSpec2 k (SyscallInput.of s) o k' → ProcStep2 (s, k) (o.apply s, k')

theorem ProcStep2.sys {s s' : State} {k k' : Kern} (h : ProcStep2 (s, k) (s', k'))
    (hc : s.reg Reg.a7 ≠ sysClose) (hb : s.reg Reg.a7 ≠ sysBrk) (hm : s.reg Reg.a7 ≠ sysMmap)
    (hu : s.reg Reg.a7 ≠ sysMunmap) : Sys s s' := by
  cases h with
  | step h =>
    have hno : (SyscallInput.of s).sysno = s.reg Reg.a7 := rfl
    simp only [procSpec2, hno, hm, hu, ↓reduceIte] at h
    exact ProcStep.sys (ProcStep.step h) hc hb

/-- A successful `mmap` gives fresh pages: aligned, below TASK_SIZE, apart from
    every earlier mapping, zero-filled, and recorded. -/
theorem mmap_fresh {k k' : Kern} {i : SyscallInput} {o : Outcome} (h : mmapSpec k i o k')
    (hok : ∀ e ev, o = .ret e ev → e.ret ≠ enomem) :
    ∃ a : Word, a.toNat % 4096 = 0 ∧ a.toNat + pageUp (i.arg 1) ≤ taskSize ∧
      (∀ p ∈ k.maps, disjointNat a.toNat (pageUp (i.arg 1)) p.1.toNat p.2) ∧
      o = .ret { ret := a, zeros := [(a, pageUp (i.arg 1))] } none ∧ (a, pageUp (i.arg 1)) ∈ k'.maps := by
  unfold mmapSpec at h
  split at h
  · rcases h with ⟨a, h1, h2, h3, rfl, rfl⟩ | ⟨rfl, -⟩
    · refine ⟨a, h1, h2, h3, rfl, ?_⟩
      unfold withProt; split <;> (try split) <;> exact List.mem_cons_self
    · exact absurd rfl (hok _ _ rfl)
  · exact h.elim

/-- Control: `munmap` of an unaligned address fails with EINVAL and unmaps nothing. -/
theorem munmap_unaligned {k k' : Kern} {i : SyscallInput} {o : Outcome} (h : (i.arg 0).toNat % 4096 ≠ 0)
    (hm : munmapSpec k i o k') : o = .ret { ret := einval } none ∧ k' = k := by
  have hc : ¬ ((i.arg 0).toNat % 4096 = 0 ∧ 0 < (i.arg 1).toNat) := fun ⟨h', _⟩ => h h'
  simp only [munmapSpec, hc, ↓reduceIte] at hm
  exact hm

/-- Control: mapping a file (fd 3) has no outcome either. -/
theorem mmap_file_none {k k' : Kern} {i : SyscallInput} {o : Outcome} (h : i.arg 4 = 3) :
    ¬ mmapSpec k i o k' := by
  have h4 : ¬ (i.arg 4 = -1) := by rw [h]; decide
  have hc : ¬ (i.arg 0 = 0 ∧ i.arg 3 = mapPrivateAnon ∧ i.arg 4 = -1 ∧ i.arg 5 = 0 ∧ 0 < (i.arg 1).toNat ∧
      (i.arg 2).toNat < 8) :=
    fun ⟨_, _, h', _⟩ => h4 h'
  intro hp
  unfold mmapSpec at hp
  simp only [hc, ↓reduceIte] at hp

end NoCompiler.Linux
