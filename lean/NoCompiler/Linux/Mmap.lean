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
* Every other `mmap` (a file, MAP_FIXED, an address hint), and `munmap`
  (215): NO outcome, fail closed, until the layer has partial memory.
* The protection bits are not modelled: our memory is total.
-/
namespace NoCompiler.Linux

def sysMmap : Word := 222
def sysMunmap : Word := 215
def mapPrivateAnon : Word := 0x22
def taskSize : Nat := 0x800000000000
def enomem : Word := -(BitVec.ofNat 64 12)

/-- `[a, a + n)` and `[b, b + m)` share no byte (as numbers; both below TASK_SIZE). -/
def disjointNat (a : Nat) (n : Nat) (b : Nat) (m : Nat) : Prop := a + n ≤ b ∨ b + m ≤ a

def mmapSpec (k : Kern) (i : SyscallInput) (o : Outcome) (k' : Kern) : Prop :=
  let len := pageUp (i.arg 1)
  if i.arg 0 = 0 ∧ i.arg 3 = mapPrivateAnon ∧ i.arg 4 = -1 ∧ i.arg 5 = 0 ∧ 0 < (i.arg 1).toNat then
    (∃ a : Word, a.toNat % 4096 = 0 ∧ a.toNat + len ≤ taskSize ∧
        (∀ p ∈ k.maps, disjointNat a.toNat len p.1.toNat p.2) ∧
        o = .ret { ret := a, zeros := [(a, len)] } none ∧ k' = { k with maps := (a, len) :: k.maps }) ∨
      (o = .ret { ret := enomem } none ∧ k' = k)
  else False

/-- The process layer with `mmap`; `munmap` has no outcome. -/
def procSpec2 (k : Kern) (i : SyscallInput) (o : Outcome) (k' : Kern) : Prop :=
  if i.sysno = sysMmap then mmapSpec k i o k'
  else if i.sysno = sysMunmap then False
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
    · exact ⟨a, h1, h2, h3, rfl, List.mem_cons_self⟩
    · exact absurd rfl (hok _ _ rfl)
  · exact h.elim

/-- Control: `munmap` has no outcome (fail closed). -/
theorem munmap_none {k k' : Kern} {i : SyscallInput} {o : Outcome} (h : i.sysno = sysMunmap) :
    ¬ procSpec2 k i o k' := by
  have hmm : sysMunmap ≠ sysMmap := by decide
  intro hp
  unfold procSpec2 at hp
  simp only [h, hmm, ↓reduceIte] at hp

/-- Control: mapping a file (fd 3) has no outcome either. -/
theorem mmap_file_none {k k' : Kern} {i : SyscallInput} {o : Outcome} (h : i.arg 4 = 3) :
    ¬ mmapSpec k i o k' := by
  have h4 : ¬ (i.arg 4 = -1) := by rw [h]; decide
  have hc : ¬ (i.arg 0 = 0 ∧ i.arg 3 = mapPrivateAnon ∧ i.arg 4 = -1 ∧ i.arg 5 = 0 ∧ 0 < (i.arg 1).toNat) :=
    fun ⟨_, _, h', _⟩ => h4 h'
  intro hp
  unfold mmapSpec at hp
  simp only [hc, ↓reduceIte] at hp

end NoCompiler.Linux
