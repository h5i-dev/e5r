import NoCompiler.Linux.Launch

/-
The Linux layer: page protections (decision 2026-11-21 Q5 (a), 13:18). The
mapped ranges carry overlays (`Kern.ro`, `Kern.noacc`, Linux/Fd.lean) that
`mmap`'s `prot` sets (`withProt`, Linux/Mmap.lean), `munmap` and a `brk`
shrink cut (`Kern.unmap`), and `mprotect` changes. Linux/Process.lean turns
them into the permission a load or a store needs.

* `mprotect(addr, len, prot)` (226), Linux v6.18.46 mm/mprotect.c
  do_mprotect_pkey: EINVAL for an unaligned `addr`; 0 and nothing changed
  for `len = 0`; with every page of `[addr, addr + PAGE_ALIGN(len))` mapped,
  0 and the range set to `prot`. A range not wholly mapped: no outcome (Linux
  returns ENOMEM after changing the pages before the hole; not modelled, so
  fail closed). A `prot` bit beyond READ/WRITE/EXEC: no outcome.
-/
namespace NoCompiler.Linux

def sysMprotect : Word := 226

/-- Every byte of `[a, a + n)` lies in a mapped range. -/
def Kern.covers (k : Kern) (a : Nat) (n : Nat) : Prop :=
  ∀ x, a ≤ x → x < a + n → ∃ p ∈ k.maps, p.1.toNat ≤ x ∧ x < p.1.toNat + p.2

def mprotectSpec (k : Kern) (i : SyscallInput) (o : Outcome) (k' : Kern) : Prop :=
  if (i.arg 2).toNat < 8 then
    if (i.arg 0).toNat % 4096 = 0 then
      if (i.arg 1).toNat = 0 then o = .ret { ret := 0 } none ∧ k' = k
      else k.covers (i.arg 0).toNat (pageUp (i.arg 1)) ∧
        o = .ret { ret := 0 } none ∧ k' = withProt (i.arg 2) (i.arg 0) (pageUp (i.arg 1)) k
    else o = .ret { ret := einval } none ∧ k' = k
  else False

def procSpec7 (k : Kern) (i : SyscallInput) (o : Outcome) (k' : Kern) : Prop :=
  if i.sysno = sysMprotect then mprotectSpec k i o k' else procSpec6 k i o k'

inductive ProcStep7 : State × Kern → State × Kern → Prop
  | step {s : State} {k k' : Kern} {o : Outcome} :
      procSpec7 k (SyscallInput.of s) o k' → ProcStep7 (s, k) (o.apply s, k')

theorem OldSys.ne7 {s : State} (h : OldSys s) : s.reg Reg.a7 ≠ sysMprotect := by
  rcases h with h | h | h | h <;> rw [h] <;> decide

theorem procSpec7_old {s : State} {k k' : Kern} {o : Outcome} (ho : OldSys s) :
    procSpec7 k (SyscallInput.of s) o k' ↔ procSpec6 k (SyscallInput.of s) o k' := by
  have hno : (SyscallInput.of s).sysno = s.reg Reg.a7 := rfl
  simp only [procSpec7, hno, ho.ne7, ↓reduceIte]

theorem ProcStep7.sys {s s' : State} {k k' : Kern} (h : ProcStep7 (s, k) (s', k'))
    (hp : s.reg Reg.a7 ≠ sysMprotect)
    (hr : s.reg Reg.a7 ≠ sysReadv) (hl : s.reg Reg.a7 ≠ sysLseek)
    (ho : s.reg Reg.a7 ≠ sysOpenat) (hf : s.reg Reg.a7 ≠ sysFstat)
    (hc : s.reg Reg.a7 ≠ sysClose) (hb : s.reg Reg.a7 ≠ sysBrk) (hm : s.reg Reg.a7 ≠ sysMmap)
    (hu : s.reg Reg.a7 ≠ sysMunmap) (hv : s.reg Reg.a7 ≠ sysWritev)
    (ht : s.reg Reg.a7 ≠ sysSetTidAddress) (hg : s.reg Reg.a7 ≠ sysRtSigprocmask)
    (hi : s.reg Reg.a7 ≠ sysIoctl) : Sys s s' := by
  cases h with
  | step h =>
    have hno : (SyscallInput.of s).sysno = s.reg Reg.a7 := rfl
    simp only [procSpec7, hno, hp, ↓reduceIte] at h
    exact ProcStep6.sys (ProcStep6.step h) hr hl ho hf hc hb hm hu hv ht hg hi

/-- At the trusted model's syscalls the kernel's memory state (mapped ranges
    and overlays) does not change. -/
theorem procSpec5_mem_old {s : State} {k k' : Kern} {o : Outcome} (ho : OldSys s)
    (h : procSpec5 k (SyscallInput.of s) o k') : k'.maps = k.maps ∧ k'.ro = k.ro ∧ k'.noacc = k.noacc := by
  obtain ⟨h1, h2, h3, -⟩ := ho.ne
  have hno : (SyscallInput.of s).sysno = s.reg Reg.a7 := rfl
  simp only [procSpec5, hno, h1, h2, h3, ↓reduceIte] at h
  split at h
  · split at h
    · rw [h.2]; exact ⟨rfl, rfl, rfl⟩
    · rw [procSpec4_old ho h]; exact ⟨rfl, rfl, rfl⟩
  · rw [procSpec4_old ho h]; exact ⟨rfl, rfl, rfl⟩

theorem ProcStep7.mem_old {s s' : State} {k k' : Kern} (h : ProcStep7 (s, k) (s', k'))
    (ho : OldSys s) : k'.maps = k.maps ∧ k'.ro = k.ro ∧ k'.noacc = k.noacc := by
  cases h with
  | step h =>
    exact procSpec5_mem_old ho ((procSpec6_old ho).1 ((procSpec7_old ho).1 h))

theorem procSpec7_exists {s s₁ : State} (k : Kern) (ho : OldSys s) (hy : Sys s s₁) :
    ∃ o k', procSpec7 k (SyscallInput.of s) o k' := by
  obtain ⟨o, k', h⟩ := procSpec6_exists k ho hy
  exact ⟨o, k', (procSpec7_old ho).2 h⟩

/-- `mprotect(a, n, PROT_READ)` on a mapped range makes it read-only. -/
theorem mprotect_ro {k k' : Kern} {i : SyscallInput} {o : Outcome} (hp : i.arg 2 = 1)
    (ha : (i.arg 0).toNat % 4096 = 0) (hn : (i.arg 1).toNat ≠ 0)
    (h : mprotectSpec k i o k') : (i.arg 0, pageUp (i.arg 1)) ∈ k'.ro := by
  have h8 : (i.arg 2).toNat < 8 := by rw [hp]; decide
  simp only [mprotectSpec, h8, ha, hn, ↓reduceIte] at h
  obtain ⟨-, -, rfl⟩ := h
  have hw : ¬ (i.arg 2 &&& protWrite ≠ 0) := by rw [hp]; decide
  have hr : i.arg 2 &&& protReadExec ≠ 0 := by rw [hp]; decide
  unfold withProt
  rw [if_neg hw, if_pos hr]
  exact List.mem_cons_self

/-- Control: an unaligned `mprotect` gives EINVAL and changes nothing. -/
theorem mprotect_unaligned {k k' : Kern} {i : SyscallInput} {o : Outcome} (h8 : (i.arg 2).toNat < 8)
    (ha : (i.arg 0).toNat % 4096 ≠ 0) (h : mprotectSpec k i o k') :
    o = .ret { ret := einval } none ∧ k' = k := by
  simp only [mprotectSpec, h8, ha, ↓reduceIte] at h
  exact h

end NoCompiler.Linux
