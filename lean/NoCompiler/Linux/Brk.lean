import NoCompiler.Linux.Fd

/-
The Linux layer, `brk` (214), after LPS `brk_spec` (theories/LinuxProcessSem/
Sys/Mm/Mmap.v#L662, `brk_r_ok` #L397, `brk_zeros` #L211; Linux v6.18.46
mm/mmap.c SYSCALL_DEFINE1(brk)).

* A query (`req = 0`) or a request below the break's start: the break,
  unchanged.
* A grow (`req ≥ brk`): the new break `req`, with the pages
  [PAGE_ALIGN(brk), PAGE_ALIGN(req)) zero-filled; or failure, the old break.
  LPS also refuses a grow that would meet another mapping or exceed the memory
  budget; here such a grow may still succeed. That over-approximates Linux's
  outcomes, which is sound for proofs that hold for every outcome.
* A grow records its new pages in `Kern.maps`, so the process may touch them
  (Linux/Process.lean).
* A shrink (`startBrk ≤ req < brk`): the break `req`, with
  [PAGE_ALIGN(req), PAGE_ALIGN(brk)) cut out of `Kern.maps` (LPS
  `brk_unmaps`), so a later access there faults; or failure.
-/
namespace NoCompiler.Linux

def sysBrk : Word := 214

def pageUp (x : Word) : Nat := (x.toNat + 4095) / 4096 * 4096

/-- The outcomes of `brk(req)` and the next kernel state. -/
def brkSpec (k : Kern) (req : Word) (o : Outcome) (k' : Kern) : Prop :=
  if req = 0 ∨ req.toNat < k.startBrk.toNat then
    o = .ret { ret := k.brk } none ∧ k' = k
  else if req.toNat < k.brk.toNat then
    (o = .ret { ret := req } none ∧
      k' = { k.unmap (BitVec.ofNat 64 (pageUp req)) (pageUp k.brk - pageUp req) with brk := req }) ∨
    (o = .ret { ret := k.brk } none ∧ k' = k)
  else
    (o = .ret { ret := req, zeros := [(BitVec.ofNat 64 (pageUp k.brk), pageUp req - pageUp k.brk)] } none ∧
      k' = { k with brk := req,
                    maps := (BitVec.ofNat 64 (pageUp k.brk), pageUp req - pageUp k.brk) :: k.maps }) ∨
    (o = .ret { ret := k.brk } none ∧ k' = k)

/-- The process layer so far: `brk`, then the fd table and the basic calls. -/
def procSpec (k : Kern) (i : SyscallInput) (o : Outcome) (k' : Kern) : Prop :=
  if i.sysno = sysBrk then brkSpec k (i.arg 0) o k' else fdSpec k i o k'

inductive ProcStep : State × Kern → State × Kern → Prop
  | step {s : State} {k k' : Kern} {o : Outcome} :
      procSpec k (SyscallInput.of s) o k' → ProcStep (s, k) (o.apply s, k')

/-- At every syscall but `close` and `brk`, a step is a step of `Sys`. -/
theorem ProcStep.sys {s s' : State} {k k' : Kern} (h : ProcStep (s, k) (s', k'))
    (hc : s.reg Reg.a7 ≠ sysClose) (hb : s.reg Reg.a7 ≠ sysBrk) : Sys s s' := by
  cases h with
  | step h =>
    have hno : (SyscallInput.of s).sysno = s.reg Reg.a7 := rfl
    simp only [procSpec, hno, hb, ↓reduceIte] at h
    exact FdStep.sys (FdStep.step h) hc

/-- A query returns the break and changes nothing. -/
theorem brk_query {k k' : Kern} {o : Outcome} (h : brkSpec k 0 o k') :
    o = .ret { ret := k.brk } none ∧ k' = k := by
  simpa [brkSpec] using h

/-- A grow either fails or succeeds with exactly the new pages zero-filled. -/
theorem brk_grow {k k' : Kern} {req : Word} {o : Outcome} (h0 : req ≠ 0)
    (hs : k.startBrk.toNat ≤ req.toNat) (hg : k.brk.toNat ≤ req.toNat) (h : brkSpec k req o k') :
    (o = .ret { ret := req, zeros := [(BitVec.ofNat 64 (pageUp k.brk), pageUp req - pageUp k.brk)] } none ∧
      k'.brk = req) ∨ (o = .ret { ret := k.brk } none ∧ k' = k) := by
  have h1 : ¬ (req = 0 ∨ req.toNat < k.startBrk.toNat) := by
    rintro (h | h)
    · exact h0 h
    · omega
  have h2 : ¬ req.toNat < k.brk.toNat := by omega
  simp only [brkSpec, h1, h2, ↓reduceIte] at h
  rcases h with ⟨ho, rfl⟩ | h
  · exact .inl ⟨ho, rfl⟩
  · exact .inr h

/-- A shrink either fails or unmaps the freed pages. -/
theorem brk_shrink {k k' : Kern} {req : Word} {o : Outcome} (h0 : req ≠ 0)
    (hs : k.startBrk.toNat ≤ req.toNat) (hlt : req.toNat < k.brk.toNat) (h : brkSpec k req o k') :
    (o = .ret { ret := req } none ∧
      k'.maps = unmapRanges k.maps (BitVec.ofNat 64 (pageUp req)) (pageUp k.brk - pageUp req)) ∨
    (o = .ret { ret := k.brk } none ∧ k' = k) := by
  have h1 : ¬ (req = 0 ∨ req.toNat < k.startBrk.toNat) := by
    rintro (h | h)
    · exact h0 h
    · omega
  simp only [brkSpec, h1, hlt, ↓reduceIte] at h
  rcases h with ⟨ho, rfl⟩ | h
  · exact .inl ⟨ho, rfl⟩
  · exact .inr h

end NoCompiler.Linux
