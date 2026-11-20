import NoCompiler.Env

/-
Two step relations and the predicate proofs are stated with.

`HwStep` is the machine: fetch the word at pc from memory, decode, execute
(NoCompiler/Machine.lean) or hand to the kernel (NoCompiler/Env.lean). It is the relation
the theorems in NoCompiler/Adequacy.lean are about.

`Step c P` is what a proof steps through. It differs from `HwStep` in two
ways, both of which make it smaller:

* the instruction comes from the code image `c` (the `.text` bytes of the
  binary), not from memory, so a proof does not carry the code around in its
  memory assertions;
* every load, store and syscall buffer has to lie in the permission `P`.

`Reach c P D Q s` says: every execution from `s` reaches a state satisfying
`Q`, and until it does it stays in the code region `D`, never faults, never
reaches an instruction outside the profile, and only touches memory `P`
allows. It is inductive, so every execution is finite: termination is part
of every result. `Exec` is `Reach` stopped at the first exit from `D`, which
is how a function's return is observed.
-/
namespace NoCompiler

/-! ## Regions and permissions -/

/-- `size` bytes from `base`, wrapping at 2^64. -/
structure Region where
  base : Word
  size : Nat

namespace Region
def mem (r : Region) (x : Word) : Prop := (x - r.base).toNat < r.size
/-- The `n` bytes from `a` all lie in `r`. -/
def covers (r : Region) (a : Word) (n : Nat) : Prop := (a - r.base).toNat + n ≤ r.size
end Region

structure Perm where
  /-- Readable only. -/
  rd : List Region
  /-- Readable and writable. -/
  wr : List Region

namespace Perm
def canRead (P : Perm) (a : Word) (n : Nat) : Prop :=
  n = 0 ∨ ∃ r ∈ P.rd ++ P.wr, r.covers a n
def canWrite (P : Perm) (a : Word) (n : Nat) : Prop :=
  n = 0 ∨ ∃ r ∈ P.wr, r.covers a n
def writable (P : Perm) (x : Word) : Prop := ∃ r ∈ P.wr, r.mem x

/-- `P` allows no more than `Q`. -/
structure le (P Q : Perm) : Prop where
  read : ∀ a n, P.canRead a n → Q.canRead a n
  write : ∀ a n, P.canWrite a n → Q.canWrite a n

theorem le_refl (P : Perm) : P.le P := ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem le_trans {P Q R : Perm} (h1 : P.le Q) (h2 : Q.le R) : P.le R :=
  ⟨fun a n h => h2.read a n (h1.read a n h), fun a n h => h2.write a n (h1.write a n h)⟩

theorem canRead_of_canWrite {P : Perm} {a : Word} {n : Nat} (h : P.canWrite a n) :
    P.canRead a n := by
  rcases h with h | ⟨r, hr, hc⟩
  · exact .inl h
  · exact .inr ⟨r, List.mem_append.2 (.inr hr), hc⟩

/-- Everything; what the hardware allows a user process, as far as nocompiler models it. -/
def top : Perm := { rd := [], wr := [⟨0, 2 ^ 64⟩] }
end Perm

/-- What an instruction at state `s` needs from the permission. -/
def SysOk (P : Perm) (s : State) : Prop :=
  (s.reg Reg.a7 = sysWrite → P.canRead (s.reg Reg.a1) (s.reg Reg.a2).toNat) ∧
  (s.reg Reg.a7 = sysRead → P.canWrite (s.reg Reg.a1) (s.reg Reg.a2).toNat)

def InstrOk (P : Perm) : Instr → State → Prop
  | .load op _ rs1 off, s => P.canRead (ea s rs1 off) op.width
  | .store op rs1 _ off, s => P.canWrite (ea s rs1 off) op.width
  | .ecall, s => SysOk P s
  | _, _ => True

theorem InstrOk.mono {P Q : Perm} (h : P.le Q) : ∀ {i s}, InstrOk P i s → InstrOk Q i s
  | .load .., _, hi => h.read _ _ hi
  | .store .., _, hi => h.write _ _ hi
  | .ecall, _, ⟨hw, hr⟩ => ⟨fun e => h.read _ _ (hw e), fun e => h.write _ _ (hr e)⟩
  | .lui .., _, _ | .auipc .., _, _ | .jal .., _, _ | .jalr .., _, _ | .branch .., _, _
  | .iop .., _, _ | .addiw .., _, _ | .shift .., _, _ | .shiftw .., _, _ | .rop .., _, _
  | .rwop .., _, _ | .uop .., _, _ => trivial

/-! ## The code image -/

/-- The `.text` of a binary: 32-bit words from `base`. -/
structure Code where
  base : Word
  words : Array (BitVec 32)

namespace Code
def fetch (c : Code) (pc : Word) : Option (BitVec 32) :=
  let off := (pc - c.base).toNat
  if off % 4 = 0 then c.words[off / 4]? else none

def instr (c : Code) (pc : Word) : Option Instr := (c.fetch pc).bind decode

/-- `x` is one of the code bytes. -/
def mem (c : Code) (x : Word) : Prop := (x - c.base).toNat < 4 * c.words.size

/-- Memory holds the image: what the loader establishes before the first
    instruction runs. -/
def Loaded (c : Code) (m : Word → Byte) : Prop :=
  ∀ pc w, c.fetch pc = some w → (read32 m pc).setWidth 32 = w
end Code

/-! ## Step relations -/

def fetchMem (m : Word → Byte) (pc : Word) : BitVec 32 := (read32 m pc).setWidth 32

/-- The machine. -/
inductive HwStep : State → State → Prop
  | exec {s s' : State} {i : Instr} :
      s.exit = none → aligned s.pc 4 → decode (fetchMem s.mem s.pc) = some i →
      exec i s = some s' → HwStep s s'
  | sys {s s' : State} :
      s.exit = none → aligned s.pc 4 → decode (fetchMem s.mem s.pc) = some .ecall →
      Sys s s' → HwStep s s'

/-- What proofs step through: instructions from the image, accesses within `P`. -/
inductive Step (c : Code) (P : Perm) : State → State → Prop
  | exec {s s' : State} {i : Instr} :
      s.exit = none → c.instr s.pc = some i → InstrOk P i s → exec i s = some s' → Step c P s s'
  | sys {s s' : State} :
      s.exit = none → c.instr s.pc = some .ecall → SysOk P s → Sys s s' → Step c P s s'

theorem exec_ecall (s : State) : exec .ecall s = none := by unfold exec; rfl

/-- The instruction at `s` is allowed by `P` whenever some `P`-step exists. -/
theorem Step.instrOk {c P s s'} (h : Step c P s s') :
    ∃ i, c.instr s.pc = some i ∧ InstrOk P i s ∧ s.exit = none := by
  cases h with
  | exec he hi hok _ => exact ⟨_, hi, hok, he⟩
  | sys he hi hok _ => exact ⟨_, hi, hok, he⟩

/-- Steps under a larger permission are steps under any permission that
    already allows the instruction at `s`. -/
theorem Step.restrict {c P Q s s₁ s'} (h : Step c P s s₁) (h' : Step c Q s s') : Step c P s s' := by
  obtain ⟨i, hi, hok, _⟩ := h.instrOk
  cases h' with
  | exec he hi' _ hx => rw [hi] at hi'; cases hi'; exact .exec he hi hok hx
  | sys he hi' _ hy => rw [hi] at hi'; cases hi'; exact .sys he hi hok hy

theorem Step.mono {c P Q s s'} (hle : P.le Q) (h : Step c P s s') : Step c Q s s' := by
  cases h with
  | exec he hi hok hx => exact .exec he hi (InstrOk.mono hle hok) hx
  | sys he hi hok hy =>
    exact .sys he hi (InstrOk.mono (i := .ecall) hle hok) hy

/-! ## Reach and Exec -/

/-- A code region, as a list of (start, length in bytes) ranges. Decidable,
    so `D pc` for a concrete pc is settled by `decide`. -/
abbrev Dom := List (Word × Nat)

def Dom.mem (D : Dom) (x : Word) : Prop := D.any (fun r => decide ((x - r.1).toNat < r.2)) = true

instance (D : Dom) (x : Word) : Decidable (D.mem x) := inferInstanceAs (Decidable (_ = _))

def Dom.sub (D E : Dom) : Prop := ∀ x, D.mem x → E.mem x

/-- Every range of `D` is one of `E`'s: decidable, so `by decide` settles it
    for the regions `nocompiler export` writes. -/
theorem Dom.sub_of_ranges {D E : Dom} (h : D.all (fun r => E.contains r) = true) : D.sub E := by
  intro x hx
  unfold Dom.mem at *
  obtain ⟨r, hr, hx⟩ := List.any_eq_true.1 hx
  exact List.any_eq_true.2 ⟨r, List.elem_iff.1 (List.all_eq_true.1 h r hr), hx⟩

inductive Reach (c : Code) (P : Perm) (D : Dom) (Q : State → Prop) : State → Prop
  | done {s : State} : Q s → Reach c P D Q s
  | step {s : State} :
      D.mem s.pc → (∃ s', Step c P s s') → (∀ s', Step c P s s' → Reach c P D Q s') →
      Reach c P D Q s

/-- Left the region, or ended the process. -/
def Final (D : Dom) (s : State) : Prop := ¬ D.mem s.pc ∨ s.exit ≠ none

/-- Run inside `D` until the first state outside it (or exit); `Q` holds there. -/
def Exec (c : Code) (P : Perm) (D : Dom) (Q : State → Prop) (s : State) : Prop :=
  Reach c P D (fun s => Final D s ∧ Q s) s

namespace Reach
variable {c : Code} {P : Perm} {D : Dom}

theorem mono {Q Q' : State → Prop} (hq : ∀ s, Q s → Q' s) {s} (h : Reach c P D Q s) :
    Reach c P D Q' s := by
  induction h with
  | done hq' => exact .done (hq _ hq')
  | step hd hex _ ih => exact .step hd hex ih

/-- Sequential composition, possibly into a larger region and permission:
    the rule for calls as well as for straight-line code. -/
theorem bind {P₁ P₂ : Perm} {D₁ D₂ : Dom} {Q₁ Q₂ : State → Prop} {s}
    (h : Reach c P₁ D₁ Q₁ s) (hP : P₁.le P₂) (hD : D₁.sub D₂)
    (k : ∀ s', Q₁ s' → Reach c P₂ D₂ Q₂ s') : Reach c P₂ D₂ Q₂ s := by
  induction h with
  | done hq => exact k _ hq
  | step hd hex _ ih =>
    obtain ⟨s₁, h₁⟩ := hex
    exact .step (hD _ hd) ⟨s₁, h₁.mono hP⟩ (fun s' h' => ih s' (h₁.restrict h'))

theorem trans {Q₁ Q₂ : State → Prop} {s} (h : Reach c P D Q₁ s)
    (k : ∀ s', Q₁ s' → Reach c P D Q₂ s') : Reach c P D Q₂ s :=
  bind h (Perm.le_refl P) (fun _ h => h) k

/-- Carry an invariant of every step into the goal. -/
theorem inv {Q I : State → Prop} (hI : ∀ u u', I u → Step c P u u' → I u') {s}
    (h : Reach c P D Q s) (hs : I s) : Reach c P D (fun u => Q u ∧ I u) s := by
  induction h with
  | done hq => exact .done ⟨hq, hs⟩
  | step hd hex _ ih => exact .step hd hex (fun s' h' => ih s' h' (hI _ _ hs h'))

/-- The loop rule: an invariant `I` at the loop head and a measure `μ` that
    every trip around the loop decreases. -/
theorem loop {Q : State → Prop} (I : State → Prop) (μ : State → Nat)
    (body : ∀ s, I s → Reach c P D (fun s' => Q s' ∨ (I s' ∧ μ s' < μ s)) s) :
    ∀ s, I s → Reach c P D Q s := by
  intro s hs
  induction hm : μ s using Nat.strongRecOn generalizing s with
  | _ n ih =>
    refine trans (body s hs) ?_
    rintro s' (hq | ⟨hi, hlt⟩)
    · exact .done hq
    · exact ih _ (hm ▸ hlt) s' hi rfl

/-- One state of `Option State` reaches `Q`; `none` (a fault) never does. -/
def opt (c : Code) (P : Perm) (D : Dom) (Q : State → Prop) : Option State → Prop
  | none => False
  | some s => Reach c P D Q s

@[simp] theorem opt_some {Q s} : opt c P D Q (some s) = Reach c P D Q s := rfl
@[simp] theorem opt_none {Q} : opt c P D Q none = False := rfl

-- Never unfolded by unification: a goal `opt .. (exec i s)` with a symbolic
-- state would otherwise be reduced through `exec` into Nat arithmetic.
attribute [irreducible] opt

/-- Step over one instruction other than ECALL. -/
theorem exec_step {Q : State → Prop} {s : State} {i : Instr}
    (hd : D.mem s.pc) (hx : s.exit = none) (hi : c.instr s.pc = some i) (hok : InstrOk P i s)
    (h : opt c P D Q (exec i s)) : Reach c P D Q s := by
  cases hxs : exec i s with
  | none => rw [hxs, opt_none] at h; exact h.elim
  | some s₁ =>
    rw [hxs, opt_some] at h
    refine .step hd ⟨s₁, .exec hx hi hok hxs⟩ (fun s' h' => ?_)
    cases h' with
    | exec _ hi' _ hx' => rw [hi] at hi'; cases hi'; rw [hxs] at hx'; cases hx'; exact h
    | sys _ hi' _ _ => rw [hi] at hi'; cases hi'; exact absurd hxs (by simp [exec_ecall])

/-- Step over an ECALL: every outcome the environment allows has to reach `Q`. -/
theorem sys_step {Q : State → Prop} {s : State}
    (hd : D.mem s.pc) (hx : s.exit = none) (hi : c.instr s.pc = some .ecall) (hok : SysOk P s)
    (hex : ∃ s', Sys s s') (h : ∀ s', Sys s s' → Reach c P D Q s') : Reach c P D Q s := by
  obtain ⟨s₁, h₁⟩ := hex
  refine .step hd ⟨s₁, .sys hx hi hok h₁⟩ (fun s' h' => ?_)
  cases h' with
  | exec _ hi' _ hx' => rw [hi] at hi'; cases hi'; simp [exec_ecall] at hx'
  | sys _ _ _ hy => exact h _ hy

end Reach

namespace Exec
variable {c : Code} {P : Perm} {D : Dom}

theorem mono {Q Q' : State → Prop} (hq : ∀ s, Q s → Q' s) {s} (h : Exec c P D Q s) :
    Exec c P D Q' s := Reach.mono (fun _ ⟨hf, h⟩ => ⟨hf, hq _ h⟩) h

/-- A final state satisfying `Q` ends the run. -/
theorem final {Q : State → Prop} {s} (hf : Final D s) (hq : Q s) : Exec c P D Q s :=
  .done ⟨hf, hq⟩

end Exec

end NoCompiler
