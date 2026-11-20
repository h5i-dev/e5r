import NoCompiler.Adequacy

/-
Function specifications (docs/isa/spec.md).

A `Spec α` is parameterised by `α`, the logical arguments (an array as a
list, a length, a base pointer). It gives a precondition, a postcondition on
return, an optional postcondition for a function that exits the process, the
memory it may read and write, and a stack bound.

`VerifiedImg c D entry spec` is the statement a function proof establishes:
called at `entry` with a return address outside its code `D`, a 16-byte
aligned sp and the precondition, every execution

* stays inside `D` until it returns to `ra` (or exits), and terminates;
* touches only `reads`, `writes` and `stack` bytes below sp, aligned;
* returns with sp, gp, tp and s0 to s11 as they were (`Preserved`), and the
  postcondition.

That the memory it does not own is unchanged on return is not part of the
definition; `VerifiedImg.frame` derives it, and `VerifiedImg.call` hands it to
the caller.
-/
namespace NoCompiler

/-- Registers a callee must give back unchanged: sp, gp, tp, s0 to s11. -/
def preservedRegs : List Reg := [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

def Preserved (s s' : State) : Prop := ∀ r ∈ preservedRegs, s'.reg r = s.reg r

/-- Registers outside `rs` hold what they held in `s0`: the frame of a
    straight-line or loop invariant. -/
def Same (s0 s : State) (rs : List Nat) : Prop := ∀ r : Reg, r.val ∉ rs → s.reg r = s0.reg r

theorem Same.preserved {s0 s : State} {rs : List Nat} (h : Same s0 s rs)
    (hrs : preservedRegs.all (fun r => !rs.contains r.val) = true) : Preserved s0 s := by
  intro r hr
  apply h r
  have := List.all_eq_true.1 hrs r hr
  simpa using this

theorem Same.refl (s : State) (rs : List Nat) : Same s s rs := fun _ _ => rfl

/-- Writing a register in `rs` keeps `Same`. -/
theorem Same.setReg {s0 s : State} {rs : List Nat} (h : Same s0 s rs) {q : Reg} (v : Word)
    (hq : q.val ∈ rs) : Same s0 (s.setReg q v) rs := by
  intro r hr
  have hne : r ≠ q := fun e => hr (by subst e; exact hq)
  rw [State.reg_setReg_other _ _ _ _ hne]
  exact h r hr

theorem Same.setPc {s0 s : State} {rs : List Nat} (h : Same s0 s rs) (p : Word) :
    Same s0 (s.setPc p) rs := h

theorem Same.emit {s0 s : State} {rs : List Nat} (h : Same s0 s rs) (e : Event) :
    Same s0 (s.emit e) rs := h

theorem Same.setMem {s0 s : State} {rs : List Nat} (h : Same s0 s rs) (m : Word → Byte) :
    Same s0 (s.setMem m) rs := h

/-- A syscall's result goes to a0. -/
theorem Same.sysRet {s0 s : State} {rs : List Nat} (h : Same s0 s rs) (v : Word)
    (h10 : 10 ∈ rs) : Same s0 (s.sysRet v) rs :=
  (h.setReg (q := 10) v h10).setPc _

structure Spec (α : Type) where
  pre : α → State → Prop
  /-- On return: the entry state, the state at the return address. -/
  post : α → State → State → Prop
  /-- If the function may end the process instead of returning. -/
  onExit : α → State → State → Prop := fun _ _ _ => False
  reads : α → State → List Region := fun _ _ => []
  writes : α → State → List Region := fun _ _ => []
  /-- Bytes of stack below the entry sp the function may use. -/
  stack : Nat := 0

namespace Spec
variable {α : Type}

def stackRegion (s : State) (n : Nat) : Region := ⟨s.reg Reg.sp - BitVec.ofNat 64 n, n⟩

def perm (sp : Spec α) (a : α) (s : State) : Perm :=
  { rd := sp.reads a s, wr := sp.writes a s ++ [stackRegion s sp.stack] }

/-- How a run of the function ends, seen from its entry state `s`. -/
def Done (sp : Spec α) (a : α) (s s' : State) : Prop :=
  (s'.exit = none ∧ s'.pc = s.reg Reg.ra ∧ Preserved s s' ∧ sp.post a s s') ∨
  (s'.exit ≠ none ∧ sp.onExit a s s')

end Spec

/-- The conditions under which a function may be entered. -/
structure Entry (D : Dom) (entry : Word) (s : State) : Prop where
  pc : s.pc = entry
  live : s.exit = none
  ret : ¬ D.mem (s.reg Reg.ra)
  retAligned : aligned (s.reg Reg.ra) 4
  sp : aligned (s.reg Reg.sp) 16

def VerifiedImg {α : Type} (c : Code) (D : Dom) (entry : Word) (sp : Spec α) : Prop :=
  ∀ a s, Entry D entry s → sp.pre a s → Exec c (sp.perm a s) D (sp.Done a s) s

/-! ## Using a verified function -/

namespace Region
/-- `r` lies inside `r'`. -/
def within (r r' : Region) : Prop := (r.base - r'.base).toNat + r.size ≤ r'.size

theorem covers_of_within {r r' : Region} {a : Word} {n : Nat} (h : r.covers a n)
    (hw : r.within r') : r'.covers a n := by
  unfold covers within at *
  have e : a - r'.base = (a - r.base) + (r.base - r'.base) := by bv_omega
  rw [e, BitVec.toNat_add]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.mod_le _ _) n) (by omega)

theorem within_refl (r : Region) : r.within r := by simp [within]
end Region

/-- `P ≤ Q` from region containment, the form calls need. -/
theorem Perm.le_of {P Q : Perm}
    (hr : ∀ r ∈ P.rd, ∃ r' ∈ Q.rd ++ Q.wr, r.within r')
    (hw : ∀ r ∈ P.wr, ∃ r' ∈ Q.wr, r.within r') : P.le Q := by
  constructor
  · rintro a n (h0 | ⟨r, hr', hc⟩)
    · exact .inl h0
    · right
      rcases List.mem_append.1 hr' with h | h
      · obtain ⟨r', h', hw'⟩ := hr r h; exact ⟨r', h', Region.covers_of_within hc hw'⟩
      · obtain ⟨r', h', hw'⟩ := hw r h
        exact ⟨r', List.mem_append.2 (.inr h'), Region.covers_of_within hc hw'⟩
  · rintro a n (h0 | ⟨r, hr', hc⟩)
    · exact .inl h0
    · obtain ⟨r', h', hw'⟩ := hw r hr'; exact .inr ⟨r', h', Region.covers_of_within hc hw'⟩

variable {c : Code} {α : Type}

/-- The frame property of a verified function. -/
theorem VerifiedImg.frame {D : Dom} {entry : Word} {sp : Spec α} (h : VerifiedImg c D entry sp)
    (a : α) (s : State) (he : Entry D entry s) (hpre : sp.pre a s) :
    Exec c (sp.perm a s) D
      (fun s' => sp.Done a s s' ∧ ∀ x, ¬ (sp.perm a s).writable x → s'.mem x = s.mem x) s :=
  Reach.mono (fun _ ⟨⟨hf, hd⟩, hm⟩ => ⟨hf, hd, hm⟩) (Reach.frame (h a s he hpre))

/-- The call rule: inside a caller with region `D` and permission `P`, a call
    to a verified function continues from every way the callee can end. -/
theorem VerifiedImg.call {Dg D : Dom} {entry : Word} {sp : Spec α} {P : Perm}
    {Q : State → Prop} {s : State} (hg : VerifiedImg c Dg entry sp) (a : α)
    (he : Entry Dg entry s) (hpre : sp.pre a s) (hD : Dg.sub D) (hP : (sp.perm a s).le P)
    (k : ∀ s', sp.Done a s s' → (∀ x, ¬ (sp.perm a s).writable x → s'.mem x = s.mem x) →
      Reach c P D Q s') : Reach c P D Q s :=
  Reach.bind (hg.frame a s he hpre) hP hD (fun s' ⟨_, hd, hm⟩ => k s' hd hm)

/-- What a verified function guarantees on the machine, from a loaded image:
    the three theorems of NoCompiler/Adequacy.lean, specialised. -/
theorem VerifiedImg.hw {D : Dom} {entry : Word} {sp : Spec α} (h : VerifiedImg c D entry sp)
    (a : α) (s : State) (he : Entry D entry s) (hpre : sp.pre a s) (hl : c.Loaded s.mem)
    (hp : Protected c (sp.perm a s)) (hb : aligned c.base 4) :
    (∀ t, HwRun D s t → D.mem t.pc → t.exit = none →
      (∃ t', HwStep t t') ∧ ∀ t', HwStep t t' → Step c (sp.perm a s) t t') ∧
    (∀ t, HwRun D s t → Final D t → sp.Done a s t) ∧
    ¬ ∃ f : Nat → State, f 0 = s ∧ ∀ n, D.mem (f n).pc ∧ HwStep (f n) (f (n + 1)) :=
  ⟨fun _ hr hd hx => (h a s he hpre).hw_safe hl hp hb hr hd hx,
   fun _ hr hf => (h a s he hpre).hw_final hl hp hr hf,
   (h a s he hpre).hw_terminates hl hp⟩

end NoCompiler
