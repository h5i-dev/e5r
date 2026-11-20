import NoCompiler.Attr
import NoCompiler.Spec

/-
Proof automation: the `nocompiler` simp set and the step tactics. Nothing here is
trusted; a tactic that does the wrong thing produces a proof the kernel
rejects.

* `nocompiler_step` steps over one instruction other than ECALL. It looks the
  instruction up in the image (by evaluation), discharges "pc is in the
  region" and "not exited", proves the permission side condition when the
  instruction has none, and leaves the successor state normalised. Extra
  rewrite facts, typically `hpc : s.pc = ...`, go in brackets.
* `nocompiler_steps n` is `nocompiler_step` n times.
* `nocompiler_norm` is the normaliser on its own.

A conditional branch leaves an `if` on its condition; `split` takes it apart.
A load or store leaves its alignment `if` and its permission goal.
-/
namespace NoCompiler

@[simp] theorem State.setReg_zero (s : State) (v : Word) : s.setReg 0 v = s := by
  simp [State.setReg]

theorem and_not_one_of_aligned {x : Word} (h : aligned x 4) : x &&& ~~~1#64 = x := by
  unfold aligned at h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not]
  by_cases h0 : i = 0
  · subst h0
    have : x.getLsbD 0 = false := by
      rw [BitVec.getLsbD, Nat.testBit_zero]; simp; omega
    simpa [BitVec.getLsbD_eq_getElem] using this
  · simp [h0, hi]

@[simp] theorem sysRet_reg (s : State) (r : Word) (q : Reg) :
    (s.sysRet r).reg q = (s.setReg Reg.a0 r).reg q := rfl

theorem ret_mask {x : Word} (h : aligned x 4) : x &&& 0xfffffffffffffffe#64 = x :=
  and_not_one_of_aligned h

@[simp] theorem State.setPc_setPc (s : State) (p q : Word) : (s.setPc p).setPc q = s.setPc q := rfl

/-! The normal form of a state the step tactics keep: register writes, then
one memory, then one pc, so that a memory or pc overwritten by a later step
does not stay inside the term. -/

theorem State.setMem_setMem (s : State) (m m' : Word → Byte) :
    (s.setMem m).setMem m' = s.setMem m' := rfl
theorem State.setPc_setMem (s : State) (p : Word) (m : Word → Byte) :
    (s.setPc p).setMem m = (s.setMem m).setPc p := rfl
theorem State.setReg_setPc (s : State) (p : Word) (r : Reg) (v : Word) :
    (s.setPc p).setReg r v = (s.setReg r v).setPc p := by
  unfold setReg setPc; split <;> rfl
theorem State.setReg_setMem (s : State) (m : Word → Byte) (r : Reg) (v : Word) :
    (s.setMem m).setReg r v = (s.setReg r v).setMem m := by
  unfold setReg setMem; split <;> rfl

attribute [nocompiler_state] State.setPc_setPc State.setMem_setMem State.setPc_setMem State.setReg_pc State.setReg_mem State.setReg_trace
  State.setReg_exit State.setPc_pc State.setPc_mem State.setPc_trace State.setPc_exit State.setPc_reg
  State.setMem_pc State.setMem_mem State.setMem_trace State.setMem_exit State.setMem_reg
  State.emit_pc State.emit_mem State.emit_trace State.emit_exit State.emit_reg
  State.halt_pc State.halt_mem State.halt_trace State.halt_exit State.halt_reg
  State.reg_zero State.setReg_zero State.reg_setReg_same State.reg_setReg_other
  sysRet_pc sysRet_mem sysRet_trace sysRet_exit sysRet_reg Reach.opt_some Reach.opt_none
  ite_true ite_false reduceIte

attribute [nocompiler_sem] exec jumpTo ea evalI evalR evalRW evalU evalSh evalShW evalBr loadVal
  LdOp.width StOp.width InstrOk

attribute [nocompiler_lit] BitVec.reduceNeg BitVec.reduceNot BitVec.reduceAnd BitVec.reduceOr
  BitVec.reduceXOr BitVec.reduceAdd BitVec.reduceMul BitVec.reduceSub BitVec.reduceUMod
  BitVec.reduceUDiv BitVec.reduceShiftLeft BitVec.reduceUShiftRight BitVec.reduceSShiftRight
  BitVec.reduceHShiftLeft BitVec.reduceHShiftRight BitVec.reduceRotateLeft
  BitVec.reduceRotateRight BitVec.reduceToNat BitVec.reduceOfNat BitVec.reduceEq BitVec.reduceNe
  BitVec.reduceBEq BitVec.reduceBNe BitVec.reduceULT BitVec.reduceSLT BitVec.reduceSetWidth
  BitVec.reduceZeroExtend BitVec.reduceSignExtend BitVec.reduceAllOnes
  Fin.isValue Nat.reduceMod Nat.reduceDiv Nat.reduceAdd Nat.reduceMul Nat.reduceSub
  BitVec.add_zero BitVec.zero_add

/-- Normalise the goal (or `at h`): the four passes, each allowed to make no
    progress, and none an error once the goal is closed. -/
syntax "nocompiler_norm" (" [" Lean.Parser.Tactic.simpArg,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| nocompiler_norm) => `(tactic| nocompiler_norm [])
  | `(tactic| nocompiler_norm $loc:location) => `(tactic| nocompiler_norm [] $loc:location)
  | `(tactic| nocompiler_norm [$ts,*]) =>
    `(tactic| (
      all_goals (try simp only [nocompiler_sem])
      all_goals (try simp (config := { decide := true }) only [nocompiler_state, nocompiler_image, $ts,*])
      all_goals (try simp only [nocompiler_lit])
      all_goals (try simp (config := { decide := true }) only [nocompiler_state, nocompiler_image, $ts,*])))
  | `(tactic| nocompiler_norm [$ts,*] $loc:location) =>
    `(tactic| (
      (try simp only [nocompiler_sem] $loc:location)
      (try simp (config := { decide := true }) only [nocompiler_state, nocompiler_image, $ts,*] $loc:location)
      (try simp only [nocompiler_lit] $loc:location)
      (try simp (config := { decide := true }) only [nocompiler_state, nocompiler_image, $ts,*] $loc:location)))

syntax "nocompiler_step" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic
macro_rules
  | `(tactic| nocompiler_step) => `(tactic| nocompiler_step [])
  | `(tactic| nocompiler_step [$ts,*]) => `(tactic| (
      refine Reach.exec_step (i := ?i) ?hd ?hx ?hi ?hok ?h
      case hi => (try nocompiler_norm [$ts,*]) <;> rfl
      case hd => (try nocompiler_norm [$ts,*]) <;> decide
      case hx => (try nocompiler_norm [$ts,*]) <;> assumption
      case' hok => (try nocompiler_norm [$ts,*]) <;> (try trivial)
      case' h => (try nocompiler_norm [$ts,*])
      rotate_left))

/-- Close `Same s0 s' rs` where `s'` is `s` after register writes in `rs`
    and pc updates, from a hypothesis `Same s0 s rs`. -/
macro "nocompiler_same" : tactic => `(tactic| (
  repeat (first
    | with_reducible refine Same.setPc ?_ _
    | with_reducible refine Same.setMem ?_ _
    | with_reducible refine Same.emit ?_ _
    | with_reducible refine Same.sysRet ?_ _ (by decide)
    | with_reducible refine Same.setReg ?_ _ (by decide))
  first | with_reducible assumption | with_reducible exact Same.refl _ _))

syntax "nocompiler_steps" num (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic
macro_rules
  | `(tactic| nocompiler_steps $n) => `(tactic| nocompiler_steps $n [])
  | `(tactic| nocompiler_steps $n [$ts,*]) => do
    let mut t ← `(tactic| skip)
    for _ in [0:n.getNat] do
      t ← `(tactic| ($t; nocompiler_step [$ts,*]))
    return t

end NoCompiler
