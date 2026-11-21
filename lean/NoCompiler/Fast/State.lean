import NoCompiler.Fast.Mem
import NoCompiler.Lemmas

/-
A flat machine state for proofs (docs/design/prior-art-others.md,
"Implementation plan", step 1).

`FState` keeps the 32 registers as a list (one slot each: writing a
register replaces its slot, so a run does not build a chain of writes) and
memory as word-level writes (`FMem`). `toState` is the trusted `State` it
stands for. `fexec` is `exec` on it, for every instruction but `ecall`, and
`exec_toState` is the one bridge: `exec` of the abstraction is the
abstraction of `fexec`. Nothing here is trusted and the trusted definitions
are unchanged.
-/
namespace NoCompiler.Fast

structure FState where
  regs : List Word
  pc : Word
  mem : FMem
  trace : List Event
  exit : Option Word

namespace FState

/-- The trusted state. Register r is slot r (x0 reads as zero in `State.reg`). -/
def toState (S : FState) : State :=
  { regs := fun r => S.regs.getD r.val 0, pc := S.pc, mem := S.mem.mem, trace := S.trace, exit := S.exit }

/-- The state has its 32 slots. -/
def WF (S : FState) : Prop := S.regs.length = 32

def reg (S : FState) (r : Reg) : Word := if r = 0 then 0 else S.regs.getD r.val 0
def setReg (S : FState) (r : Reg) (v : Word) : FState :=
  if r = 0 then S else { S with regs := S.regs.set r.val v }
def setPc (S : FState) (p : Word) : FState := { S with pc := p }
def ea (S : FState) (rs1 : Reg) (off : BitVec 12) : Word := S.reg rs1 + off.signExtend 64

theorem reg_toState (S : FState) (r : Reg) : S.toState.reg r = S.reg r := rfl

theorem WF.setReg {S : FState} (h : S.WF) (r : Reg) (v : Word) : (S.setReg r v).WF := by
  unfold FState.setReg WF at *; split
  · exact h
  · simpa using h

@[simp] theorem toState_pc (S : FState) : S.toState.pc = S.pc := rfl
@[simp] theorem toState_mem (S : FState) : S.toState.mem = S.mem.mem := rfl
@[simp] theorem toState_trace (S : FState) : S.toState.trace = S.trace := rfl
@[simp] theorem toState_exit (S : FState) : S.toState.exit = S.exit := rfl

theorem toState_setReg {S : FState} (h : S.WF) (r : Reg) (v : Word) :
    (S.setReg r v).toState = S.toState.setReg r v := by
  unfold FState.setReg State.setReg
  by_cases h0 : r = 0
  · simp [h0]
  · simp only [h0, ite_false]
    unfold toState
    simp only [State.mk.injEq, and_true]
    funext q
    unfold State.upd
    by_cases hq : q = r
    · subst hq
      have : q.val < S.regs.length := by unfold WF at h; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_self this]
    · have hv : r.val ≠ q.val := fun e => hq (Fin.ext e).symm
      simp [hq, List.getD_eq_getElem?_getD, List.getElem?_set_ne hv]

@[simp] theorem toState_setPc (S : FState) (p : Word) : (S.setPc p).toState = S.toState.setPc p := rfl
@[simp] theorem setReg_pc (S : FState) (r : Reg) (v : Word) : (S.setReg r v).pc = S.pc := by
  unfold FState.setReg; split <;> rfl
theorem ea_toState (S : FState) (rs1 : Reg) (off : BitVec 12) : NoCompiler.ea S.toState rs1 off = S.ea rs1 off := rfl

end FState

/-- `loadVal`, from the number the load reads. -/
def loadValN (op : LdOp) (n : Nat) : Word :=
  match op with
  | .lb => (BitVec.ofNat 8 n).signExtend 64
  | .lh => (BitVec.ofNat 16 n).signExtend 64
  | .lw => (BitVec.ofNat 32 n).signExtend 64
  | .ld => BitVec.ofNat 64 n
  | .lbu | .lhu | .lwu => BitVec.ofNat 64 n

theorem loadVal_eq (op : LdOp) (m : Word → Byte) (a : Word) :
    loadVal op m a = loadValN op (readLE m a op.width) := by
  cases op <;> rfl

open FState in
/-- `exec` on the flat state, for every instruction but `ecall` (where it is `none`, as `exec` is). -/
def fexec (i : Instr) (S : FState) : Option FState :=
  let next := S.pc + 4
  match i with
  | .lui rd imm => some ((S.setReg rd ((imm.setWidth 32 <<< 12).signExtend 64)).setPc next)
  | .auipc rd imm => some ((S.setReg rd (S.pc + (imm.setWidth 32 <<< 12).signExtend 64)).setPc next)
  | .jal rd off =>
    let t := S.pc + off.signExtend 64
    if aligned t 4 then some ((S.setReg rd next).setPc t) else none
  | .jalr rd rs1 off =>
    let t := (S.reg rs1 + off.signExtend 64) &&& ~~~1
    if aligned t 4 then some ((S.setReg rd next).setPc t) else none
  | .branch op rs1 rs2 off =>
    if evalBr op (S.reg rs1) (S.reg rs2) then
      (let t := S.pc + off.signExtend 64; if aligned t 4 then some (S.setPc t) else none)
    else some (S.setPc next)
  | .load op rd rs1 off =>
    let a := S.ea rs1 off
    if aligned a op.width then some ((S.setReg rd (loadValN op (S.mem.read a op.width))).setPc next)
    else none
  | .store op rs1 rs2 off =>
    let a := S.ea rs1 off
    if aligned a op.width then some ({ S with mem := S.mem.write a (S.reg rs2).toNat op.width }.setPc next)
    else none
  | .iop op rd rs1 imm => some ((S.setReg rd (evalI op (S.reg rs1) (imm.signExtend 64))).setPc next)
  | .addiw rd rs1 imm => some ((S.setReg rd (sext32 (S.reg rs1 + imm.signExtend 64))).setPc next)
  | .shift op rd rs1 sh => some ((S.setReg rd (evalSh op (S.reg rs1) sh.toNat)).setPc next)
  | .shiftw op rd rs1 sh => some ((S.setReg rd (evalShW op (S.reg rs1) sh.toNat)).setPc next)
  | .rop op rd rs1 rs2 => some ((S.setReg rd (evalR op (S.reg rs1) (S.reg rs2))).setPc next)
  | .rwop op rd rs1 rs2 => some ((S.setReg rd (evalRW op (S.reg rs1) (S.reg rs2))).setPc next)
  | .uop op rd rs1 => some ((S.setReg rd (evalU op (S.reg rs1))).setPc next)
  | .ecall => none

/-- The bridge, proved once: on a well-formed flat state, `exec` of the
    trusted state it stands for is the trusted state of `fexec`. -/
theorem exec_toState {S : FState} (h : S.WF) (i : Instr) :
    exec i S.toState = (fexec i S).map FState.toState := by
  have e1 : ∀ (r : Reg) (v : Word) (p : Word),
      (S.toState.setReg r v).setPc p = ((S.setReg r v).setPc p).toState := fun r v p => by
    rw [FState.toState_setPc, FState.toState_setReg h]
  cases i with
  | jal rd off =>
    simp only [exec, fexec, jumpTo, FState.toState_pc]
    by_cases hc : aligned (S.pc + off.signExtend 64) 4 <;> simp [hc, e1]
  | jalr rd rs1 off =>
    simp only [exec, fexec, jumpTo, FState.reg_toState, FState.toState_pc]
    by_cases hc : aligned ((S.reg rs1 + off.signExtend 64) &&& ~~~1) 4 <;> simp [hc, e1]
  | branch op rs1 rs2 off =>
    simp only [exec, fexec, jumpTo, FState.reg_toState, FState.toState_pc]
    by_cases hb : evalBr op (S.reg rs1) (S.reg rs2) = true
    · by_cases hc : aligned (S.pc + off.signExtend 64) 4 <;> simp [hb, hc]
    · simp [hb]
  | load op rd rs1 off =>
    simp only [exec, fexec, FState.ea_toState, FState.toState_pc, FState.toState_mem]
    by_cases hc : aligned (S.ea rs1 off) op.width
    · simp only [hc, ite_true, Option.map_some, loadVal_eq, ← FMem.read_eq, e1]
    · simp [hc]
  | store op rs1 rs2 off =>
    simp only [exec, fexec, FState.ea_toState, FState.reg_toState, FState.toState_pc, FState.toState_mem]
    by_cases hc : aligned (S.ea rs1 off) op.width
    · simp only [hc, ite_true, Option.map_some]; rfl
    · simp [hc]
  | ecall => simp [exec_ecall, fexec]
  | _ => simp only [exec, fexec, Option.map_some, FState.reg_toState, FState.toState_pc, e1]

end NoCompiler.Fast
