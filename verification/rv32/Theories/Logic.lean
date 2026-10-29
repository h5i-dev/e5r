/-
  Program logic over the platform semantics: deterministic step sequences,
  the fetch/decode/execute bridge, and frame lemmas for registers, CSRs and
  RAM. Original e5r code, Apache-2.0.
-/
import Theories.Platform

set_option linter.constructorNameAsVariable false

namespace E5R

variable {B : Board} {img : List Segment}

/-! ## Deterministic steps

An instruction step that ends the same way under every environment and emits
nothing. Straight-line computation, RAM accesses and branches are such
steps; device reads, mip reads and SC are not. -/

def DetStep (B : Board) (img : List Segment) (m m' : Machine) : Prop :=
  ∀ o, stepInstr B img m o = .ok m'.core m'.ram []

inductive DetSteps (B : Board) (img : List Segment) : Nat → Machine → Machine → Prop
  | refl (m) : DetSteps B img 0 m m
  | step {n m m₁ m₂} : DetStep B img m m₁ → DetSteps B img n m₁ m₂ → DetSteps B img (n+1) m m₂

theorem DetSteps.trans {a b m₁ m₂ m₃} (h₁ : DetSteps B img a m₁ m₂) (h₂ : DetSteps B img b m₂ m₃) :
    DetSteps B img (a + b) m₁ m₃ := by
  induction h₁ with
  | refl => simpa using h₂
  | step hs _ ih => rw [Nat.add_right_comm]; exact .step hs (ih h₂)

theorem DetSteps.single {m m'} (h : DetStep B img m m') : DetSteps B img 1 m m' :=
  .step h (.refl _)

/-- A deterministic step is a `Step` with no events. -/
theorem DetStep.toStep {m m'} (h : DetStep B img m m') : Step B img m m' [] :=
  .instr (fun _ => 0) (h _)

/-- Every machine along a deterministic run can step without escaping. -/
theorem DetStep.noFault {m m'} (h : DetStep B img m m') (o f) : stepInstr B img m o ≠ .fault f := by
  rw [h o]; exact fun h => Result.noConfusion h

/-! ## Fetch, decode, execute -/

/-- The instruction the hart decodes at `pc`. -/
def fetchDecode (img : List Segment) (pc : Word) : Option (Instr × Word) :=
  match fetch img pc with
  | some (bits, len) => (decode bits len).map (·, len)
  | none => none

theorem stepInstr_of {m : Machine} {i len o} (hal : m.core.pc.getLsbD 0 = false)
    (hd : fetchDecode img m.core.pc = some (i, len)) :
    stepInstr B img m o = interp B img o (exec m.core len i) m.ram 0 [] := by
  unfold fetchDecode at hd
  unfold stepInstr
  rw [hal]
  split at hd
  · rename_i bits len' hf
    simp only [hf]
    cases hdec : decode bits len' with
    | none => simp [hdec] at hd
    | some i' =>
      simp only [hdec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      rfl
  · simp at hd

/-- The bridge every per-instruction step lemma goes through. -/
theorem detStep_of {m : Machine} {i len c ram} (hal : m.core.pc.getLsbD 0 = false)
    (hd : fetchDecode img m.core.pc = some (i, len))
    (h : ∀ o, interp B img o (exec m.core len i) m.ram 0 [] = .ok c ram []) :
    DetStep B img m ⟨c, ram⟩ := fun o => by rw [stepInstr_of hal hd]; exact h o

/-! ## Registers and CSRs -/

@[simp] theorem Core.get_zero (c : Core) : c.get 0 = 0 := rfl

theorem Core.get_set (c : Core) (r q : Reg) (v : Word) :
    (c.set r v).get q = if q.val = 0 then 0 else if q = r then v else c.get q := by
  unfold Core.set Core.get
  by_cases hr : r.val = 0
  · simp only [hr, ite_true]
    by_cases hq : q.val = 0
    · simp [hq]
    · by_cases e : q = r
      · exact absurd (e ▸ hr) hq
      · simp [hq, e]
  · simp only [hr, ite_false]
    by_cases hq : q.val = 0
    · simp [hq]
    · by_cases e : q = r <;> simp [hq, e]

@[simp] theorem Core.get_set_self (c : Core) (r : Reg) (v : Word) (h : r.val ≠ 0) :
    (c.set r v).get r = v := by simp [Core.get_set, h]

@[simp] theorem Core.get_set_ne (c : Core) (r q : Reg) (v : Word) (h : q ≠ r) :
    (c.set r v).get q = c.get q := by
  rw [Core.get_set]
  by_cases hq : q.val = 0
  · simp [hq, Core.get]
  · simp [hq, h]

@[simp] theorem Core.get_withPc (c : Core) (p : Word) (r : Reg) :
    ({ c with pc := p } : Core).get r = c.get r := rfl

@[simp] theorem Core.set_zero (c : Core) (v : Word) : c.set 0 v = c := rfl

/-- Write `rd` and move to `pc`: what every ALU instruction does. -/
def Core.wr (c : Core) (rd : Reg) (v pc : Word) : Core := { c.set rd v with pc := pc }
/-- Move to `pc`. -/
def Core.goto (c : Core) (pc : Word) : Core := { c with pc := pc }

@[simp] theorem Core.wr_pc (c : Core) (rd : Reg) (v pc : Word) : (c.wr rd v pc).pc = pc := rfl
@[simp] theorem Core.goto_pc (c : Core) (pc : Word) : (c.goto pc).pc = pc := rfl
@[simp] theorem Core.goto_get (c : Core) (pc : Word) (r : Reg) : (c.goto pc).get r = c.get r := rfl
@[simp] theorem Core.goto_goto (c : Core) (p q : Word) : (c.goto p).goto q = c.goto q := rfl
theorem Core.wr_get (c : Core) (rd r : Reg) (v pc : Word) :
    (c.wr rd v pc).get r = if r.val = 0 then 0 else if r = rd then v else c.get r :=
  Core.get_set c rd r v
theorem Core.wr_get_self (c : Core) (rd : Reg) (v pc : Word) (h : rd.val ≠ 0) :
    (c.wr rd v pc).get rd = v := Core.get_set_self c rd v h
theorem Core.wr_get_ne (c : Core) (rd r : Reg) (v pc : Word) (h : r ≠ rd) :
    (c.wr rd v pc).get r = c.get r := Core.get_set_ne c rd r v h

/-! Each instruction's effect tree, as the step lemmas consume it. -/

theorem exec_opimm (c : Core) (len : Word) (op rd rs1 imm) :
    exec c len (.opimm op rd rs1 imm) = .done (c.wr rd (alu op (c.get rs1) imm) (c.pc + len)) := rfl
theorem exec_op (c : Core) (len : Word) (op rd rs1 rs2) :
    exec c len (.op op rd rs1 rs2) = .done (c.wr rd (alu op (c.get rs1) (c.get rs2)) (c.pc + len)) := rfl
theorem exec_lui (c : Core) (len : Word) (rd imm) :
    exec c len (.lui rd imm) = .done (c.wr rd imm (c.pc + len)) := rfl
theorem exec_load (c : Core) (len : Word) (w signed rd rs1 off) :
    exec c len (.load w signed rd rs1 off) =
      .load w (c.get rs1 + off) false (fun v => .done (c.wr rd (extend w signed v) (c.pc + len))) := rfl
theorem exec_store (c : Core) (len : Word) (w rs1 rs2 off) :
    exec c len (.store w rs1 rs2 off) =
      .store w (c.get rs1 + off) (c.get rs2) false (.done (c.goto (c.pc + len))) := rfl
theorem exec_branch (c : Core) (len : Word) (cond rs1 rs2 off) :
    exec c len (.branch cond rs1 rs2 off) =
      if taken cond (c.get rs1) (c.get rs2) then jump c (c.pc + off) else .done (c.goto (c.pc + len)) := rfl
theorem exec_jalr (c : Core) (len : Word) (rd rs1 off) :
    exec c len (.jalr rd rs1 off) = jump (c.set rd (c.pc + len)) ((c.get rs1 + off) &&& ~~~1) := rfl
theorem exec_jal (c : Core) (len : Word) (rd off) :
    exec c len (.jal rd off) = jump (c.set rd (c.pc + len)) (c.pc + off) := rfl

theorem jump_ok (c : Core) (t : Word) (h : t.getLsbD 0 = false) : jump c t = .done (c.goto t) := by
  unfold jump; rw [h]; rfl

theorem clear_bit0 (t : Word) : (t &&& ~~~1).getLsbD 0 = false := by simp

/-- Everything in a core except the general-purpose registers. -/
def Core.ctl (c : Core) : Word × Bool × Bool × BitVec 2 × Word × Word × Word × Word × Word × Bool :=
  (c.pc, c.mie_, c.mpie, c.mpp, c.mieReg, c.mtvec, c.mepc, c.mcause, c.mscratch, c.resv)

/-- Two cores whose CSRs and reservation agree. -/
def Core.sameCsr (c d : Core) : Prop := c.ctl.2 = d.ctl.2

theorem Core.set_ctl (c : Core) (r : Reg) (v : Word) : (c.set r v).ctl = c.ctl := by
  unfold Core.set; split <;> rfl

@[simp] theorem Core.set_pc (c : Core) (r : Reg) (v : Word) : (c.set r v).pc = c.pc := by
  unfold Core.set; split <;> rfl

theorem Core.sameCsr_set {c d : Core} (h : c.sameCsr d) (r : Reg) (v : Word) :
    (c.set r v).sameCsr d := by
  unfold Core.sameCsr at *; rw [Core.set_ctl]; exact h

theorem Core.sameCsr_pc {c d : Core} (h : c.sameCsr d) (pc : Word) :
    ({ c with pc := pc } : Core).sameCsr d := h

theorem Core.sameCsr_refl (c : Core) : c.sameCsr c := rfl

theorem Core.sameCsr_symm {c d : Core} (h : c.sameCsr d) : d.sameCsr c := h.symm

theorem Core.sameCsr_trans {c d e : Core} (h₁ : c.sameCsr d) (h₂ : d.sameCsr e) :
    c.sameCsr e := h₁.trans h₂

theorem Core.sameCsr_wr (c : Core) (rd : Reg) (v pc : Word) : (c.wr rd v pc).sameCsr c := by
  unfold Core.wr Core.set; split <;> rfl

theorem Core.sameCsr_goto (c : Core) (pc : Word) : (c.goto pc).sameCsr c := rfl

/-! ## Effects that touch only RAM -/

@[simp] theorem interp_done (o : Oracle) (c : Core) (ram) (i evs) :
    interp B img o (.done c) ram i evs = .ok c ram evs := rfl

theorem interp_load_ram (o : Oracle) {w a atomic k ram i evs}
    (hal : a.toNat % w.bytes = 0) (hin : B.inRam a w.bytes = true) :
    interp B img o (.load w a atomic k) ram i evs = interp B img o (k (ramRead ram a w)) ram i evs := by
  simp [interp, hal, hin]

theorem interp_store_ram (o : Oracle) {w a v atomic k ram i evs}
    (hal : a.toNat % w.bytes = 0) (hin : B.inRam a w.bytes = true) :
    interp B img o (.store w a v atomic k) ram i evs = interp B img o k (ramWrite ram a v w) i evs := by
  simp [interp, hal, hin]

theorem Board.inRam_iff (a : Word) (n : Nat) :
    B.inRam a n = true ↔ B.ramBase ≤ a.toNat ∧ a.toNat + n ≤ B.ramBase + B.ramSize := by
  simp [Board.inRam]

/-- Reading a byte RAM holds. -/
theorem ramRead_b (ram : Word → BitVec 8) (a : Word) : (ramRead ram a .b).toNat = (ram a).toNat := by
  have := (ram a).isLt
  simp [ramRead]; omega

end E5R
