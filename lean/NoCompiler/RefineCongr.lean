import NoCompiler.Refine
import NoCompiler.Lemmas

/-
The congruence rule for refinement (docs/isa/refine.md, item 2): the same
instruction, run from two states that agree on what it reads, gives two
states that agree on what it wrote and on everything else they agreed on.

`Agree L sa sb`: the registers in `L`, memory, the trace and the exit status
are equal. The pc is related separately, since the two functions may sit at
different addresses (an unchanged instruction of B is the instruction of A,
somewhere else).

A liveness analysis says which registers each instruction's continuation
reads. It is not trusted: the sets it computes are a certificate, and what is
used of them is the inclusion `uses i ∪ (L ∖ defs i) ⊆ L'` at each
instruction, decided by the kernel.
-/
namespace NoCompiler

/-- The registers an instruction reads. -/
def Instr.uses : Instr → List Reg
  | .lui .. | .auipc .. | .jal .. => []
  | .jalr _ rs1 _ => [rs1]
  | .branch _ a b _ => [a, b]
  | .load _ _ rs1 _ => [rs1]
  | .store _ a b _ => [a, b]
  | .iop _ _ rs1 _ | .addiw _ rs1 _ | .shift _ _ rs1 _ | .shiftw _ _ rs1 _ | .uop _ _ rs1 => [rs1]
  | .rop _ _ a b | .rwop _ _ a b => [a, b]
  -- a7 the number, a0..a2 the arguments of the syscalls the model admits.
  | .ecall => [17, 10, 11, 12]

/-- The registers an instruction writes. -/
def Instr.defs : Instr → List Reg
  | .lui rd _ | .auipc rd _ | .jal rd _ | .jalr rd _ _ | .load _ rd _ _ | .iop _ rd _ _
  | .addiw rd _ _ | .shift _ rd _ _ | .shiftw _ rd _ _ | .rop _ rd _ _ | .rwop _ rd _ _
  | .uop _ rd _ => [rd]
  | .branch .. | .store .. => []
  | .ecall => [10]

/-- Equal on the registers `L`, memory, the trace and the exit status. -/
structure Agree (L : List Reg) (sa sb : State) : Prop where
  regs : ∀ r ∈ L, sa.reg r = sb.reg r
  mem : sa.mem = sb.mem
  trace : sa.trace = sb.trace
  exit : sa.exit = sb.exit

namespace Agree
variable {L L' : List Reg} {sa sb : State}

theorem mono (h : Agree L sa sb) (hs : ∀ r ∈ L', r ∈ L) : Agree L' sa sb :=
  ⟨fun r hr => h.regs r (hs r hr), h.mem, h.trace, h.exit⟩

theorem setPc (h : Agree L sa sb) (p q : Word) : Agree L (sa.setPc p) (sb.setPc q) :=
  ⟨h.regs, h.mem, h.trace, h.exit⟩

/-- Writing equal values into one register keeps agreement on `L` if every
    register of `L` other than it was agreed on before. -/
theorem setReg (h : Agree L' sa sb) (rd : Reg) {va vb : Word} (hv : va = vb)
    (hL : ∀ r ∈ L, r ≠ rd → r ∈ L') : Agree L (sa.setReg rd va) (sb.setReg rd vb) := by
  refine ⟨fun r hr => ?_, by simp [h.mem], by simp [h.trace], by simp [h.exit]⟩
  rw [State.reg_setReg, State.reg_setReg]
  by_cases h0 : r = 0
  · simp [h0]
  · by_cases hr' : r = rd
    · simp [hr', hv]
    · simp only [h0, hr', ite_false]; exact h.regs r (hL r hr hr')

theorem setMem (h : Agree L sa sb) {ma mb : Word → Byte} (hm : ma = mb) :
    Agree L (sa.setMem ma) (sb.setMem mb) := ⟨h.regs, hm, h.trace, h.exit⟩

theorem emit (h : Agree L sa sb) (e : Event) : Agree L (sa.emit e) (sb.emit e) :=
  ⟨h.regs, h.mem, by simp [h.trace], h.exit⟩

theorem reg_of_mem (h : Agree L sa sb) {r : Reg} (hr : r ∈ L) : sa.reg r = sb.reg r := h.regs r hr
end Agree

/-- What the congruence rule needs of the registers agreed on before an
    instruction (`L'`) for agreement on `L` after it. -/
def Instr.transfer (i : Instr) (L L' : List Reg) : Prop :=
  (∀ r ∈ i.uses, r ∈ L') ∧ ∀ r ∈ L, r ∉ i.defs → r ∈ L'

instance (i : Instr) (L L' : List Reg) : Decidable (i.transfer L L') := by
  unfold Instr.transfer; infer_instance

/-- An instruction whose effect does not depend on its own address: neither
    a jump (its target is pc-relative), nor `auipc`, nor `ecall` (separately,
    below). -/
def Instr.straight : Instr → Bool
  | .lui .. | .load .. | .store .. | .iop .. | .addiw .. | .shift .. | .shiftw .. | .rop .. | .rwop ..
  | .uop .. => true
  | _ => false

/-- The congruence rule for straight-line instructions: from states agreeing
    on `L'`, the instruction faults on both or on neither, and the results
    agree on `L` and are at the next instruction of each. -/
theorem exec_congr {i : Instr} (hi : i.straight = true) {L L' : List Reg} (ht : i.transfer L L')
    {sa sb : State} (h : Agree L' sa sb) :
    (exec i sa = none ↔ exec i sb = none) ∧
    ∀ sa' sb', exec i sa = some sa' → exec i sb = some sb' →
      Agree L sa' sb' ∧ sa'.pc = sa.pc + 4 ∧ sb'.pc = sb.pc + 4 := by
  obtain ⟨hu, hl⟩ := ht
  have u1 : ∀ r, r ∈ i.uses → sa.reg r = sb.reg r := fun r hr => h.regs r (hu r hr)
  cases i with
  | lui rd imm =>
    refine ⟨by simp [exec], fun sa' sb' ha hb => ?_⟩
    simp only [exec, Option.some.injEq] at ha hb; subst ha hb
    exact ⟨(h.setReg rd rfl (fun r hr hne => hl r hr (by simp [Instr.defs, hne]))).setPc _ _,
      by simp, by simp⟩
  | load op rd rs1 off =>
    have e1 := u1 rs1 (by simp [Instr.uses])
    have ea_eq : ea sa rs1 off = ea sb rs1 off := by simp [ea, e1]
    refine ⟨by simp only [exec]; rw [ea_eq]; split <;> simp, fun sa' sb' ha hb => ?_⟩
    simp only [exec] at ha hb
    rw [ea_eq] at ha
    by_cases hal : aligned (ea sb rs1 off) op.width <;>
      simp only [hal, ite_true, ite_false, Option.some.injEq, reduceCtorEq] at ha hb
    subst ha hb
    refine ⟨(h.setReg rd (by rw [h.mem]) (fun r hr hne => hl r hr (by simp [Instr.defs, hne]))).setPc _ _,
      by simp, by simp⟩
  | store op a b off =>
    have ea_eq : ea sa a off = ea sb a off := by simp [ea, u1 a (by simp [Instr.uses])]
    have eb := u1 b (by simp [Instr.uses])
    refine ⟨by simp only [exec]; rw [ea_eq]; split <;> simp, fun sa' sb' ha hb => ?_⟩
    simp only [exec] at ha hb
    rw [ea_eq] at ha
    by_cases hal : aligned (ea sb a off) op.width <;>
      simp only [hal, ite_true, ite_false, Option.some.injEq, reduceCtorEq] at ha hb
    subst ha hb
    refine ⟨((h.mono (fun r hr => hl r hr (by simp [Instr.defs]))).setMem (by rw [h.mem, eb])).setPc _ _,
      by simp, by simp⟩
  | iop op rd rs1 imm =>
    refine ⟨by simp [exec], fun sa' sb' ha hb => ?_⟩
    simp only [exec, Option.some.injEq] at ha hb; subst ha hb
    exact ⟨(h.setReg rd (by rw [u1 rs1 (by simp [Instr.uses])])
      (fun r hr hne => hl r hr (by simp [Instr.defs, hne]))).setPc _ _, by simp, by simp⟩
  | addiw rd rs1 imm =>
    refine ⟨by simp [exec], fun sa' sb' ha hb => ?_⟩
    simp only [exec, Option.some.injEq] at ha hb; subst ha hb
    exact ⟨(h.setReg rd (by rw [u1 rs1 (by simp [Instr.uses])])
      (fun r hr hne => hl r hr (by simp [Instr.defs, hne]))).setPc _ _, by simp, by simp⟩
  | shift op rd rs1 sh =>
    refine ⟨by simp [exec], fun sa' sb' ha hb => ?_⟩
    simp only [exec, Option.some.injEq] at ha hb; subst ha hb
    exact ⟨(h.setReg rd (by rw [u1 rs1 (by simp [Instr.uses])])
      (fun r hr hne => hl r hr (by simp [Instr.defs, hne]))).setPc _ _, by simp, by simp⟩
  | shiftw op rd rs1 sh =>
    refine ⟨by simp [exec], fun sa' sb' ha hb => ?_⟩
    simp only [exec, Option.some.injEq] at ha hb; subst ha hb
    exact ⟨(h.setReg rd (by rw [u1 rs1 (by simp [Instr.uses])])
      (fun r hr hne => hl r hr (by simp [Instr.defs, hne]))).setPc _ _, by simp, by simp⟩
  | rop op rd a b =>
    refine ⟨by simp [exec], fun sa' sb' ha hb => ?_⟩
    simp only [exec, Option.some.injEq] at ha hb; subst ha hb
    exact ⟨(h.setReg rd (by rw [u1 a (by simp [Instr.uses]), u1 b (by simp [Instr.uses])])
      (fun r hr hne => hl r hr (by simp [Instr.defs, hne]))).setPc _ _, by simp, by simp⟩
  | rwop op rd a b =>
    refine ⟨by simp [exec], fun sa' sb' ha hb => ?_⟩
    simp only [exec, Option.some.injEq] at ha hb; subst ha hb
    exact ⟨(h.setReg rd (by rw [u1 a (by simp [Instr.uses]), u1 b (by simp [Instr.uses])])
      (fun r hr hne => hl r hr (by simp [Instr.defs, hne]))).setPc _ _, by simp, by simp⟩
  | uop op rd rs1 =>
    refine ⟨by simp [exec], fun sa' sb' ha hb => ?_⟩
    simp only [exec, Option.some.injEq] at ha hb; subst ha hb
    exact ⟨(h.setReg rd (by rw [u1 rs1 (by simp [Instr.uses])])
      (fun r hr hne => hl r hr (by simp [Instr.defs, hne]))).setPc _ _, by simp, by simp⟩
  | auipc | jal | jalr | branch | ecall => simp [Instr.straight] at hi

/-- The permission an instruction needs is the same on agreeing states. -/
theorem instrOk_congr {P : Perm} {i : Instr} {L' : List Reg} (hu : ∀ r ∈ i.uses, r ∈ L')
    {sa sb : State} (h : Agree L' sa sb) : InstrOk P i sa ↔ InstrOk P i sb := by
  have u1 : ∀ r, r ∈ i.uses → sa.reg r = sb.reg r := fun r hr => h.regs r (hu r hr)
  cases i with
  | load op rd rs1 off => simp [InstrOk, ea, u1 rs1 (by simp [Instr.uses])]
  | store op a b off => simp [InstrOk, ea, u1 a (by simp [Instr.uses])]
  | ecall =>
    simp [InstrOk, SysOk, u1 17 (by simp [Instr.uses]), u1 11 (by simp [Instr.uses]),
      u1 12 (by simp [Instr.uses]), Reg.a7, Reg.a1, Reg.a2]
  | _ => simp [InstrOk]

/-- A conditional branch takes the same direction on agreeing states. -/
theorem evalBr_congr {op : BrOp} {a b : Reg} {L' : List Reg}
    (hu : ∀ r ∈ (Instr.branch op a b 0).uses, r ∈ L') {sa sb : State} (h : Agree L' sa sb) :
    evalBr op (sa.reg a) (sa.reg b) = evalBr op (sb.reg a) (sb.reg b) := by
  rw [h.regs a (hu a (by simp [Instr.uses])), h.regs b (hu b (by simp [Instr.uses]))]

/-- The syscall rule: the environment's outcome for B is one it allows for A,
    and the two results agree. -/
theorem sys_congr {L L' : List Reg} (ht : Instr.ecall.transfer L L') {sa sb sb' : State}
    (h : Agree L' sa sb) (hb : Sys sb sb') :
    ∃ sa', Sys sa sa' ∧ Agree L sa' sb' ∧ (sa'.exit = none → sa'.pc = sa.pc + 4) ∧
      (sb'.exit = none → sb'.pc = sb.pc + 4) := by
  obtain ⟨hu, hl⟩ := ht
  have u : ∀ r, r ∈ Instr.ecall.uses → sa.reg r = sb.reg r := fun r hr => h.regs r (hu r hr)
  have e7 : sa.reg Reg.a7 = sb.reg Reg.a7 := u 17 (by simp [Instr.uses])
  have e0 : sa.reg Reg.a0 = sb.reg Reg.a0 := u 10 (by simp [Instr.uses])
  have e1 : sa.reg Reg.a1 = sb.reg Reg.a1 := u 11 (by simp [Instr.uses])
  have e2 : sa.reg Reg.a2 = sb.reg Reg.a2 := u 12 (by simp [Instr.uses])
  have hl' : ∀ r ∈ L, r ≠ 10 → r ∈ L' := fun r hr hne => hl r hr (by simp [Instr.defs, hne])
  have ret : ∀ v, Agree L (sa.sysRet v) (sb.sysRet v) := fun v =>
    (h.setReg 10 rfl hl').setPc _ _
  cases hb with
  | writeOk r h7 hr hm hp =>
    refine ⟨_, .writeOk r (e7 ▸ h7) (e2 ▸ hr) hm (e2 ▸ hp), ?_, fun _ => by simp, fun _ => by simp⟩
    rw [e0, e1, h.mem]; exact (ret _).emit _
  | writeErr e h7 h1 h2 =>
    exact ⟨_, .writeErr e (e7 ▸ h7) h1 h2, ret _, fun _ => by simp, fun _ => by simp⟩
  | readOk ds h7 hr hm =>
    refine ⟨_, .readOk ds (e7 ▸ h7) (e2 ▸ hr) hm, ?_, fun _ => by simp, fun _ => by simp⟩
    rw [e0, e1, h.mem]
    exact ((ret _).setMem rfl).emit _
  | readErr e h7 h1 h2 =>
    exact ⟨_, .readErr e (e7 ▸ h7) h1 h2, ret _, fun _ => by simp, fun _ => by simp⟩
  | exit h7 =>
    refine ⟨_, .exit (e7 ▸ h7), ?_, fun hx => by simp at hx, fun hx => by simp at hx⟩
    rw [e0]
    exact ⟨fun r hr => h.regs r (by
      by_cases hne : r = 10
      · subst hne; exact hu 10 (by simp [Instr.uses])
      · exact hl' r hr hne), by simp [h.mem], by simp [h.trace], by simp⟩

end NoCompiler
