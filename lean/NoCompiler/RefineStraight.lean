import NoCompiler.RefineCongr
import Std.Tactic.BVDecide

/-
Straight-line equivalence (spec-v1-refine.md item 6; docs/isa/refine.md).

Two straight-line sequences of register instructions, `as` in A and `bs` in
B, are equivalent from live-in registers `L` to live-out registers `L'`
(`SeqEquiv L L' as bs`) when any two register files that agree on `L` give,
after `as` and after `bs` respectively, the same values in every register of
`L'`. `SeqEquiv.agree` turns that into C's `Agree` on machine states: from
states agreeing on `L`, both sequences run without faulting and end in
states agreeing on `L'`, with memory, trace and exit status unchanged, each
`4 * length` bytes further on.

The register instructions are those without memory, control or environment
effects (`Instr.alu`): `lui`, the immediate and register ALU operations, the
W forms, shifts and Zbb's unary operations. Loads and stores are not in the
first version.

Proving `SeqEquiv` for two concrete sequences is a set of bit-vector
identities, one per live-out register, over the live-in registers' values.
Two tactics, two trust tiers (docs/isa/trust.md):

* `seq_equiv`: unfold, then normalise in the kernel (`simp` with the
  bit-vector lemmas, `bv_normalize`, `omega`). Standard axioms only.
* `seq_equiv_bv`: the same, then `bv_decide` on what is left. `bv_decide`
  checks a SAT certificate by native evaluation: every theorem it proves
  depends on an axiom of native computation (`<thm>._native.bv_decide.ax_*`
  in Lean 4.35; `Lean.ofReduceBool` before), and the audit lists those
  theorems as a separate tier.
-/
namespace NoCompiler

/-- Instructions that only read and write registers. -/
def Instr.alu : Instr → Bool
  | .lui .. | .iop .. | .addiw .. | .shift .. | .shiftw .. | .rop .. | .rwop .. | .uop .. => true
  | _ => false

/-- A register file as a function, read the way `State.reg` reads it. -/
def RegFile := Reg → Word

namespace RegFile
def get (g : RegFile) (r : Reg) : Word := if r = 0 then 0 else g r
def set (g : RegFile) (rd : Reg) (v : Word) : RegFile := fun r => if r = rd then v else g r
end RegFile

/-- The destination and value of a register instruction, from a register
    file: what `exec` writes (Machine.lean). -/
def Instr.aluOut : Instr → RegFile → Option (Reg × Word)
  | .lui rd imm, _ => some (rd, (imm.setWidth 32 <<< 12).signExtend 64)
  | .iop op rd rs1 imm, g => some (rd, evalI op (g.get rs1) (imm.signExtend 64))
  | .addiw rd rs1 imm, g => some (rd, sext32 (g.get rs1 + imm.signExtend 64))
  | .shift op rd rs1 sh, g => some (rd, evalSh op (g.get rs1) sh.toNat)
  | .shiftw op rd rs1 sh, g => some (rd, evalShW op (g.get rs1) sh.toNat)
  | .rop op rd a b, g => some (rd, evalR op (g.get a) (g.get b))
  | .rwop op rd a b, g => some (rd, evalRW op (g.get a) (g.get b))
  | .uop op rd rs1, g => some (rd, evalU op (g.get rs1))
  | _, _ => none

/-- Run register instructions on a register file. -/
def runRegs : List Instr → RegFile → RegFile
  | [], g => g
  | i :: is, g => runRegs is (match i.aluOut g with
    | some (rd, v) => g.set rd v
    | none => g)

/-- Equivalence of two register-instruction sequences, from `L` to `L'`. -/
def SeqEquiv (L L' : List Reg) (as bs : List Instr) : Prop :=
  ∀ ga gb : RegFile, (∀ r ∈ L, ga.get r = gb.get r) → ∀ r ∈ L', (runRegs as ga).get r = (runRegs bs gb).get r

/-- Run a sequence of instructions with `exec`. -/
def execSeq : List Instr → State → Option State
  | [], s => some s
  | i :: is, s => (exec i s).bind (execSeq is)

/-- The register file `s.reg` reads. -/
def State.regFile (s : State) : RegFile := fun r => s.reg r

theorem RegFile.get_regFile (s : State) (r : Reg) : s.regFile.get r = s.reg r := by
  by_cases h : r = 0 <;> simp [State.regFile, RegFile.get, State.reg, h]

/-- Two register files that read the same. -/
def RegFile.Same (g g' : RegFile) : Prop := ∀ r, g.get r = g'.get r

theorem aluOut_congr {g g' : RegFile} (h : g.Same g') (i : Instr) : i.aluOut g = i.aluOut g' := by
  cases i <;> simp [Instr.aluOut, h _]

theorem RegFile.Same.set {g g' : RegFile} (h : g.Same g') (rd : Reg) (v : Word) :
    (g.set rd v).Same (g'.set rd v) := by
  intro r
  have := h r
  by_cases h0 : r = 0 <;> by_cases hr : r = rd <;> simp_all [RegFile.get, RegFile.set]

theorem runRegs_congr : ∀ (is : List Instr) {g g' : RegFile}, g.Same g' → (runRegs is g).Same (runRegs is g')
  | [], _, _, h => h
  | i :: is, g, g', h => by
    simp only [runRegs, aluOut_congr h i]
    apply runRegs_congr is
    split
    · exact h.set _ _
    · exact h

/-- One register instruction, as `exec` does it. -/
theorem exec_alu {i : Instr} (hi : i.alu = true) (s : State) :
    ∃ rd v, i.aluOut s.regFile = some (rd, v) ∧ exec i s = some ((s.setReg rd v).setPc (s.pc + 4)) := by
  cases i <;> simp [Instr.alu] at hi <;>
    simp only [Instr.aluOut, exec, RegFile.get_regFile] <;> exact ⟨_, _, rfl, rfl⟩

theorem regFile_step (s : State) (rd : Reg) (v : Word) (p : Word) :
    ((s.setReg rd v).setPc p).regFile.Same (s.regFile.set rd v) := by
  intro r
  rw [RegFile.get_regFile]
  simp only [State.setPc_reg, State.reg_setReg]
  by_cases h0 : r = 0 <;> by_cases hr : r = rd <;> simp [h0, hr, RegFile.get, RegFile.set, State.regFile]

/-- A sequence of register instructions runs without faulting; afterwards
    the registers read as `runRegs` says, memory, trace and exit status are
    unchanged, and the pc is past the sequence. -/
theorem execSeq_alu : ∀ {is : List Instr}, (∀ i ∈ is, i.alu = true) → ∀ s : State,
    ∃ s', execSeq is s = some s' ∧ (∀ r, s'.reg r = (runRegs is s.regFile).get r) ∧
      s'.mem = s.mem ∧ s'.trace = s.trace ∧ s'.exit = s.exit ∧ s'.pc = s.pc + BitVec.ofNat 64 (4 * is.length)
  | [], _, s => ⟨s, rfl, fun r => (RegFile.get_regFile s r).symm, rfl, rfl, rfl, by simp⟩
  | i :: is, h, s => by
    obtain ⟨rd, v, ho, he⟩ := exec_alu (h i List.mem_cons_self) s
    obtain ⟨s', hs, hr, hm, ht, hx, hp⟩ := execSeq_alu (fun j hj => h j (List.mem_cons_of_mem _ hj))
      ((s.setReg rd v).setPc (s.pc + 4))
    refine ⟨s', by rw [execSeq, he, Option.bind_some]; exact hs, ?_, by simpa using hm, by simpa using ht, by simpa using hx, ?_⟩
    · intro r
      rw [hr r]
      simp only [runRegs, ho]
      exact runRegs_congr is (regFile_step s rd v _) r
    · rw [hp]; simp only [State.setPc_pc, List.length_cons]; bv_omega

/-- `SeqEquiv` on machine states: from states agreeing on `L`, both sequences
    run, and end agreeing on `L'`. -/
theorem SeqEquiv.agree {L L' : List Reg} {as bs : List Instr} (h : SeqEquiv L L' as bs)
    (ha : ∀ i ∈ as, i.alu = true) (hb : ∀ i ∈ bs, i.alu = true) {sa sb : State} (hab : Agree L sa sb) :
    ∃ sa' sb', execSeq as sa = some sa' ∧ execSeq bs sb = some sb' ∧ Agree L' sa' sb' ∧
      sa'.pc = sa.pc + BitVec.ofNat 64 (4 * as.length) ∧ sb'.pc = sb.pc + BitVec.ofNat 64 (4 * bs.length) := by
  obtain ⟨sa', ea, ra, ma, ta, xa, pa⟩ := execSeq_alu ha sa
  obtain ⟨sb', eb, rb, mb, tb, xb, pb⟩ := execSeq_alu hb sb
  refine ⟨sa', sb', ea, eb, ⟨fun r hr => ?_, by rw [ma, mb, hab.mem], by rw [ta, tb, hab.trace],
    by rw [xa, xb, hab.exit]⟩, pa, pb⟩
  rw [ra, rb]
  exact h _ _ (fun r hr => by rw [RegFile.get_regFile, RegFile.get_regFile]; exact hab.regs r hr) r hr

/-! ## Tactics -/

/-- Split a `SeqEquiv` goal on concrete sequences into one bit-vector
    equation per live-out register, with the instructions evaluated and the
    live-in registers of B rewritten to A's. -/
macro "seq_equiv_split" : tactic => `(tactic| (
  intro ga gb hin
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true] at hin ⊢
  simp only [runRegs, Instr.aluOut, RegFile.get, RegFile.set, evalI, evalR, evalRW, evalSh, evalShW, evalU, bool64,
    Fin.isValue, Fin.reduceEq, ite_true, ite_false, reduceIte] at hin ⊢
  simp only [hin]
  repeat' apply And.intro))

/-- Kernel tier: standard axioms only. -/
macro "seq_equiv" : tactic => `(tactic| (
  seq_equiv_split
  all_goals first | with_reducible rfl | (bv_normalize; done) | bv_omega | (simp; done) | ac_rfl))

/-- With `bv_decide` where the kernel tier fails: the theorem depends on an
    axiom of native computation (docs/isa/trust.md, the bv_decide tier). -/
macro "seq_equiv_bv" : tactic => `(tactic| (
  seq_equiv_split
  all_goals first | with_reducible rfl | (bv_normalize; done) | bv_omega | (simp; done) | ac_rfl | bv_decide))

end NoCompiler
