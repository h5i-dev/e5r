import Theories.Logic
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.constructorNameAsVariable false
namespace E5R.Thermostat.Control
open E5R

/-- Every possible continuation of an effect preserves masked global IRQs.
    Faults have no successor; this predicate does not claim absence of faults. -/
def Masked : Eff → Prop
  | .done c => c.mie_ = false
  | .trap _ | .unsupported _ => True
  | .load _ _ _ k | .pick k => ∀ v, Masked (k v)
  | .store _ _ _ _ k => Masked k
  | .choose k => ∀ b, Masked (k b)

theorem interp_masked {B img e} (h : Masked e) :
    ∀ o ram i evs c r out, interp B img o e ram i evs = .ok c r out → c.mie_ = false := by
  induction e with
  | done c => intro o ram i evs c' r out he; cases he; exact h
  | trap | unsupported => intros; contradiction
  | choose k ih => intro o ram i evs c r out he; exact ih _ (h _) o ram (i+1) evs c r out he
  | pick k ih => intro o ram i evs c r out he; exact ih _ (h _) o ram (i+1) evs c r out he
  | load w a atomic k ih =>
    intro o ram i evs c r out he
    simp only [interp] at he
    split at he
    · contradiction
    · split at he
      · exact ih _ (h _) o ram i evs c r out he
      · split at he
        · contradiction
        · split at he
          · exact ih _ (h _) o ram i evs c r out he
          · split at he
            · split at he
              · exact ih _ (h _) o ram (i+1) evs c r out he
              · contradiction
            · contradiction
  | store w a v atomic k ih =>
    intro o ram i evs c r out he
    simp only [interp] at he
    split at he
    · contradiction
    · split at he
      · exact ih h o _ i evs c r out he
      · split at he
        · contradiction
        · split at he
          · split at he
            · exact ih h o ram i _ c r out he
            · contradiction
          · contradiction

theorem set_masked {c : Core} (h : c.mie_ = false) (r : Reg) (v : Word) :
    (c.set r v).mie_ = false := by unfold Core.set; split <;> exact h

theorem jump_masked {c : Core} (h : c.mie_ = false) (a : Word) : Masked (jump c a) := by
  unfold jump
  split
  · trivial
  · exact h

/-- A supported CSR write outside mstatus cannot change global MIE. -/
theorem csrWrite_masked (c : Core) (addr : Nat) (v : Word) (fin : Core → Eff)
    (ha : addr ≠ csrMstatus) (h : c.mie_ = false)
    (hf : ∀ d, d.mie_ = false → Masked (fin d)) : Masked (csrWrite c addr v fin) := by
  unfold csrWrite
  simp only [ha,ite_false]
  split
  · exact hf _ h
  · split
    · split
      · exact hf _ h
      · split
        · exact hf _ h
        · trivial
    · split
      · exact hf _ h
      · split
        · exact hf _ h
        · split
          · exact hf _ h
          · trivial

theorem csrRead_masked (c : Core) (addr : Nat) (k : Word → Eff)
    (hk : ∀ v, Masked (k v)) : Masked (csrRead c addr k) := by
  unfold csrRead
  split
  · exact hk _
  · split
    · exact hk _
    · split
      · exact hk _
      · split
        · exact hk _
        · split
          · exact hk _
          · split
            · exact hk _
            · split
              · exact fun v => hk _
              · split
                · exact hk _
                · trivial

/-- Non-mstatus CSR accesses either fail closed or retain global MIE. -/
theorem csr_masked (c : Core) (op : CsrOp) (rd : Reg) (src : CsrSrc) (addr : Nat)
    (ha : addr ≠ csrMstatus) (h : c.mie_ = false) (fin : Core → Eff)
    (hf : ∀ d, d.mie_ = false → Masked (fin d)) : Masked (execCsr c op rd src addr fin) := by
  cases src <;> dsimp only [execCsr]
  all_goals
    split
    · trivial
    · apply csrRead_masked
      intro old
      split
      · exact hf _ (set_masked h _ _)
      · exact csrWrite_masked _ _ _ _ ha (set_masked h _ _) hf

theorem clear_masked (c : Core) (len : Word) :
    Masked (exec c len (.csr .rc 0 (.imm 8) csrMstatus)) := by
  change Masked (csrWrite c csrMstatus (mstatusOf c &&& ~~~8#32) (fun d => .done {d with pc := c.pc+len}))
  unfold csrWrite
  simp only [ite_true]
  split
  · trivial
  · split
    · trivial
    · change (mstatusOf c &&& ~~~8#32).getLsbD 3 = false
      rw [BitVec.getLsbD_and]
      have hb : (~~~8#32).getLsbD 3 = false := by decide +kernel
      rw [hb,Bool.and_false]

def Safe : Instr → Prop
  | .mret => False
  | .csr op rd src addr => addr ≠ csrMstatus ∨ (op = .rc ∧ rd = 0 ∧ src = .imm 8)
  | _ => True

instance (i : Instr) : Decidable (Safe i) := by
  cases i <;> unfold Safe <;> infer_instance

theorem exec_masked (c : Core) (len : Word) (i : Instr) (h : c.mie_ = false) (hs : Safe i) :
    Masked (exec c len i) := by
  cases i with
  | lui rd imm | auipc rd imm | opimm op rd rs1 imm | op op rd rs1 rs2 | muldiv op rd rs1 rs2 =>
    exact set_masked h _ _
  | jal rd off => exact jump_masked (set_masked h _ _) _
  | jalr rd rs1 off => exact jump_masked (set_masked h _ _) _
  | branch cond rs1 rs2 off =>
    simp only [exec]
    split
    · exact jump_masked h _
    · exact h
  | load w signed rd rs1 off => exact fun v => set_masked h _ _
  | store w rs1 rs2 off => exact h
  | lr rd rs1 => exact fun v => set_masked (c := {c with resv := true}) h _ _
  | sc rd rs1 rs2 =>
    simp only [exec,Masked]
    intro v
    split
    · exact set_masked (c := {c with resv := false}) h _ _
    · intro b
      cases b <;> exact set_masked (c := {c with resv := false}) h _ _
  | amo op rd rs1 rs2 => exact fun v => set_masked h _ _
  | fence | fencei | wfi => exact h
  | ecall | ebreak => trivial
  | mret => exact False.elim hs
  | csr op rd src addr =>
    rcases hs with ha | ⟨rfl,rfl,rfl⟩
    · exact csr_masked c op rd src addr ha h _ (fun d hd => hd)
    · by_cases ha : addr = csrMstatus
      · subst addr
        exact clear_masked c len
      · exact csr_masked c .rc 0 (.imm 8) addr ha h _ (fun d hd => hd)
end E5R.Thermostat.Control
