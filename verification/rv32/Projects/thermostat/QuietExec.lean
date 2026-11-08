import Projects.thermostat.QuietEffect
namespace E5R.Thermostat.QuietExec
open E5R E5R.Thermostat
open QuietEffect

theorem jump_safe {B img} (c : Core) (p : Word) : Safe B img (jump c p) := by
  unfold jump
  split
  · exact .trap _
  · exact .done _

theorem csr_read {B img} (c : Core) (addr : Nat) (k : Word → Eff) (next : ∀ v, Safe B img (k v)) : Safe B img (csrRead c addr k) := by
  unfold csrRead
  split
  · exact next _
  · split
    · exact next _
    · split
      · exact next _
      · split
        · exact next _
        · split
          · exact next _
          · split
            · exact next _
            · split
              · exact .pick (fun _ => next _)
              · split
                · exact next _
                · exact .unsupported _

theorem csr_write {B img} (c : Core) (addr : Nat) (v : Word) (k : Core → Eff) (next : ∀ c, Safe B img (k c)) : Safe B img (csrWrite c addr v k) := by
  simp only [csrWrite]
  split
  · split
    · exact .unsupported _
    · split
      · exact .unsupported _
      · exact next _
  · split
    · exact next _
    · split
      · split
        · exact next _
        · split
          · exact next _
          · exact .unsupported _
      · split
        · exact next _
        · split
          · exact next _
          · split
            · exact next _
            · exact .unsupported _

theorem csr_safe {B img} (c : Core) (op : CsrOp) (rd : Reg) (src : CsrSrc) (addr : Nat)
    (k : Core → Eff) (next : ∀ c, Safe B img (k c)) : Safe B img (execCsr c op rd src addr k) := by
  cases src <;> simp only [execCsr]
  all_goals
    split
    · exact .trap _
    · apply csr_read
      intro value
      split
      · exact next _
      · exact csr_write _ _ _ _ next

def NonLoad : Instr → Prop
  | .load _ _ _ _ _ => False
  | _ => True

/-- Non-load instructions accept no device reads, including environmental CSR
    choices and atomic accesses, which fail closed outside RAM. -/
theorem safe {B img} (c : Core) (len : Word) (i : Instr) (hi : NonLoad i) : Safe B img (exec c len i) := by
  cases i with
  | lui => exact .done _
  | auipc => exact .done _
  | jal => exact jump_safe _ _
  | jalr => exact jump_safe _ _
  | branch =>
    simp only [exec]
    split
    · exact jump_safe _ _
    · exact .done _
  | load => contradiction
  | store => exact .store (.done _)
  | opimm => exact .done _
  | op => exact .done _
  | muldiv => exact .done _
  | lr => exact .load (Or.inl rfl) (fun _ => .done _)
  | sc =>
    apply Safe.load (Or.inl rfl)
    intro value
    split
    · exact .done _
    · apply Safe.choose
      intro success
      split
      · exact .store (.done _)
      · exact .done _
  | amo => exact .load (Or.inl rfl) (fun _ => .store (.done _))
  | fence => exact .done _
  | fencei => exact .done _
  | csr => exact csr_safe _ _ _ _ _ _ (fun _ => .done _)
  | ecall => exact .trap _
  | ebreak => exact .trap _
  | mret =>
    simp only [exec]
    split
    · exact .unsupported _
    · exact jump_safe _ _
  | wfi => exact .done _

theorem promote_nonload {B : Board} {img : List Segment} {c d : Core} {ram after : Word → BitVec 8} {i : Instr} {len : Word}
    (hal : c.pc.getLsbD 0=false) (hf : fetchDecode img c.pc=some (i,len)) (hi : NonLoad i)
    (h : DetStep B img ⟨c,ram⟩ ⟨d,after⟩) : Quiet.Step B img ⟨c,ram⟩ ⟨d,after⟩ := QuietEffect.promote hal hf (safe c len i hi) h
end E5R.Thermostat.QuietExec
