import Projects.thermostat.Observed
set_option autoImplicit false
set_option maxRecDepth 3000
namespace E5R.Thermostat.BoardRestriction
open E5R E5R.Thermostat

/-- Successful execution under the RAM monitor is exactly execution on the
    original board, including every oracle index, RAM byte and MMIO log.
    Faults of the monitor are not silently accepted or summarized. -/
theorem effect (smallBoard bigBoard : Board) (image : List Segment)
    (incl : ∀ (a : Word) (w : Width),smallBoard.inRam a w.bytes=true → bigBoard.inRam a w.bytes=true)
    (away : ∀ (a : Word) (w : Width),bigBoard.inRam a w.bytes=true → smallBoard.inRam a w.bytes=false →
      romRead? image a.toNat w.bytes false=none ∧ smallBoard.device? a=none)
    (devs : ∀ a,smallBoard.device? a=bigBoard.device? a) {e : Eff} {o ram i evs reads c after events}
    (success : (Observed.interp smallBoard image o e ram i evs reads).value=.ok c after events) :
    Observed.interp bigBoard image o e ram i evs reads=Observed.interp smallBoard image o e ram i evs reads := by
  induction e generalizing ram i evs reads with
  | done d => rfl
  | trap ex =>
    change Result.fault (.trap ex)=Result.ok c after events at success
    cases success
  | unsupported why =>
    change Result.fault (.unsupported why)=Result.ok c after events at success
    cases success
  | choose k ih => exact ih _ success
  | pick k ih => exact ih _ success
  | load w a atomic k ih =>
    by_cases aligned : a.toNat%w.bytes≠0
    · rw [Observed.interp,if_pos aligned] at success
      cases success
    simp only [Observed.interp,aligned,ite_false] at success ⊢
    cases small : smallBoard.inRam a w.bytes with
    | true =>
      have large := incl a w small
      simp only [small,large,ite_true] at success ⊢
      exact ih _ success
    | false =>
      cases large : bigBoard.inRam a w.bytes with
      | true =>
        obtain ⟨rom,dev⟩ := away a w large small
        cases atomic <;> simp only [small,Bool.false_eq_true,ite_false,ite_true,rom,dev] at success <;> cases success
      | false =>
        simp only [small,large,ite_false] at success ⊢
        cases atomic with
        | true => cases success
        | false =>
          simp only [Bool.false_eq_true,ite_false] at success ⊢
          cases rom : romRead? image a.toNat w.bytes false with
          | some value => simp only [rom] at success ⊢;exact ih _ success
          | none =>
            simp only [rom,devs] at success ⊢
            cases dev : bigBoard.device? a with
            | none => simp only [dev] at success;cases success
            | some reg =>
              simp only [dev] at success ⊢
              split at success
              · rename_i ready
                simp only [ready,ite_true]
                exact ih _ success
              · cases success
  | store w a value atomic k ih =>
    by_cases aligned : a.toNat%w.bytes≠0
    · rw [Observed.interp,if_pos aligned] at success
      cases success
    simp only [Observed.interp,aligned,ite_false] at success ⊢
    cases small : smallBoard.inRam a w.bytes with
    | true =>
      have large := incl a w small
      simp only [small,large,ite_true] at success ⊢
      exact ih success
    | false =>
      cases large : bigBoard.inRam a w.bytes with
      | true =>
        have dev := (away a w large small).2
        cases atomic <;> simp only [small,Bool.false_eq_true,ite_false,ite_true,dev] at success <;> cases success
      | false =>
        simp only [small,large,ite_false] at success ⊢
        cases atomic with
        | true => cases success
        | false =>
          simp only [Bool.false_eq_true,ite_false,devs] at success ⊢
          cases dev : bigBoard.device? a with
          | none => simp only [dev] at success;cases success
          | some reg =>
            simp only [dev] at success ⊢
            split at success
            · rename_i ready
              simp only [ready,ite_true]
              exact ih success
            · cases success
theorem instruction (smallBoard bigBoard : Board) (image : List Segment)
    (incl : ∀ (a : Word) (w : Width),smallBoard.inRam a w.bytes=true → bigBoard.inRam a w.bytes=true)
    (away : ∀ (a : Word) (w : Width),bigBoard.inRam a w.bytes=true → smallBoard.inRam a w.bytes=false →
      romRead? image a.toNat w.bytes false=none ∧ smallBoard.device? a=none)
    (devs : ∀ a,smallBoard.device? a=bigBoard.device? a) {m o c after events}
    (success : (Observed.stepInstr smallBoard image m o).value=.ok c after events) :
    Observed.stepInstr bigBoard image m o=Observed.stepInstr smallBoard image m o := by
  cases aligned : m.core.pc.getLsbD 0 with
  | true => simp only [Observed.stepInstr,aligned,ite_true]
  | false =>
    simp only [Observed.stepInstr,aligned,ite_false] at success ⊢
    cases fetched : fetch image m.core.pc with
    | none => simp only [fetched]
    | some pair =>
      obtain ⟨bits,len⟩ := pair
      simp only [fetched] at success ⊢
      cases decoded : decode bits len with
      | none => simp only [decoded]
      | some instr =>
        simp only [decoded] at success ⊢
        exact effect smallBoard bigBoard image incl away devs success

end E5R.Thermostat.BoardRestriction
