import Projects.thermostat.StackUartPoll
import Projects.thermostat.MainHeaderWaitSafety
set_option autoImplicit false
namespace E5R.Thermostat.StackHeaderWait
open E5R E5R.Thermostat
abbrev B := StackBoard.board
abbrev Waiting := MainHeaderWaitSafety.Waiting
abbrev At := MainHeaderWaitSafety.At
abbrev Exit := MainHeaderWaitSafety.Exit
abbrev LsrOnly := MainHeaderWaitSafety.LsrOnly

/-- Every oracle choice inside the actual header wait is safe. Arbitrarily
    many not-ready status reads require no input arrival or fairness premise. -/
theorem next {c : Core} (ram : Word → BitVec 8) (h : At c) (o : Oracle) :
    ∃ d reads, Observed.stepInstr B img ⟨c,ram⟩ o=⟨.ok d ram [],reads⟩ ∧
      (At d ∨ Exit d) ∧ LsrOnly reads ∧ (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  rcases h with ⟨hp,hu,hm⟩
  rcases hp with hp|hp|hp|hp
  · let d := c.wr 10 (UartPoll.byte (o 0)) 0x80000ba6#32
    refine ⟨d,_,StackUartPoll.rx_load c ram o hp hu,Or.inl ⟨Or.inr (Or.inl rfl),?_,hm⟩,Or.inr ⟨_,rfl⟩,?_,rfl⟩
    · exact (Core.wr_get_ne _ _ _ _ _ (by decide : (19 : Reg)≠10)).trans hu
    · intro r ne;exact Core.wr_get_ne _ _ _ _ _ ne
  · let d := c.wr 10 (c.get 10 &&& 1#32) 0x80000ba8#32
    refine ⟨d,[],?_,Or.inl ⟨Or.inr (Or.inr (Or.inl rfl)),?_,hm⟩,Or.inl rfl,?_,rfl⟩
    · rw [Observed.stepInstr_of (by rw [hp];decide) (by rw [hp];exact up2147486630),exec_opimm,hp]
      rfl
    · exact (Core.wr_get_ne _ _ _ _ _ (by decide : (19 : Reg)≠10)).trans hu
    · intro r ne;exact Core.wr_get_ne _ _ _ _ _ ne
  · let notReady := taken .eq (c.get 10) (0 : Word)
    let d := c.goto (if notReady then 0x80000b9e#32 else 0x80000baa#32)
    refine ⟨d,[],?_,?_,Or.inl rfl,fun _ _ => rfl,rfl⟩
    · rw [Observed.stepInstr_of (by rw [hp];decide) (by rw [hp];exact up2147486632),exec_branch,Core.get_zero,hp]
      cases branch : notReady with
      | false => change Observed.interp B img o (if notReady=true then _ else _) ram 0 [] []=_;rw [branch];simp only [d,branch];rfl
      | true =>
        change Observed.interp B img o (if notReady=true then _ else _) ram 0 [] []=_
        rw [branch]
        simp only [ite_true]
        rw [show 0x80000ba8#32+0xfffffff6#32=0x80000b9e#32 by decide +kernel,jump_ok _ _ (by decide)]
        simp only [d,branch,ite_true]
        rfl
    · cases branch : notReady with
      | false => exact Or.inr ⟨by simp [d,branch],hu,hm⟩
      | true => exact Or.inl ⟨Or.inr (Or.inr (Or.inr (by simp [d,branch]))),hu,hm⟩
  · let d := c.goto 0x80000ba2#32
    refine ⟨d,[],?_,Or.inl ⟨Or.inl rfl,hu,hm⟩,Or.inl rfl,fun _ _ => rfl,rfl⟩
    rw [Observed.stepInstr_of (by rw [hp];decide) (by rw [hp];exact up2147486622)]
    change Observed.interp B img o (Eff.done (c.goto (c.pc+4#32))) ram 0 [] []=_
    rw [hp,show 0x80000b9e#32+4#32=0x80000ba2#32 by decide +kernel]
    rfl

theorem safe {c ram} (h : At c) : ¬Escapes B img ⟨c,ram⟩ := by
  rintro (⟨o,f,hf⟩|⟨code,e,enabled,_⟩)
  · obtain ⟨d,reads,he,_⟩ := next ram h o
    have erase := Observed.erase_step B img ⟨c,ram⟩ o
    rw [he] at erase
    rw [←erase] at hf
    cases hf
  · simp [irqEnabled,h.2.2] at enabled

/-- Every actual platform/IRQ-aware observed step remains in the wait
    invariant or reaches the ready cutpoint. Only LSR reads occur here. -/
theorem step {c ram d reads evs} (h : At c)
    (actual : Observed.Step B img ⟨c,ram⟩ d reads evs) :
    d.ram=ram ∧ (At d.core ∨ Exit d.core) ∧ LsrOnly reads ∧ evs=[] := by
  cases actual with
  | instr o he =>
    obtain ⟨e,log,hk,post,only,frame,csr⟩ := next ram h o
    rw [hk] at he
    cases he
    exact ⟨rfl,post,by simpa only [hk] using only,rfl⟩
  | irq code enabled _ => simp [irqEnabled,h.2.2] at enabled
theorem exit_safe {c ram} (h : Exit c) : ¬Escapes B img ⟨c,ram⟩ := by
  rintro (⟨o,f,hf⟩|⟨code,e,enabled,_⟩)
  · have he := StackUartPoll.rx_data_load c ram o h.1 h.2.1
    have erase := Observed.erase_step B img ⟨c,ram⟩ o
    rw [he] at erase
    rw [←erase] at hf
    cases hf
  · simp [irqEnabled,h.2.2] at enabled

end E5R.Thermostat.StackHeaderWait
