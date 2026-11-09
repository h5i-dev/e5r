import Projects.thermostat.UartTxWaitSafety
import Projects.thermostat.StackUartTxPoll
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.StackUartTxWaitSafety
open E5R E5R.Thermostat ProtocolStreamSpec UartTxWaitSafety
abbrev B := StackBoard.board
theorem next {c : Core} (ram : Word → BitVec 8) (h : At c) (o : Oracle) :
    ∃ d reads, Observed.stepInstr B img ⟨c,ram⟩ o=⟨.ok d ram [],reads⟩ ∧
      (At d ∨ Exit d) ∧ LsrOnly reads ∧
      (∀ r : Reg, r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  rcases h with ⟨hp,hu,hm⟩
  rcases hp with hp|hp|hp|hp|hp
  · let d := c.wr 17 (UartPoll.byte (o 0)) 0x800007fc#32
    refine ⟨d,_,StackUartTxPoll.load c ram o hp hu,Or.inl ⟨Or.inr (Or.inl rfl),?_,hm⟩,
      Or.inr ⟨_,rfl⟩,?_,rfl⟩
    · simpa only [d,Core.wr_get_ne _ _ _ _ _ (by decide : (13:Reg)≠17)] using hu
    · intro r hr;exact Core.wr_get_ne _ _ _ _ _ hr
  · let d := c.wr 17 (c.get 17 &&& 32#32) 0x80000800#32
    refine ⟨d,[],?_,Or.inl ⟨Or.inr (Or.inr (Or.inl rfl)),?_,hm⟩,Or.inl rfl,?_,rfl⟩
    · rw [Observed.stepInstr_of (by rw [hp];decide) (by rw [hp];exact up2147485692),exec_opimm,hp]
      rfl
    · simpa only [d,Core.wr_get_ne _ _ _ _ _ (by decide : (13:Reg)≠17)] using hu
    · intro r hr;exact Core.wr_get_ne _ _ _ _ _ hr
  · let ready := taken .ne (c.get 17) (0 : Word)
    let d := c.goto (if ready then 0x800007ea#32 else 0x80000804#32)
    refine ⟨d,[],?_,?_,Or.inl rfl,fun _ _ => rfl,rfl⟩
    · rw [Observed.stepInstr_of (by rw [hp];decide) (by rw [hp];exact up2147485696),exec_branch,Core.get_zero,hp]
      cases he : ready with
      | false => change Observed.interp B img o (if ready=true then _ else _) ram 0 [] []=_;rw [he];simp only [d,he];rfl
      | true =>
        change Observed.interp B img o (if ready=true then _ else _) ram 0 [] []=_
        rw [he]
        simp only [ite_true]
        rw [show 0x80000800#32+0xffffffea#32=0x800007ea#32 by decide +kernel,jump_ok _ _ (by decide)]
        simp only [d,he,ite_true]
        rfl
    · cases he : ready with
      | false => exact Or.inl ⟨Or.inr (Or.inr (Or.inr (Or.inl (by simp [d,he])))),hu,hm⟩
      | true => exact Or.inr ⟨by simp [d,he],hu,hm⟩
  · let d := c.goto 0x80000808#32
    refine ⟨d,[],?_,Or.inl ⟨Or.inr (Or.inr (Or.inr (Or.inr rfl))),hu,hm⟩,
      Or.inl rfl,fun _ _ => rfl,rfl⟩
    rw [Observed.stepInstr_of (by rw [hp];decide) (by rw [hp];exact up2147485700)]
    change Observed.interp B img o (Eff.done (c.goto (c.pc+4#32))) ram 0 [] []=_
    rw [hp,show 0x80000804#32+4#32=0x80000808#32 by decide +kernel]
    rfl
  · let d := c.goto 0x800007f8#32
    refine ⟨d,[],?_,Or.inl ⟨Or.inl rfl,hu,hm⟩,Or.inl rfl,fun _ _ => rfl,rfl⟩
    rw [Observed.stepInstr_of (by rw [hp];decide) (by rw [hp];exact up2147485704),exec_jal,Core.set_zero,hp]
    rw [show 0x80000808#32+0xfffffff0#32=0x800007f8#32 by decide +kernel,jump_ok _ _ (by decide)]
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
  have quiet : Quiet.Step B img ⟨c,ram⟩ ⟨c.wr 12 (c.get 12+1#32) 0x800007ec#32,ram⟩ := by
    intro o
    rw [Observed.stepInstr_of (by rw [h.1];decide) (by rw [h.1];exact tx2147485674),exec_opimm,h.1]
    rfl
  exact Trace.no_escape quiet.det h.2.2

end E5R.Thermostat.StackUartTxWaitSafety
