import Projects.thermostat.UartPoll
namespace E5R.Thermostat.MainHeaderPoll
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

/-- A complete real header wait cycle for any not-ready status, without a
    fabricated input byte or progress assumption. The fence is an actual step. -/
theorem pending (c : Core) (ram : Word → BitVec 8) (status : Word)
    (hp : c.pc=0x80000ba2#32) (uart : c.get 19=0x10000000#32)
    (notReady : UartPoll.byte status &&& 1#32=0#32) :
    ∃ d, Observed.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ [⟨0x10000005#32,.b,UartPoll.byte status,0⟩] [] ∧
      d.pc=0x80000ba2#32 ∧ (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 10 (UartPoll.byte status) 0x80000ba6#32
  let b := a.wr 10 0#32 0x80000ba8#32
  let z := b.goto 0x80000b9e#32
  let d := z.goto 0x80000ba2#32
  have t0 : Observed.Step B img ⟨c,ram⟩ ⟨a,ram⟩ [⟨0x10000005#32,.b,UartPoll.byte status,0⟩] [] := by
    have actual := UartPoll.rx_load c ram (fun _ => status) hp uart
    have step : Observed.Step B img ⟨c,ram⟩ ⟨a,ram⟩ (Observed.stepInstr B img ⟨c,ram⟩ (fun _ => status)).reads [] :=
      .instr (fun _ => status) (by rw [actual])
    simpa only [actual] using step
  have t1 : Observed.Step B img ⟨a,ram⟩ ⟨b,ram⟩ [] [] := by
    apply Observed.pure_step (m := ⟨a,ram⟩) (by change (0x80000ba6#32).getLsbD 0=false;decide) up2147486630
    rw [exec_opimm,show a.get 10=UartPoll.byte status from by simp [a,Core.wr_get]]
    change Eff.done (a.wr 10 (UartPoll.byte status &&& 1#32) 0x80000ba8#32)=_
    rw [notReady]
  have t2 : Observed.Step B img ⟨b,ram⟩ ⟨z,ram⟩ [] [] := by
    apply Observed.pure_step (m := ⟨b,ram⟩) (by change (0x80000ba8#32).getLsbD 0=false;decide) up2147486632
    rw [exec_branch,show b.get 10=0#32 from by simp [b,Core.wr_get],Core.get_zero]
    rw [show taken .eq 0#32 (0 : Word)=true by decide +kernel]
    simp only [ite_true]
    change jump b (0x80000ba8#32+0xfffffff6#32)=_
    rw [show 0x80000ba8#32+0xfffffff6#32=0x80000b9e#32 by decide +kernel,jump_ok _ _ (by decide)]
  have t3 : Observed.Step B img ⟨z,ram⟩ ⟨d,ram⟩ [] [] := by
    apply Observed.pure_step (m := ⟨z,ram⟩) (by change (0x80000b9e#32).getLsbD 0=false;decide) up2147486622
    rfl
  refine ⟨d,?_,rfl,?_,by rfl⟩
  · simpa only [List.append_nil] using (Observed.Steps.single t0).trans ((Observed.Steps.single t1).trans ((Observed.Steps.single t2).trans (Observed.Steps.single t3)))
  · intro r ne;simp [d,z,b,a,Core.wr_get_ne,ne]
end E5R.Thermostat.MainHeaderPoll
