import Projects.thermostat.MainLengthUart
namespace E5R.Thermostat.MainLengthPoll
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

/-- A complete real header wait cycle for any not-ready status, without a
    fabricated input byte or progress assumption. The fence is an actual step. -/
theorem pending (c : Core) (ram : Word → BitVec 8) (status : Word)
    (hp : c.pc=0x80000c6c#32) (uart : c.get 19=0x10000000#32)
    (notReady : MainLengthUart.byte status &&& 1#32=0#32) :
    ∃ d, Observed.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ [⟨0x10000005#32,.b,MainLengthUart.byte status,0⟩] [] ∧
      d.pc=0x80000c6c#32 ∧ (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 10 (MainLengthUart.byte status) 0x80000c70#32
  let b := a.wr 10 0#32 0x80000c72#32
  let z := b.goto 0x80000c68#32
  let d := z.goto 0x80000c6c#32
  have t0 : Observed.Step B img ⟨c,ram⟩ ⟨a,ram⟩ [⟨0x10000005#32,.b,MainLengthUart.byte status,0⟩] [] := by
    have actual := MainLengthUart.rx_load c ram (fun _ => status) hp uart
    have step : Observed.Step B img ⟨c,ram⟩ ⟨a,ram⟩ (Observed.stepInstr B img ⟨c,ram⟩ (fun _ => status)).reads [] :=
      .instr (fun _ => status) (by rw [actual])
    simpa only [actual] using step
  have t1 : Observed.Step B img ⟨a,ram⟩ ⟨b,ram⟩ [] [] := by
    apply Observed.pure_step (m := ⟨a,ram⟩) (by change (0x80000c70#32).getLsbD 0=false;decide) ml2147486832
    rw [exec_opimm,show a.get 10=MainLengthUart.byte status from by simp [a,Core.wr_get]]
    change Eff.done (a.wr 10 (MainLengthUart.byte status &&& 1#32) 0x80000c72#32)=_
    rw [notReady]
  have t2 : Observed.Step B img ⟨b,ram⟩ ⟨z,ram⟩ [] [] := by
    apply Observed.pure_step (m := ⟨b,ram⟩) (by change (0x80000c72#32).getLsbD 0=false;decide) ml2147486834
    rw [exec_branch,show b.get 10=0#32 from by simp [b,Core.wr_get],Core.get_zero]
    rw [show taken .eq 0#32 (0 : Word)=true by decide +kernel]
    simp only [ite_true]
    change jump b (0x80000c72#32+0xfffffff6#32)=_
    rw [show 0x80000c72#32+0xfffffff6#32=0x80000c68#32 by decide +kernel,jump_ok _ _ (by decide)]
  have t3 : Observed.Step B img ⟨z,ram⟩ ⟨d,ram⟩ [] [] := by
    apply Observed.pure_step (m := ⟨z,ram⟩) (by change (0x80000c68#32).getLsbD 0=false;decide) ml2147486824
    rfl
  refine ⟨d,?_,rfl,?_,by rfl⟩
  · simpa only [List.append_nil] using (Observed.Steps.single t0).trans ((Observed.Steps.single t1).trans ((Observed.Steps.single t2).trans (Observed.Steps.single t3)))
  · intro r ne;simp [d,z,b,a,Core.wr_get_ne,ne]
end E5R.Thermostat.MainLengthPoll
