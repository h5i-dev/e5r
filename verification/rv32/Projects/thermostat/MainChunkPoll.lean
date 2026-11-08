import Projects.thermostat.UartPoll
import Projects.thermostat.MainChunkReceiveCode
namespace E5R.Thermostat.MainChunkPoll
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def mask (status : Word) : Word := UartPoll.byte status &&& 1#32

theorem load (c : Core) (ram : Word → BitVec 8) (o : Oracle)
    (hp : c.pc=0x80000fb0#32) (hu : c.get 19=0x10000000#32) :
    Observed.stepInstr B img ⟨c,ram⟩ o =
      ⟨.ok (c.wr 11 (UartPoll.byte (o 0)) 0x80000fb4#32) ram [],[⟨0x10000005#32,.b,UartPoll.byte (o 0),0⟩]⟩ := by
  have hk := UartPlatform.load ⟨c,ram⟩ o 11 19 5#32 4#32 0x10000005#32 UartPlatform.lsr
    (by rw [hp];decide) (by rw [hp];exact cr2147487664)
    (by rw [hu];decide +kernel) (by decide +kernel) UartPlatform.lsr_device rfl rfl
  have hraw : devVal .b (o 0)=UartPoll.byte (o 0) := rfl
  rw [hraw] at hk
  simpa only [hp,UartPoll.extend_byte,show 0x80000fb0#32+4#32=0x80000fb4#32 by decide +kernel] using hk

/-- Actual three-instruction status test. Device reads remain arbitrary;
    the ready/not-ready branch is exactly the observed bit-zero value. -/
theorem test (c : Core) (ram : Word → BitVec 8) (status : Word) (ready : Bool)
    (hp : c.pc=0x80000fb0#32) (hu : c.get 19=0x10000000#32)
    (hr : taken .ne (mask status) (0 : Word)=ready) :
    ∃ d, Observed.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ [⟨0x10000005#32,.b,UartPoll.byte status,0⟩] [] ∧
      d.pc=(if ready then 0x80000e80#32 else 0x80000fba#32) ∧ d.get 11=mask status ∧
      (∀ r : Reg, r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 11 (UartPoll.byte status) 0x80000fb4#32
  let b := a.wr 11 (mask status) 0x80000fb6#32
  let d := b.goto (if ready then 0x80000e80#32 else 0x80000fba#32)
  have t0 : Observed.Step B img ⟨c,ram⟩ ⟨a,ram⟩ [⟨0x10000005#32,.b,UartPoll.byte status,0⟩] [] := by
    have hk := load c ram (fun _ => status) hp hu
    have hs : Observed.Step B img ⟨c,ram⟩ ⟨a,ram⟩ (Observed.stepInstr B img ⟨c,ram⟩ (fun _ => status)).reads [] :=
      .instr (fun _ => status) (by rw [hk])
    simpa only [hk] using hs
  have t1 : Observed.Step B img ⟨a,ram⟩ ⟨b,ram⟩ [] [] := by
    apply Observed.pure_step (m := ⟨a,ram⟩) (by change (0x80000fb4#32).getLsbD 0=false;decide) cr2147487668
    have a17 : a.get 11=UartPoll.byte status := by simp [a,Core.wr_get]
    rw [exec_opimm,a17];rfl
  have t2 : Observed.Step B img ⟨b,ram⟩ ⟨d,ram⟩ [] [] := by
    apply Observed.pure_step (m := ⟨b,ram⟩) (by change (0x80000fb6#32).getLsbD 0=false;decide) cr2147487670
    have b17 : b.get 11=mask status := by simp [b,Core.wr_get]
    rw [exec_branch,b17,Core.get_zero,hr]
    cases ready with
    | false => rfl
    | true =>
      simp only [ite_true]
      change jump b (0x80000fb6#32+0xfffffeca#32)=.done d
      rw [show 0x80000fb6#32+0xfffffeca#32=0x80000e80#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  refine ⟨d,.step t0 (.step t1 (.single t2)),rfl,?_,?_,by rfl⟩
  · simp [d,b,Core.wr_get]
  · intro reg hr;simp [d,b,a,Core.wr_get_ne,hr]
end E5R.Thermostat.MainChunkPoll
