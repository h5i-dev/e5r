import Projects.thermostat.MainChunkPoll
import Projects.thermostat.Quiet
namespace E5R.Thermostat.MainChunkWait
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def reads (statuses : List Word) : List Observed.Read :=
  statuses.map fun status => ⟨0x10000005#32,.b,UartPoll.byte status,0⟩

theorem pause (c : Core) (ram : Word → BitVec 8) (hp : c.pc=0x80000fba#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000fb0#32 ∧
      (∀ r, d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.goto 0x80000fbe#32
  let d := a.goto 0x80000fb0#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact cr2147487674) fun o => ?_
    change Observed.interp B img o (Eff.done (c.goto (c.pc+4#32))) ram 0 [] []=_
    rw [hp,show 0x80000fba#32+4#32=0x80000fbe#32 by decide +kernel]
    rfl
  have t1 : Quiet.Step B img ⟨a,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by change (0x80000fbe#32).getLsbD 0=false;decide) cr2147487678 fun o => ?_
    rw [exec_jal,Core.set_zero]
    change Observed.interp B img o (jump a (0x80000fbe#32+0xfffffff2#32)) ram 0 [] []=_
    rw [show 0x80000fbe#32+0xfffffff2#32=0x80000fb0#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  exact ⟨d,.step t0 (.single t1),rfl,fun _ => rfl,rfl⟩

/-- A finite readiness certificate lists every status read. This theorem
    does not infer eventual readiness from the unconstrained UART model. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (pending : List Word) (ready : Word)
    (hp : c.pc=0x80000fb0#32) (hu : c.get 19=0x10000000#32)
    (hn : ∀ status ∈ pending, MainChunkPoll.mask status=0#32)
    (hr : MainChunkPoll.mask ready≠0#32) :
    ∃ d, Observed.Steps B img (5*pending.length+3) ⟨c,ram⟩ ⟨d,ram⟩
      (reads (pending++[ready])) [] ∧ d.pc=0x80000e80#32 ∧
      (∀ r : Reg, r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  induction pending generalizing c with
  | nil =>
    have ht : taken .ne (MainChunkPoll.mask ready) (0 : Word)=true := by simp [taken,hr]
    obtain ⟨d,trace,pc,mask,frame,csr⟩ := MainChunkPoll.test c ram ready true hp hu ht
    exact ⟨d,trace,pc,frame,csr⟩
  | cons status pending ih =>
    have hz : MainChunkPoll.mask status=0#32 := hn status (by simp)
    have ht : taken .ne (MainChunkPoll.mask status) (0 : Word)=false := by rw [hz];decide +kernel
    obtain ⟨a,test,pc,mask,frame,csr⟩ := MainChunkPoll.test c ram status false hp hu ht
    obtain ⟨b,pause,pc2,frame2,csr2⟩ := pause a ram pc
    have uart : b.get 19=0x10000000#32 := (frame2 19).trans ((frame 19 (by decide)).trans hu)
    obtain ⟨d,rest,pc3,frame3,csr3⟩ := ih b pc2 uart (fun s hs => hn s (by simp [hs]))
    refine ⟨d,?_,pc3,?_,csr3.trans (csr2.trans csr)⟩
    · have trace := (test.trans pause.observed).trans rest
      have count : (3+2)+(5*pending.length+3)=5*(status::pending).length+3 := by simp only [List.length_cons];omega
      rw [count] at trace
      simpa only [reads,List.cons_append,List.map_cons,List.append_nil,List.cons_append,
        List.nil_append] using trace
    · intro r hreg
      exact (frame3 r hreg).trans ((frame2 r).trans (frame r hreg))

end E5R.Thermostat.MainChunkWait
