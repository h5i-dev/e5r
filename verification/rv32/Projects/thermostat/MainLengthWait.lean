import Projects.thermostat.MainLengthPoll
import Projects.thermostat.MainChunkWait
import Projects.thermostat.ChunkReceivePlan
namespace E5R.Thermostat.MainLengthWait
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def reads (pending : List Word) (ready datum : Word) : List Observed.Read :=
  MainChunkWait.reads (pending++[ready])++[⟨0x10000000#32,.b,MainLengthUart.byte datum,0⟩]

/-- A finite explicit LSR/RBR schedule for the actual header wait and byte
    store. No eventual-ready assertion is inferred from arbitrary device reads. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (pending : List Word) (ready datum : Word)
    (hp : c.pc=0x80000c6c#32) (uart : c.get 19=0x10000000#32)
    (notReady : ∀ status ∈ pending, MainLengthUart.byte status &&& 1#32=0#32)
    (isReady : MainLengthUart.byte ready &&& 1#32≠0#32) (destination : B.inRam (c.get 12) 1=true) :
    ∃ d after, Observed.Steps B img (4*pending.length+5) ⟨c,ram⟩ ⟨d,after⟩ (reads pending ready datum) [] ∧
      d.pc=0x80000c7c#32 ∧ d.get 12=c.get 12 ∧ d.get 19=c.get 19 ∧ d.sameCsr c ∧
      after (c.get 12)=(MainLengthUart.byte datum).setWidth 8 ∧ (∀ x, x≠c.get 12 → after x=ram x) ∧
      (∀ r : Reg, r≠10 → d.get r=c.get r) := by
  induction pending generalizing c with
  | nil =>
    obtain ⟨d,after,trace,pc,d12,d19,csr,value,frame,regs⟩ := MainLengthUart.rx_ready_full c ram ready datum hp uart isReady destination
    exact ⟨d,after,by simpa only [MainLengthUart.byte,UartPoll.byte,reads,MainChunkWait.reads,List.nil_append,List.map_cons,List.map_nil,List.cons_append,List.length_nil,Nat.mul_zero,Nat.zero_add] using trace,pc,d12,d19,csr,value,frame,regs⟩
  | cons status pending ih =>
    obtain ⟨a,ta,apc,ar,ac⟩ := MainLengthPoll.pending c ram status hp uart (notReady status (by simp))
    have a12 := ar 12 (by decide)
    obtain ⟨d,after,trace,pc,d12,d19,csr,value,frame,regs⟩ := ih a apc ((ar 19 (by decide)).trans uart)
      (fun s hs => notReady s (by simp [hs])) (by simpa only [a12] using destination)
    refine ⟨d,after,?_,pc,d12.trans a12,d19.trans (ar 19 (by decide)),csr.trans ac,?_,?_,?_⟩
    · have steps := ta.trans trace
      have count : 4+(4*pending.length+5)=4*(status::pending).length+5 := by simp only [List.length_cons];omega
      rw [count] at steps
      simpa only [MainLengthUart.byte,UartPoll.byte,reads,MainChunkWait.reads,List.cons_append,List.map_cons,List.singleton_append,List.append_assoc,List.nil_append] using steps
    · simpa only [a12] using value
    · intro x ne;exact frame x (by simpa only [a12] using ne)
    · intro r ne;exact (regs r ne).trans (ar r ne)

theorem input (pending : List Word) (ready datum : Word) :
    Observed.input (reads pending ready datum)=[(MainLengthUart.byte datum).setWidth 8] := by
  rw [reads,Observed.input_append,ChunkReceivePlan.lsr_input]
  rfl
end E5R.Thermostat.MainLengthWait
