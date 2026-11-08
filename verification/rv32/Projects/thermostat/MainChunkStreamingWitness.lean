import Projects.thermostat.MainChunkStreaming
import Projects.thermostat.MainChunkBufferedWitness
namespace E5R.Thermostat.MainChunkStreamingWitness
open E5R E5R.Thermostat HttpRequestSpec
open MainChunkBufferedWitness
abbrev B := UartPlatform.board

def plan : ChunkReceivePlan.Plan :=
  ⟨fun _ => [0#32],fun _ => 1#32,fun k => BitVec.ofNat 32 (wire k).toNat⟩

theorem byte_roundtrip : ∀ b : BitVec 8, (UartPoll.byte (BitVec.ofNat 32 b.toNat)).setWidth 8=b := by
  decide +kernel

theorem valid : ChunkReceivePlan.Valid plan wire 91 14 := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 1#32≠0#32;decide +kernel),byte_roundtrip (wire k)⟩
  intro status hs
  change status∈[0#32] at hs
  have eq := List.mem_singleton.mp hs
  rw [eq]
  decide +kernel

theorem input : Observed.input (ChunkReceivePlan.logs plan 91 14)=WireSpec.ascii "4\r\nauto\r\n0\r\n\r\n" := by
  rw [ChunkReceivePlan.logs_input]
  decide +kernel

/-- Starting with only the parsed head counted as received, the actual ELF
    accepts all fourteen body bytes via RBR, with one not-ready poll per byte,
    and stores exactly `auto`. Header and committed application RAM survive. -/
theorem execution : ∃ n d after reads, n≤2170 ∧
    Observed.Steps B img n ⟨core,ram true⟩ ⟨d,after⟩ reads [] ∧
    Observed.input reads=WireSpec.ascii "4\r\nauto\r\n0\r\n\r\n" ∧ d.pc=0x8000106c#32 ∧
    ChunkBufferView.Body after sp 91 (WireSpec.ascii "auto") ∧
    ramRead after (sp+3656#32) .w=105#32 ∧ ramRead after (sp+3660#32) .w=95#32 ∧
    AppState.At after Spec.initial ∧ ViewFrame.Region (ram true) after (sp+132#32) 91 := by
  have complete : (ChunkBufferSpec.consume wire 14 91 91 cStart []).stop≠.needInput := by
    rw [MainChunkBufferedWitness.expected]
    decide +kernel
  obtain ⟨received,n,d,after,receivedBound,hn,trace,terminal,payload,appFrame,header,readBound⟩ :=
    MainChunkStreaming.contract wire plan 14 (body := []) (pre true) (by decide) (unread true)
      (by intro i;have := i.isLt;contradiction) rfl valid complete
  change n≤125*14+ChunkReceivePlan.cost plan 91 14 at hn
  have cost : ChunkReceivePlan.cost plan 91 14=420 := by decide +kernel
  rw [cost] at hn
  change MainChunkBuffered.Terminal after sp 91 (ChunkBufferSpec.consume wire 14 91 91 cStart []) d at terminal
  rw [MainChunkBufferedWitness.expected] at terminal
  change ChunkBufferView.Body after sp 91 (ChunkBufferSpec.consume wire 14 91 91 cStart []).body at payload
  rw [MainChunkBufferedWitness.expected] at payload
  change (ChunkBufferSpec.consume wire 14 91 91 cStart []).read≤91+received at readBound
  rw [MainChunkBufferedWitness.expected] at readBound
  have count : received=14 := by change 105≤91+received at readBound;omega
  rw [count] at trace
  rcases terminal with ⟨pc,obj,inv,rd,wr,layout,stack,mask,tag⟩
  exact ⟨n,d,after,ChunkReceivePlan.logs plan 91 14,by omega,trace,input,pc,payload,rd,wr,
    appFrame rfl Spec.initial (app true),header⟩
end E5R.Thermostat.MainChunkStreamingWitness
