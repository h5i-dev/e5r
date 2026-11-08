import Projects.thermostat.MainChunkPersistData
import Projects.thermostat.MainChunkCoreFrame
import Projects.thermostat.ChunkOutputView
namespace E5R.Thermostat.MainChunkStore
open E5R E5R.Thermostat HttpRequestSpec

/-- The result is copied to the real persisted main state, and the input
    cursor is advanced. Padding and non-Reject status bytes are unconstrained. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp index : Word)
    (next : CState) (out : COut)
    (hp : c.pc=0x80000f10#32) (h8 : c.get 8=sp+3204#32) (h23 : c.get 23=sp+3680#32)
    (hm : Memory.Block B sp 4928) (ha : sp.toNat%4=0)
    (hi : ramRead ram (sp+3656#32) .w=index)
    (hs : ChunkLayout.At ram (sp+4824#32) next) (ho : ChunkLayout.OutAt ram (sp+4824#32) out) :
    ∃ d after, Quiet.Steps B img 21 ⟨c,ram⟩ ⟨d,after⟩ ∧ d.pc=0x80000f62#32 ∧
      ChunkLayout.At after (sp+3680#32) next ∧ ramRead after (sp+3656#32) .w=index+1#32 ∧
      d.get 24=index+1#32 ∧ d.get 10=ChunkOutputView.tag out ∧
      (∀ status, out=.reject status → status<65536 → d.get 27=BitVec.ofNat 32 status) ∧
      (∀ x, (∀ i : Fin 4, x≠(sp+3656#32)+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 32, x≠(sp+3680#32)+BitVec.ofNat 32 i.val) → after x=ram x) ∧
      (∀ r : Reg, r=1 ∨ r=2 ∨ r=8 ∨ r=9 ∨ r=20 ∨ r=22 ∨ r=23 → d.get r=c.get r) ∧ MainChunkCoreFrame.At c d ∧ d.sameCsr c := by
  obtain ⟨d,trace,pc,v11,v12,v13,v14,v15,v16,v17,v5,cursor,tag,status,regs,csr⟩ :=
    MainChunkPersist.contract B c ram sp index h8 h23 hm ha hi hp
  have tag' : d.get 10=ChunkOutputView.tag out := by
    rw [tag]
    simpa only [BitVec.add_assoc,show 4824#32+32#32=4856#32 by decide +kernel] using ChunkOutputView.tag_load ho
  refine ⟨d,MainChunkPersist.memory ram sp index,trace,pc,
    MainChunkPersistData.state ram sp index next hs,MainChunkPersistData.cursor ram sp index,
    cursor,tag',?_,MainChunkPersistData.frame ram sp index,?_,?_,csr⟩
  · intro code he hc
    have hcode : ChunkLayout.OutAt ram (sp+4824#32) (.reject code) := by simpa only [he] using ho
    rw [status]
    simpa only [BitVec.add_assoc,show 4824#32+34#32=4858#32 by decide +kernel] using
      ChunkOutputView.status_load hcode hc
  · intro r hr
    apply regs r <;> (intro he;subst r;revert hr;decide +kernel)

  · intro r hr
    apply regs r <;> (intro he;subst r;revert hr;decide +kernel)

end E5R.Thermostat.MainChunkStore
