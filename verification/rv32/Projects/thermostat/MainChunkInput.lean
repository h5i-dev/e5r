import Projects.thermostat.MainChunkCallData
import Projects.thermostat.MainChunkCoreFrame
import Projects.thermostat.ChunkStep
namespace E5R.Thermostat.MainChunkInput
open E5R E5R.Thermostat HttpRequestSpec

structure Ready (B : Board) (c : Core) (ram : Word → BitVec 8)
    (sp rx lim index maxBody : Word) (s : CState) : Prop where
  pc : c.pc=0x80000eaa#32
  stackPtr : c.get 2=sp
  fp : c.get 8=sp+3204#32
  statePtr : c.get 23=sp+3680#32
  cursor : c.get 24=index
  stack : Memory.Block B sp 4928
  align : sp.toNat%4=0
  limits : Memory.Block B lim 8
  limitsAlign : lim.toNat%4=0
  rxByte : B.inRam (rx+index) 1=true
  rxPtr : ramRead ram (sp+3312#32) .w=rx
  limitPtr : ramRead ram (sp+3636#32) .w=lim
  max : ramRead ram (lim+4#32) .w=maxBody
  object : ChunkLayout.At ram (sp+3680#32) s
  inv : ChunkSpecInvariant.Inv maxBody.toNat s

/-- Derive the complete callee prerequisites from actual main loads, stores,
    and the call. No decoder result or parser success is assumed here. -/
theorem call (B : Board) (c : Core) (ram : Word → BitVec 8)
    (sp rx lim index maxBody : Word) (s : CState)
    (h : Ready B c ram sp rx lim index maxBody s) :
    ∃ d after, Quiet.Steps B img 30 ⟨c,ram⟩ ⟨d,after⟩ ∧
      ChunkStep.Pre B d after (sp+4864#32) (sp+4824#32) s (ram (rx+index)) maxBody.toNat ∧
      d.get 1=0x80000f10#32 ∧ d.get 2=sp ∧ d.get 8=sp+3204#32 ∧
      d.get 23=sp+3680#32 ∧ d.get 24=index ∧ d.get 20=BitVec.ofNat 32 (ram (rx+index)).toNat ∧
      (∀ x, (∀ i : Fin 32, x≠(sp+4864#32)+BitVec.ofNat 32 i.val) → after x=ram x) ∧
      d.get 22=c.get 22 ∧ MainChunkCoreFrame.At c d ∧ d.sameCsr c := by
  obtain ⟨d,trace,pc,a0,a1,a2,a4,a5,a6,a7,t0,t1,t2,cache,limit,ra,regs,csr⟩ :=
    MainChunkCall.contract B c ram sp rx lim index maxBody h.stackPtr h.fp h.statePtr h.cursor h.stack h.align
      h.limits h.limitsAlign h.rxByte h.rxPtr h.limitPtr h.max h.pc
  have pre : ChunkStep.Pre B d (MainChunkCall.memory ram sp rx lim index maxBody)
      (sp+4864#32) (sp+4824#32) s (ram (rx+index)) maxBody.toNat := by
    constructor
    · exact pc
    · exact a0
    · exact a1
    · exact a2
    · simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using limit
    · exact Memory.sub_block h.stack (off := 4864) (by decide) (by decide)
    · exact Memory.sub_block h.stack (off := 4824) (by decide) (by decide)
    · exact Memory.word_aligned sp 1216 h.align
    · exact Memory.word_aligned sp 1206 h.align
    · exact MainChunkCallData.state ram sp rx lim index maxBody s h.object
    · exact h.inv
    · exact maxBody.isLt
  have vSp := (regs 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.stackPtr
  have vFp := (regs 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.fp
  have vStatePtr := (regs 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.statePtr
  have vCursor := (regs 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.cursor
  have stable : MainChunkCoreFrame.At c d := by
    intro r hr
    apply regs r <;> (intro he;subst r;revert hr;decide +kernel)
  exact ⟨d,MainChunkCall.memory ram sp rx lim index maxBody,trace,pre,ra,vSp,vFp,vStatePtr,vCursor,cache,
    MainChunkCallData.frame ram sp rx lim index maxBody,
    regs 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),stable,csr⟩
end E5R.Thermostat.MainChunkInput
