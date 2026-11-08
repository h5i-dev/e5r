import Projects.thermostat.HeadFieldsRejectStore
import Projects.thermostat.HeadEarlyFinish
namespace E5R.Thermostat.HeadFieldsReject
open E5R E5R.Thermostat

/-- Actual fields error stores and complete ABI return for any u16 status. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (values : Reg → Word) (status : Nat)
    (hp : c.pc=0x8000342c#32) (h2 : c.get 2=sp) (hdst : ramRead ram (sp+52#32) .w=sp+4904#32)
    (h1 : c.get 1=BitVec.ofNat 32 status) (hs : status<65536)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (saved : HeadSaved.At ram sp values) :
    ∃ d, Quiet.Steps B img 21 ⟨c,ram⟩ ⟨d,HeadResultStore.memory ram (sp+4904#32) 4#32 (BitVec.ofNat 32 status)⟩ ∧
      d.pc=values 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d values ∧
      HeadResultView.At (HeadResultStore.memory ram (sp+4904#32) 4#32 (BitVec.ofNat 32 status)) (sp+4904#32) (.reject status) ∧ d.sameCsr c := by
  have dstBlock : Memory.Block B (sp+4904#32) 12 := Memory.sub_block hm (off := 4904) (by decide) (by decide)
  have dstAlign : (sp+4904#32).toNat%4=0 := Memory.word_aligned sp 1226 ha
  have stack : Memory.Block B sp 384 := by
    simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := 384) (by decide) (by decide)
  obtain ⟨a,emit,pc,tag,dst,frame,csr⟩ := HeadFieldsRejectStore.contract B c ram sp (sp+4904#32) (BitVec.ofNat 32 status) h2 h1 hdst
    (by simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := 56) (by decide) (by decide)) ha dstBlock dstAlign hp
  obtain ⟨d,ret,endPC,endSP,abi,rest,csr2⟩ := HeadReturn.contract B a
    (HeadResultStore.memory ram (sp+4904#32) 4#32 (BitVec.ofNat 32 status)) sp values pc
    ((frame 2 (by decide) (by decide)).trans h2) stack ha (HeadResultFrame.reject_saved saved)
  exact ⟨d,emit.trans ret,endPC,endSP,abi,HeadResultView.reject ram (sp+4904#32) status hs,csr2.trans csr⟩
end E5R.Thermostat.HeadFieldsReject
