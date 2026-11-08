import Projects.thermostat.HeadMethodRejectStore
import Projects.thermostat.HeadEarlyFinish
namespace E5R.Thermostat.HeadMethodRejectFinish
open E5R E5R.Thermostat

/-- Actual request-line rejection stores followed by the complete ABI epilogue. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (values : Reg → Word)
    (hp : c.pc=0x80002efc#32) (h2 : c.get 2=sp) (h10 : c.get 10=sp+4904#32) (h15 : c.get 15=400#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (saved : HeadSaved.At ram sp values) :
    ∃ d, Quiet.Steps B img 20 ⟨c,ram⟩ ⟨d,HeadEarlyFinish.memory ram sp .bad⟩ ∧
      d.pc=values 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d values ∧ d.sameCsr c := by
  have dstBlock : Memory.Block B (sp+4904#32) 12 := Memory.sub_block hm (off := 4904) (by decide) (by decide)
  have dstAlign : (sp+4904#32).toNat%4=0 := Memory.word_aligned sp 1226 ha
  have stack : Memory.Block B sp 384 := by
    simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := 384) (by decide) (by decide)
  obtain ⟨a,emit,pc,tag,frame,csr⟩ := HeadMethodRejectStore.contract B c ram (sp+4904#32) 400#32 h10 h15 dstBlock dstAlign hp
  obtain ⟨d,ret,endPC,endSP,abi,rest,csr2⟩ := HeadReturn.contract B a (HeadEarlyFinish.memory ram sp .bad) sp values pc
    ((frame 2 (by decide)).trans h2) stack ha (HeadEarlyFinish.saved saved)
  exact ⟨d,emit.trans ret,endPC,endSP,abi,csr2.trans csr⟩
end E5R.Thermostat.HeadMethodRejectFinish
