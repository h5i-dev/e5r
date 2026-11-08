import Projects.thermostat.HeadRequestReject
import Projects.thermostat.HeadVersionReload
namespace E5R.Thermostat.HeadRequestRejectPath
open E5R E5R.Thermostat

/-- Both actual request-line rejection cutpoints, including the deferred
    output-pointer load used by malformed/unsupported versions. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (values : Reg → Word) (status : Nat)
    (hp : c.pc=0x80002efa#32 ∨ c.pc=0x80002efc#32) (h2 : c.get 2=sp)
    (hword : c.pc=0x80002efa#32 → ramRead ram (sp+52#32) .w=sp+4904#32)
    (h10 : c.pc=0x80002efc#32 → c.get 10=sp+4904#32)
    (h15 : c.get 15=BitVec.ofNat 32 status) (hs : status<65536)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (saved : HeadSaved.At ram sp values) :
    ∃ n d, 20≤n ∧ n≤21 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,HeadResultStore.memory ram (sp+4904#32) 4#32 (BitVec.ofNat 32 status)⟩ ∧
      d.pc=values 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d values ∧
      HeadResultView.At (HeadResultStore.memory ram (sp+4904#32) 4#32 (BitVec.ofNat 32 status)) (sp+4904#32) (.reject status) ∧ d.sameCsr c := by
  by_cases reload : c.pc=0x80002efa#32
  · have stack : Memory.Block B sp 56 := by
      simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := 56) (by decide) (by decide)
    obtain ⟨a,load,pc,dst,frame,csr⟩ := HeadVersionReload.contract B c ram sp (sp+4904#32) h2 (hword reload) stack ha reload
    obtain ⟨d,finish,endPC,endSP,abi,result,csr2⟩ := HeadRequestReject.contract B a ram sp values status pc
      ((frame 2 (by decide)).trans h2) dst ((frame 15 (by decide)).trans h15) hs hm ha saved
    exact ⟨21,d,by decide,by decide,load.trans finish,endPC,endSP,abi,result,csr2.trans csr⟩
  · have direct : c.pc=0x80002efc#32 := hp.resolve_left reload
    obtain ⟨d,finish,endPC,endSP,abi,result,csr⟩ := HeadRequestReject.contract B c ram sp values status direct h2 (h10 direct) h15 hs hm ha saved
    exact ⟨20,d,by decide,by decide,finish,endPC,endSP,abi,result,csr⟩
end E5R.Thermostat.HeadRequestRejectPath
