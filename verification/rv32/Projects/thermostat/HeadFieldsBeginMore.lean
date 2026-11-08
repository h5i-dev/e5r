import Projects.thermostat.HeadFieldsBegin
import Projects.thermostat.HeadFieldsMore
namespace E5R.Thermostat.HeadFieldsBeginMore
open E5R E5R.Thermostat HttpRequestSpec

/-- A complete request line without an available header line actually returns
    incomplete/431 after initializing the header state and restoring the ABI. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (m te j minor length cap : Nat) (values : Reg → Word)
    (ready : HeadLineReady.At c ram sp m te j minor length cap)
    (hbody : ramRead ram (sp+3668#32) .w=1024#32) (hj : j≤1024) (hn : cap≤1024) (full : cap≤j+2) (hlen : length≤2048)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (stored : HeadSaved.At ram sp values) :
    ∃ n d after, 262≤n ∧ n≤282 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=values 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d values ∧
      HeadResultView.At after (sp+4904#32) (HeadFieldsMore.out length) ∧
      ViewFrame.Region ram after (sp+516#32) 2048 ∧ ViewFrame.Region ram after (sp+428#32) 25 ∧ d.sameCsr c := by
  obtain ⟨a,e,cleared,alo,ahi,begin,pc,fields,metadata,rx,app,saved,stack,csr⟩ :=
    HeadFieldsBegin.contract B c ram sp m te j minor length cap values ready hbody hj hn hm ha stored
  have atMore : e.pc=0x800033ea#32 := by simpa only [full,ite_true] using pc
  have word (off : Nat) (hlo : 20≤off) (hi : off+4≤56) :
      ramRead cleared (sp+BitVec.ofNat 32 off) .w=ramRead ram (sp+BitVec.ofNat 32 off) .w := by
    have w := ViewFrame.word metadata (off-20) (by omega)
    have offset : 20#32+BitVec.ofNat 32 (off-20)=BitVec.ofNat 32 off := by
      change BitVec.ofNat 32 20+BitVec.ofNat 32 (off-20)=BitVec.ofNat 32 off
      rw [←BitVec.ofNat_add,Nat.add_sub_of_le hlo]
    simpa only [BitVec.add_assoc,offset] using w
  obtain ⟨b,d,blo,bhi,ret,retPC,retSP,abi,result,csr2⟩ := HeadFieldsMore.contract B e cleared sp length values atMore stack
    ((word 48 (by decide) (by decide)).trans ready.lengthWord) ((word 36 (by decide) (by decide)).trans ready.maxHead)
    ((word 52 (by decide) (by decide)).trans ready.output) hlen hm ha saved
  refine ⟨a+b,d,HeadFieldsMore.memory cleared sp length,by omega,by omega,begin.trans ret,retPC,retSP,abi,result,?_,?_,csr2.trans csr⟩
  · have f := HeadFieldsMore.region cleared sp length 516 2048 (by decide) (by decide)
    exact fun i => (f i).trans (rx i)
  · have f := HeadFieldsMore.region cleared sp length 428 25 (by decide) (by decide)
    exact fun i => (f i).trans (app i)
end E5R.Thermostat.HeadFieldsBeginMore
