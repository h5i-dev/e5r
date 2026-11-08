import Projects.thermostat.HeadFieldsLength
import Projects.thermostat.HeadFieldsFullBranch
import Projects.thermostat.HeadFieldsTooLong
import Projects.thermostat.HeadFieldsFailStore
import Projects.thermostat.HeadFieldsIncomplete
import Projects.thermostat.HeadEarlyFinish
import Projects.thermostat.HeadTargetMath
namespace E5R.Thermostat.HeadFieldsMore
open E5R E5R.Thermostat HttpRequestSpec

def out (length : Nat) : HeadR := if 1024≤length then .reject 431 else .incomplete

def memory (ram : Word → BitVec 8) (sp : Word) (length : Nat) :=
  if 1024≤length then HeadResultStore.memory ram (sp+4904#32) 4#32 431#32 else HeadIncomplete.memory ram (sp+4904#32)

theorem result (ram : Word → BitVec 8) (sp : Word) (length : Nat) :
    HeadResultView.At (memory ram sp length) (sp+4904#32) (out length) := by
  by_cases full : 1024≤length
  · simpa only [memory,out,full,ite_true] using HeadResultView.reject ram (sp+4904#32) 431 (by decide)
  · simpa only [memory,out,full,ite_false] using HeadResultView.incomplete ram (sp+4904#32)

theorem saved (ram : Word → BitVec 8) (sp : Word) (length : Nat) (values : Reg → Word) (h : HeadSaved.At ram sp values) :
    HeadSaved.At (memory ram sp length) sp values := by
  unfold memory
  split
  · exact HeadResultFrame.reject_saved h
  · exact HeadResultFrame.incomplete_saved h

theorem region (ram : Word → BitVec 8) (sp : Word) (length off len : Nat)
    (hb : off+len≤4294967296) (hs : off+len≤4904 ∨ 4916≤off) :
    ViewFrame.Region ram (memory ram sp length) (sp+BitVec.ofNat 32 off) len := by
  unfold memory
  split
  · exact HeadResultFrame.reject_region ram sp 4#32 431#32 off len hb hs
  · exact HeadResultFrame.incomplete_region ram sp off len hb hs

/-- Actual fields.More return. The full/short decision is loaded from RAM;
    incomplete versus 431 and every result store/ABI restore are real steps. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (length : Nat) (values : Reg → Word)
    (hp : c.pc=0x800033ea#32) (h2 : c.get 2=sp)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hmax : ramRead ram (sp+36#32) .w=1024#32)
    (hdst : ramRead ram (sp+52#32) .w=sp+4904#32)
    (hlen : length≤2048) (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (stored : HeadSaved.At ram sp values) :
    ∃ n d, 23≤n ∧ n≤25 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,memory ram sp length⟩ ∧
      d.pc=values 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d values ∧
      HeadResultView.At (memory ram sp length) (sp+4904#32) (out length) ∧ d.sameCsr c := by
  have stack : Memory.Block B sp 56 := by
    simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := 56) (by decide) (by decide)
  have retStack : Memory.Block B sp 384 := by
    simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := 384) (by decide) (by decide)
  have block : Memory.Block B (sp+4904#32) 12 := Memory.sub_block hm (off := 4904) (by decide) (by decide)
  have align : (sp+4904#32).toNat%4=0 := Memory.word_aligned sp 1226 ha
  obtain ⟨a,load,pc,len,max,frame,csr⟩ := HeadFieldsLength.contract B c ram sp (BitVec.ofNat 32 length) 1024#32 h2 hraw hmax stack ha hp
  obtain ⟨b,branch,pc2,frame2,csr2⟩ := HeadFieldsFullBranch.contract B a ram (BitVec.ofNat 32 length) 1024#32
    (decide (1024≤length)) pc len max (HeadTargetMath.geu length 1024 hlen (by decide))
  have source (r : Reg) (h10 : r≠10) (h11 : r≠11) : b.get r=c.get r := (frame2 r).trans (frame r h10 h11)
  have stackB : b.get 2=sp := (source 2 (by decide) (by decide)).trans h2
  by_cases full : 1024≤length
  · have atFull : b.pc=0x80003414#32 := by simpa only [full,decide_true,ite_true] using pc2
    obtain ⟨e,setup,pc3,tag,status,frame3,csr3⟩ := HeadFieldsTooLong.contract B b ram atFull
    obtain ⟨f,emit,pc4,dst,frame4,csr4⟩ := HeadFieldsFailStore.contract B e ram sp (sp+4904#32) 4#32 431#32
      ((frame3 2 (by decide) (by decide)).trans stackB) tag status hdst stack ha block align pc3
    have mem : memory ram sp length=HeadResultStore.memory ram (sp+4904#32) 4#32 431#32 := by simp only [memory,full,ite_true]
    obtain ⟨d,ret,endPC,endSP,abi,rest,csr5⟩ := HeadReturn.contract B f (memory ram sp length) sp values pc4
      ((frame4 2 (by decide)).trans ((frame3 2 (by decide) (by decide)).trans stackB)) retStack ha (saved ram sp length values stored)
    rw [←mem] at emit
    exact ⟨25,d,by decide,by decide,(((load.trans branch).trans setup).trans emit).trans ret,endPC,endSP,abi,result ram sp length,csr5.trans (csr4.trans (csr3.trans (csr2.trans csr)))⟩
  · have atShort : b.pc=0x800033f2#32 := by simpa only [full,decide_false,Bool.false_eq_true,ite_false] using pc2
    obtain ⟨e,emit,pc3,tag,dst,frame3,csr3⟩ := HeadFieldsIncomplete.contract B b ram sp (sp+4904#32) stackB hdst stack ha block align atShort
    have mem : memory ram sp length=HeadIncomplete.memory ram (sp+4904#32) := by simp only [memory,full,ite_false]
    obtain ⟨d,ret,endPC,endSP,abi,rest,csr4⟩ := HeadReturn.contract B e (memory ram sp length) sp values pc3
      ((frame3 2 (by decide) (by decide)).trans stackB) retStack ha (saved ram sp length values stored)
    rw [←mem] at emit
    exact ⟨23,d,by decide,by decide,(load.trans branch).trans (emit.trans ret),endPC,endSP,abi,result ram sp length,csr4.trans (csr3.trans (csr2.trans csr))⟩
end E5R.Thermostat.HeadFieldsMore
