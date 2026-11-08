import Projects.thermostat.HeadFieldsZero
import Projects.thermostat.HeadFieldsGuard
import Projects.thermostat.HeadFieldsSetupMemory
import Projects.thermostat.HeadFieldsRegs
import Projects.thermostat.HeadLineReady
namespace E5R.Thermostat.HeadFieldsBegin
open E5R E5R.Thermostat HttpRequestSpec

/-- Actual first header-loop entry: the memset, received-capacity guard and
    real setup establish all loop registers, empty fields, metadata and frames. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (m te j minor length cap : Nat) (values : Reg → Word)
    (ready : HeadLineReady.At c ram sp m te j minor length cap)
    (hbody : ramRead ram (sp+3668#32) .w=1024#32) (hj : j≤1024) (hn : cap≤1024)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (stored : HeadSaved.At ram sp values) :
    ∃ n d after, 239≤n ∧ n≤257 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      (if cap≤j+2 then d.pc=0x800033ea#32 else HeadFieldsRegs.At d sp (j+2) length minor Fields.empty) ∧
      HeadFieldsView.At after sp Fields.empty ∧ ViewFrame.Region ram after (sp+20#32) 36 ∧
      ViewFrame.Region ram after (sp+516#32) 2048 ∧ ViewFrame.Region ram after (sp+428#32) 25 ∧
      HeadSaved.At after sp values ∧ d.get 2=sp ∧ d.sameCsr c := by
  let zeroRAM := HeadFieldsZero.memory ram sp
  obtain ⟨a,clear,pc,stackA,frame,csr⟩ := HeadFieldsZero.contract B c ram sp ready.pc ready.stack hm ha
  have stack : Memory.Block B sp 56 := by
    simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := 56) (by decide) (by decide)
  have capWord : ramRead zeroRAM (sp+40#32) .w=BitVec.ofNat 32 cap :=
    (HeadFieldsZero.word_frame ram sp 40 (by decide) (by decide)).trans ready.cap
  obtain ⟨b,guard,pc2,position,capReg,frame2,csr2⟩ := HeadFieldsGuard.contract B a zeroRAM sp j cap pc stackA
    ((frame 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.firstLine) capWord stack ha hj hn
  have source2 (r : Reg) (h1 : r≠1) (h10 : r≠10) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) (h15 : r≠15) (h16 : r≠16) (h24 : r≠24) : b.get r=c.get r :=
    (frame2 r h24 h10).trans (frame r h1 h10 h11 h12 h13 h14 h15 h16)
  have stackB : b.get 2=sp := (frame2 2 (by decide) (by decide)).trans stackA
  by_cases full : cap≤j+2
  · refine ⟨239,b,zeroRAM,by decide,by decide,clear.trans guard,?_,HeadFieldsView.initial B ram sp hm,
      HeadFieldsZero.region ram sp 20 36 (by decide) (by decide),HeadFieldsZero.region ram sp 516 2048 (by decide) (by decide),
      HeadFieldsZero.region ram sp 428 25 (by decide) (by decide),HeadFieldsZero.saved stored,stackB,csr2.trans csr⟩
    simpa only [full,ite_true] using pc2
  · have atSetup : b.pc=0x80002f28#32 := by simpa only [full,ite_false] using pc2
    have bodyWord : ramRead zeroRAM (sp+3668#32) .w=1024#32 :=
      (HeadFieldsZero.word_frame ram sp 3668 (by decide) (by decide)).trans hbody
    have lengthWord : ramRead zeroRAM (sp+48#32) .w=BitVec.ofNat 32 length :=
      (HeadFieldsZero.word_frame ram sp 48 (by decide) (by decide)).trans ready.lengthWord
    have bufWord : ramRead zeroRAM (sp+44#32) .w=sp+516#32 :=
      (HeadFieldsZero.word_frame ram sp 44 (by decide) (by decide)).trans ready.buffer
    obtain ⟨d,setup,pc3,zeroTE,zeroCount,bufNext,lengthBefore,negLength,lf,cr,tcharMin,digitMin,maskWidth,colon,upperEnd,frame3,csr3⟩ :=
      HeadFieldsSetup.contract B b zeroRAM sp (sp+516#32) 1024#32 (BitVec.ofNat 32 length) stackB
        ((source2 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.limits) bodyWord lengthWord bufWord hm ha atSetup
    have source3 (r : Reg) (h1 : r≠1) (h10 : r≠10) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) (h15 : r≠15) (h16 : r≠16)
        (h24 : r≠24) (h23 : r≠23) (h9 : r≠9) (h22 : r≠22) (h17 : r≠17) (h5 : r≠5) (h6 : r≠6) (h7 : r≠7) (h28 : r≠28) (h27 : r≠27) : d.get r=c.get r :=
      (frame3 r h23 h9 h10 h11 h22 h16 h17 h5 h6 h7 h28 h27).trans (source2 r h1 h10 h11 h12 h13 h14 h15 h16 h24)
    have stackD : d.get 2=sp := (frame3 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans stackB
    refine ⟨257,d,_,by decide,by decide,(clear.trans guard).trans setup,?_,
      HeadFieldsSetupMemory.fields (sp+516#32) 1024#32 (BitVec.ofNat 32 length) (HeadFieldsView.initial B ram sp hm),?_,?_,?_,
      HeadFieldsSetupMemory.saved (sp+516#32) 1024#32 (BitVec.ofNat 32 length) (HeadFieldsZero.saved stored),stackD,csr3.trans (csr2.trans csr)⟩
    · simp only [full,ite_false]
      refine ⟨pc3,stackD,?_,lf,cr,tcharMin,digitMin,maskWidth,colon,upperEnd,?_,?_,?_,?_,negLength⟩
      · exact (frame3 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans position
      · exact (source3 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.version
      · exact (source3 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.inverse
      · simpa only [Fields.empty,List.length_nil] using zeroCount
      · simpa only [Fields.empty,Bool.false_eq_true,ite_false] using zeroTE
    · have f1 := HeadFieldsZero.region ram sp 20 36 (by decide) (by decide)
      have f2 := HeadFieldsSetupMemory.region zeroRAM sp (sp+516#32) 1024#32 (BitVec.ofNat 32 length) 20 36 (by decide) (by decide)
      exact fun i => (f2 i).trans (f1 i)
    · have f1 := HeadFieldsZero.region ram sp 516 2048 (by decide) (by decide)
      have f2 := HeadFieldsSetupMemory.region zeroRAM sp (sp+516#32) 1024#32 (BitVec.ofNat 32 length) 516 2048 (by decide) (by decide)
      exact fun i => (f2 i).trans (f1 i)
    · have f1 := HeadFieldsZero.region ram sp 428 25 (by decide) (by decide)
      have f2 := HeadFieldsSetupMemory.region zeroRAM sp (sp+516#32) 1024#32 (BitVec.ofNat 32 length) 428 25 (by decide) (by decide)
      exact fun i => (f2 i).trans (f1 i)
end E5R.Thermostat.HeadFieldsBegin
