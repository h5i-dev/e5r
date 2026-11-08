import Projects.thermostat.MainServeNextMemory
import Projects.thermostat.MainServeNextValidBranch
import Projects.thermostat.MainServeNextReadyBranch
import Projects.thermostat.MainSavedGpr
namespace E5R.Thermostat.MainServeNextCore
open E5R E5R.Thermostat

/-- Actual common successful Next path, including two real264-byte memcpy
    calls and both real result tests. All intermediate padding is actual RAM. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc=0x80000a9a#32) (h2 : c.get 2=sp) (h8 : c.get 8=sp+3204#32)
    (h9 : c.get 9=1#32) (h18 : c.get 18=0#32) (h21 : c.get 21=0xffffffff#32) (h22 : c.get 22=1#32)
    (payload : MainNextLengthPayloadWords.At ram sp) (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 755 ⟨c,ram⟩ ⟨d,MainServeNextMemory.memory ram sp⟩ ∧ d.pc=0x80000b50#32 ∧
      MainSavedGpr.Frame c d ∧ d.sameCsr c := by
  let r0 := MainServeNextMemory.front ram sp
  let r1 := MainServeNextMemory.firstCopy ram sp
  let r2 := MainServeNextMemory.firstPack ram sp
  let r3 := MainServeNextMemory.zeroStage ram sp
  let r4 := MainServeNextMemory.secondCopy ram sp
  obtain ⟨a,ta,apc,_,_,ar,ac⟩ := MainServeNextFront.contract B c ram sp h8 h22 payload stack aligned hp
  have fa := MainSavedGpr.temps2 ar
  have a2 : a.get 2=sp := (fa 2 (by decide)).trans h2
  obtain ⟨b,tb,bpc,b2,bs,bc⟩ := MainServeNextCopyOne.contract B a r0 sp apc a2 stack aligned
  have fb := MainSavedGpr.returned bs (b2.trans a2.symm)
  have ab := MainSavedGpr.trans fa fb
  obtain ⟨d,td,dpc,_,_,_,d13,dr,dc⟩ := MainServeNextPackOne.contract B b r1 sp _ _ _
    ((ab 8 (by decide)).trans h8) stack aligned ((ab 9 (by decide)).trans h9) ((ab 18 (by decide)).trans h18) rfl rfl rfl bpc
  have fd := MainSavedGpr.temps4 dr
  have ad := MainSavedGpr.trans ab fd
  obtain ⟨e,te,epc,er,ec⟩ := MainServeNextValidBranch.contract B d r2 0#32 0xffffffff#32 true dpc d13 ((ad 21 (by decide)).trans h21) (by decide +kernel)
  have epc' : e.pc=0x80000aee#32 := by simpa only [ite_true] using epc
  have fe : MainSavedGpr.Frame d e := fun rr _ => er rr
  have ae := MainSavedGpr.trans ad fe
  have zero := MainServeNextMemory.zero_input ram sp
  obtain ⟨f,tf,fpc,_,_,fr,fc⟩ := MainServeNextZeroStage.contract B e r2 sp ((ae 8 (by decide)).trans h8) stack aligned zero.1 zero.2 epc'
  have ff := MainSavedGpr.temps2 fr
  have af := MainSavedGpr.trans ae ff
  have f2 : f.get 2=sp := (af 2 (by decide)).trans h2
  obtain ⟨g,tg,gpc,g2,gs,gc⟩ := MainServeNextCopyTwo.contract B f r3 sp fpc f2 stack aligned
  have fg := MainSavedGpr.returned gs (g2.trans f2.symm)
  have ag := MainSavedGpr.trans af fg
  obtain ⟨h,th,hpc,_,_,_,h10,_,hr,hc⟩ := MainServeNextPackTwo.contract B g r4 sp _ _ _
    ((ag 8 (by decide)).trans h8) stack aligned ((ag 9 (by decide)).trans h9) ((ag 18 (by decide)).trans h18) rfl rfl rfl gpc
  have fh := MainSavedGpr.temps5 hr
  have ah := MainSavedGpr.trans ag fh
  obtain ⟨i,ti,ipc,ir,ic⟩ := MainServeNextReadyBranch.contract B h _ 0#32 0#32 true hpc h10 (Core.get_zero _) (by decide +kernel)
  have fi : MainSavedGpr.Frame h i := fun rr _ => ir rr
  refine ⟨i,((((((ta.trans tb).trans td).trans te).trans tf).trans tg).trans th).trans ti,?_,MainSavedGpr.trans ah fi,((((((ic.trans hc).trans gc).trans fc).trans ec).trans dc).trans bc).trans ac⟩
  simpa only [ite_true] using ipc
end E5R.Thermostat.MainServeNextCore
