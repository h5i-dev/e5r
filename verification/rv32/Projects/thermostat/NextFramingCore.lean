import Projects.thermostat.NextFramingPackOne
import Projects.thermostat.NextFramingPackTwo
import Projects.thermostat.RejectNextCore
set_option autoImplicit false
namespace E5R.Thermostat.NextFramingCore
open E5R E5R.Thermostat RejectNextCore

/-- Real successful Next staging for all three Head framings. High payload
    and padding remain arbitrary actual RAM; both264-byte copies are executed. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (framing : HttpRequestSpec.Framing)
    (hp : c.pc=0x80000a9a#32) (h2 : c.get 2=sp) (h8 : c.get 8=sp+3204#32)
    (h9 : c.get 9=HeadCompletedView.framingTag framing) (h18 : c.get 18=0#32) (h21 : c.get 21=0xffffffff#32) (h22 : c.get 22=1#32)
    (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 755 ⟨c,ram⟩ ⟨d,memory ram sp⟩ ∧ d.pc=0x80000b50#32 ∧
      MainSavedGpr.Frame c d ∧ d.sameCsr c ∧ ViewFrame.Region ram (memory ram sp) sp 3304 := by
  let r0 := front ram sp
  let r1 := firstCopy ram sp
  let r2 := firstPack ram sp
  let r3 := zeroStage ram sp
  let r4 := secondCopy ram sp
  obtain ⟨a,ta,apc,_,_,ar,ac⟩ := RejectNextFront.contract B c ram sp (ramRead ram (sp+5168#32) .w) (extend .h true (ramRead ram (sp+5172#32) .h)) h8 h22 rfl rfl stack aligned hp
  have fa := MainSavedGpr.temps2 ar
  have a2 : a.get 2=sp := (fa 2 (by decide)).trans h2
  obtain ⟨b,tb,bpc,b2,bs,bc⟩ := MainServeNextCopyOne.contract B a r0 sp apc a2 stack aligned
  have fb := MainSavedGpr.returned bs (b2.trans a2.symm)
  have ab := MainSavedGpr.trans fa fb
  obtain ⟨d,td,dpc,_,_,_,d13,dr,dc⟩ := NextFramingPackOne.contract B b r1 sp _ _ _ framing
    ((ab 8 (by decide)).trans h8) stack aligned ((ab 9 (by decide)).trans h9) ((ab 18 (by decide)).trans h18) rfl rfl rfl bpc
  have fd := MainSavedGpr.temps4 dr
  have ad := MainSavedGpr.trans ab fd
  obtain ⟨e,te,epc,er,ec⟩ := MainServeNextValidBranch.contract B d r2 0#32 0xffffffff#32 true dpc d13 ((ad 21 (by decide)).trans h21) (by decide +kernel)
  have epc' : e.pc=0x80000aee#32 := by simpa only [ite_true] using epc
  have fe : MainSavedGpr.Frame d e := fun rr _ => er rr
  have ae := MainSavedGpr.trans ad fe
  obtain ⟨f,tf,fpc,_,_,fr,fc⟩ := RejectNextZeroStage.contract B e r2 sp (ramRead r2 (sp+4232#32) .w) (extend .h true (ramRead r2 (sp+4236#32) .h)) ((ae 8 (by decide)).trans h8) stack aligned rfl rfl epc'
  have ff := MainSavedGpr.temps2 fr
  have af := MainSavedGpr.trans ae ff
  have f2 : f.get 2=sp := (af 2 (by decide)).trans h2
  obtain ⟨g,tg,gpc,g2,gs,gc⟩ := MainServeNextCopyTwo.contract B f r3 sp fpc f2 stack aligned
  have fg := MainSavedGpr.returned gs (g2.trans f2.symm)
  have ag := MainSavedGpr.trans af fg
  obtain ⟨h,th,hpc,_,_,_,h10,_,hr,hc⟩ := NextFramingPackTwo.contract B g r4 sp _ _ _ framing
    ((ag 8 (by decide)).trans h8) stack aligned ((ag 9 (by decide)).trans h9) ((ag 18 (by decide)).trans h18) rfl rfl rfl gpc
  have fh := MainSavedGpr.temps5 hr
  have ah := MainSavedGpr.trans ag fh
  obtain ⟨i,ti,ipc,ir,ic⟩ := MainServeNextReadyBranch.contract B h _ 0#32 0#32 true hpc h10 (Core.get_zero _) (by decide +kernel)
  have fi : MainSavedGpr.Frame h i := fun rr _ => ir rr
  have ipc' : i.pc=0x80000b50#32 := by simpa only [ite_true] using ipc
  refine ⟨i,(((((((ta.trans tb).trans td).trans te).trans tf).trans tg).trans th).trans ti),ipc',
    MainSavedGpr.trans ah fi,((((((ic.trans hc).trans gc).trans fc).trans ec).trans dc).trans bc).trans ac,?_⟩
  simpa only [BitVec.add_zero] using caller_frame ram sp
end E5R.Thermostat.NextFramingCore
