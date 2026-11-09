import Projects.thermostat.RejectNextFront
import Projects.thermostat.RejectNextZeroStage
import Projects.thermostat.RejectNextPackOne
import Projects.thermostat.RejectNextPackTwo
import Projects.thermostat.RejectNextFrames
import Projects.thermostat.MainServeNextCore
set_option autoImplicit false
namespace E5R.Thermostat.RejectNextCore
open E5R E5R.Thermostat

def front (ram : Word → BitVec 8) (sp : Word) := RejectNextFront.memory ram sp
  (ramRead ram (sp+5168#32) .w) (extend .h true (ramRead ram (sp+5172#32) .h))
def firstCopy (ram : Word → BitVec 8) (sp : Word) := MainServeNextCopyOne.memory (front ram sp) sp
def firstPack (ram : Word → BitVec 8) (sp : Word) := RejectNextPackOne.memory (firstCopy ram sp) sp
  (ramRead (firstCopy ram sp) (sp+4896#32) .w) (extend .h true (ramRead (firstCopy ram sp) (sp+4900#32) .h))
  (extend .b false (ramRead (firstCopy ram sp) (sp+4902#32) .b))
def zeroStage (ram : Word → BitVec 8) (sp : Word) := RejectNextZeroStage.memory (firstPack ram sp) sp
  (ramRead (firstPack ram sp) (sp+4232#32) .w) (extend .h true (ramRead (firstPack ram sp) (sp+4236#32) .h))
def secondCopy (ram : Word → BitVec 8) (sp : Word) := MainServeNextCopyTwo.memory (zeroStage ram sp) sp
def memory (ram : Word → BitVec 8) (sp : Word) := RejectNextPackTwo.memory (secondCopy ram sp) sp
  (ramRead (secondCopy ram sp) (sp+3960#32) .w) (extend .h true (ramRead (secondCopy ram sp) (sp+3964#32) .h))
  (extend .b false (ramRead (secondCopy ram sp) (sp+3966#32) .b))

/-- All actual staging stores/copies lie above recurrence metadata. -/
theorem caller_frame (ram : Word → BitVec 8) (sp : Word) :
    ViewFrame.Region ram (memory ram sp) (sp+0#32) 3304 := by
  apply HeadRegionFrame.trans (RejectNextFrames.front ram sp _ _ 0 3304 (by decide) (Or.inl (by decide)) (Or.inl (by decide)))
  apply HeadRegionFrame.trans (MainRamCopy264.frame (front ram sp) sp 1226 992 0 3304 (by decide) (by decide) (Or.inl (by decide)))
  apply HeadRegionFrame.trans (MainServeNextStoreFrames.packOne (firstCopy ram sp) sp _ _ _ 0 3304 (by decide) (Or.inl (by decide)))
  apply HeadRegionFrame.trans (RejectNextFrames.zeroStage (firstPack ram sp) sp _ _ 0 3304 (by decide) (Or.inl (by decide)))
  apply HeadRegionFrame.trans (MainRamCopy264.frame (zeroStage ram sp) sp 992 1062 0 3304 (by decide) (by decide) (Or.inl (by decide)))
  exact MainServeNextStoreFrames.packTwo (secondCopy ram sp) sp _ _ _ 0 3304 (by decide) (Or.inl (by decide))

/-- Real rejected Next tag3 staging. Padding/high payload words are arbitrary
    actual RAM values, with both original264-byte copies and the error branch. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc=0x80000a9a#32) (h2 : c.get 2=sp) (h8 : c.get 8=sp+3204#32)
    (h9 : c.get 9=3#32) (h18 : c.get 18=0#32) (h21 : c.get 21=0xffffffff#32) (h22 : c.get 22=1#32)
    (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 756 ⟨c,ram⟩ ⟨d,memory ram sp⟩ ∧ d.pc=0x80001bbc#32 ∧ d.get 10=1#32 ∧
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
  obtain ⟨d,td,dpc,_,_,_,d13,dr,dc⟩ := RejectNextPackOne.contract B b r1 sp _ _ _
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
  obtain ⟨h,th,hpc,_,_,_,h10,_,hr,hc⟩ := RejectNextPackTwo.contract B g r4 sp _ _ _
    ((ag 8 (by decide)).trans h8) stack aligned ((ag 9 (by decide)).trans h9) ((ag 18 (by decide)).trans h18) rfl rfl rfl gpc
  have fh := MainSavedGpr.temps5 hr
  have ah := MainSavedGpr.trans ag fh
  obtain ⟨i,ti,ipc,ir,ic⟩ := MainServeNextReadyBranch.contract B h _ 1#32 0#32 false hpc h10 (Core.get_zero _) (by decide +kernel)
  have fi : MainSavedGpr.Frame h i := fun rr _ => ir rr
  have ipc' : i.pc=0x80000b4c#32 := by simpa only [Bool.false_eq_true,ite_false] using ipc
  let d := i.goto 0x80001bbc#32
  have last : Quiet.Step B img ⟨i,memory ram sp⟩ ⟨d,memory ram sp⟩ := by
    refine Quiet.step_of (by rw [ipc'];decide) (by rw [ipc'];exact sn2147486540) fun o => ?_
    change Observed.interp B img o (exec i _ _) _ 0 [] []=_
    rw [exec_jal,ipc',Core.set_zero]
    rw [show 0x80000b4c#32+0x00001070#32=0x80001bbc#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  refine ⟨d,(((((((ta.trans tb).trans td).trans te).trans tf).trans tg).trans th).trans ti).trans (.single last),rfl,(ir 10).trans h10,
    MainSavedGpr.trans ah fi,((((((ic.trans hc).trans gc).trans fc).trans ec).trans dc).trans bc).trans ac,?_⟩
  simpa only [BitVec.add_zero] using caller_frame ram sp
end E5R.Thermostat.RejectNextCore
