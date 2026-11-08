import Projects.thermostat.MainRequestCounterMemory
import Projects.thermostat.MainRequestCapacityBranch
import Projects.thermostat.MainRequestTargetLoad
import Projects.thermostat.MainRequestTargetOrderBranch
import Projects.thermostat.MainRequestTargetUsedBranch
import Projects.thermostat.MainRequestTargetSetup
import Projects.thermostat.MainRequestTargetNonemptyBranch
namespace E5R.Thermostat.MainRequestTargetCore
open E5R E5R.Thermostat

/-- Actual served increment, raw-used store and all target slice guards,
    through the nonempty URI scanning entry. Guards remain explicit here. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp count used start finish rx : Word)
    (hp : c.pc=0x80000b50#32) (h2 : c.get 2=sp) (h8 : c.get 8=sp+3204#32) (h18 : c.get 18=0#32) (h24 : c.get 24=used)
    (hcount : ramRead ram (sp+3292#32) .w=count) (hcapacity : ramRead ram (sp+3264#32) .w=2048#32)
    (hstart : ramRead ram (sp+36#32) .w=start) (hfinish : ramRead ram (sp+32#32) .w=finish) (hrx : ramRead ram (sp+3260#32) .w=rx)
    (capacity : taken .geu 2048#32 used=true) (order : taken .geu finish start=true)
    (inside : taken .geu used finish=true) (nonempty : taken .ne finish start=true)
    (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 17 ⟨c,ram⟩ ⟨d,MainRequestCounter.memory ram sp count used⟩ ∧ d.pc=0x80000bd0#32 ∧
      d.get 31=0#32 ∧ d.get 18=count+1#32 ∧ d.get 12=2048#32 ∧ d.get 15=63#32 ∧
      d.get 29=start ∧ d.get 30=finish ∧ d.get 5=6#32 ∧ d.get 17=5#32 ∧ d.get 21=rx ∧ d.get 10=rx+start ∧
      (∀ rr : Reg, rr≠31 → rr≠18 → rr≠12 → rr≠15 → rr≠29 → rr≠30 → rr≠5 → rr≠17 → rr≠21 → rr≠10 → d.get rr=c.get rr) ∧ d.sameCsr c := by
  let after := MainRequestCounter.memory ram sp count used
  obtain ⟨a,ta,apc,a31,a18,a12,a15,ar,ac⟩ := MainRequestCounter.contract B c ram sp count used h8 h18 h24 hcount hcapacity stack aligned hp
  obtain ⟨b,tb,bpc,br,bc⟩ := MainRequestCapacityBranch.contract B a after 2048#32 used true apc a12 ((ar 24 (by decide) (by decide) (by decide) (by decide)).trans h24) capacity
  have bpc' : b.pc=0x80000b6e#32 := by simpa only [ite_true] using bpc
  have bOrig (rr : Reg) (h31 : rr≠31) (h18 : rr≠18) (h12 : rr≠12) (h15 : rr≠15) : b.get rr=c.get rr := (br rr).trans (ar rr h31 h18 h12 h15)
  have b2 : b.get 2=sp := (bOrig 2 (by decide) (by decide) (by decide) (by decide)).trans h2
  have word (off : Nat) (bound : off+4≤3292) : ramRead after (sp+BitVec.ofNat 32 off) .w=ramRead ram (sp+BitVec.ofNat 32 off) .w := by
    have slot := ViewFrame.word (MainRequestCounterMemory.frame ram sp count used off 4 (by omega) (Or.inl bound)) 0 (by decide)
    simpa only [BitVec.add_zero] using slot
  obtain ⟨z,tz,zpc,z29,z30,zr,zc⟩ := MainRequestTargetLoad.contract B b after sp start finish b2 ((word 36 (by decide)).trans hstart) ((word 32 (by decide)).trans hfinish) stack aligned bpc'
  obtain ⟨d,td,dpc,dr,dc⟩ := MainRequestTargetOrderBranch.contract B z after finish start true zpc z30 z29 order
  have dpc' : d.pc=0x80000b7a#32 := by simpa only [ite_true] using dpc
  have d24 : d.get 24=used := (dr 24).trans ((zr 24 (by decide) (by decide)).trans ((bOrig 24 (by decide) (by decide) (by decide) (by decide)).trans h24))
  obtain ⟨e,te,epc,er,ec⟩ := MainRequestTargetUsedBranch.contract B d after used finish true dpc' d24 ((dr 30).trans z30) inside
  have epc' : e.pc=0x80000b82#32 := by simpa only [ite_true] using epc
  have e8 : e.get 8=sp+3204#32 := (er 8).trans ((dr 8).trans ((zr 8 (by decide) (by decide)).trans ((bOrig 8 (by decide) (by decide) (by decide) (by decide)).trans h8)))
  have e29 : e.get 29=start := (er 29).trans ((dr 29).trans z29)
  have e30 : e.get 30=finish := (er 30).trans ((dr 30).trans z30)
  obtain ⟨f,tf,fpc,f5,f17,f21,f10,fr,fc⟩ := MainRequestTargetSetup.contract B e after sp rx start e8 e29 ((word 3260 (by decide)).trans hrx) stack aligned epc'
  have f29 : f.get 29=start := (fr 29 (by decide) (by decide) (by decide) (by decide)).trans e29
  have f30 : f.get 30=finish := (fr 30 (by decide) (by decide) (by decide) (by decide)).trans e30
  obtain ⟨g,tg,gpc,gr,gc⟩ := MainRequestTargetNonemptyBranch.contract B f after finish start true fpc f30 f29 nonempty
  have fromA (rr : Reg) (h29 : rr≠29) (h30 : rr≠30) (h5 : rr≠5) (h17 : rr≠17) (h21 : rr≠21) (h10 : rr≠10) : g.get rr=a.get rr :=
    (gr rr).trans ((fr rr h5 h17 h21 h10).trans ((er rr).trans ((dr rr).trans ((zr rr h29 h30).trans (br rr)))))
  refine ⟨g,(((((ta.trans tb).trans tz).trans td).trans te).trans tf).trans tg,?_,
    (fromA 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a31,
    (fromA 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a18,
    (fromA 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a12,
    (fromA 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a15,
    (gr 29).trans f29,(gr 30).trans f30,(gr 5).trans f5,(gr 17).trans f17,(gr 21).trans f21,(gr 10).trans f10,?_,
    (((((gc.trans fc).trans ec).trans dc).trans zc).trans bc).trans ac⟩
  · simpa only [ite_true] using gpc
  · intro rr h31 h18 h12 h15 h29 h30 h5 h17 h21 h10
    exact (fromA rr h29 h30 h5 h17 h21 h10).trans (ar rr h31 h18 h12 h15)
end E5R.Thermostat.MainRequestTargetCore
