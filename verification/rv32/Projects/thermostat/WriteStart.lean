import Projects.thermostat.OuterSave
import Projects.thermostat.FutureExtract
import Projects.thermostat.FutureCopy
import Projects.thermostat.ViewFrame
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.WriteStart
open E5R E5R.Thermostat

def Separate (f sp : Word) : Prop :=
  ∀ i : Fin 41, ∀ j : Fin 96, f+BitVec.ofNat 32 i.val ≠ sp+BitVec.ofNat 32 j.val

def memory (ram : Word → BitVec 8) (sp f : Word) (c : Core) := FutureCopy.memory (OuterSave.memory ram sp c) f

theorem future_region (ram : Word → BitVec 8) (sp f : Word) (c : Core) (hs : Separate f sp) :
    ViewFrame.Region ram (OuterSave.memory ram sp c) f 41 := by
  intro i;apply OuterSave.frame;exact hs i

theorem saved_region (ram : Word → BitVec 8) (sp f : Word) (c : Core) (hs : Separate f sp) :
    ViewFrame.Region (OuterSave.memory ram sp c) (memory ram sp f c) sp 96 := by
  intro i
  apply FutureCopy.frame
  intro j
  exact Ne.symm (hs ⟨20+j.val,by have := j.isLt;omega⟩ i)

/-- Fresh actual write Future: real stack saves, flag test, argument copy,
    Request/App/output extraction, ending at the actual header-query setup. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp f response : Word)
    (hp : c.pc = 0x800004c6#32) (hsp : c.get 2 = sp+96#32)
    (h11 : c.get 11 = f) (h10 : c.get 10 = response)
    (hm : Memory.Block B sp 96) (ha : sp.toNat%4 = 0)
    (hf : Memory.Block B f 41) (hfa : f.toNat%4 = 0) (hs : Separate f sp)
    (hz : ram (f+40#32) = 0#8) :
    ∃ d, DetSteps B img 31 ⟨c,ram⟩ ⟨d,memory ram sp f c⟩ ∧ d.pc = 0x8000052e#32 ∧
      d.get 2 = sp ∧ d.get 8 = f ∧ d.get 9 = response ∧
      d.get 21 = ramRead ram (f+4#32) .w ∧ d.get 23 = ramRead ram (f+8#32) .w ∧
      d.get 19 = ramRead ram (f+12#32) .w ∧ d.get 18 = ramRead ram (f+16#32) .w ∧ d.sameCsr c := by
  let r := OuterSave.memory ram sp c
  obtain ⟨a,ta,apc,asp,aframe,acsr⟩ := OuterSave.contract B c ram sp hp hsp hm ha
  have a11 : a.get 11 = f := (aframe 11 (by decide)).trans h11
  have a10 : a.get 10 = response := (aframe 10 (by decide)).trans h10
  have hz' : r (f+40#32) = 0#8 := (future_region ram sp f c hs ⟨40,by decide⟩).trans hz
  obtain ⟨b,tb,bpc,b8,b9,bframe,bcsr⟩ := FutureExtract.fresh B a r f response apc a11 a10 hf hz'
  obtain ⟨d,td,dpc,d21,d23,d19,d18,dframe,dcsr⟩ := FutureCopy.contract B b r f bpc b8 hf hfa
  have reg2 : d.get 2 = sp := (dframe 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    ((bframe 2 (by decide) (by decide) (by decide)).trans asp)
  have reg8 : d.get 8 = f := (dframe 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b8
  have reg9 : d.get 9 = response := (dframe 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b9
  have hregion := future_region ram sp f c hs
  exact ⟨d,(ta.trans tb).trans td,dpc,reg2,reg8,reg9,
    d21.trans (ViewFrame.word hregion 4 (by decide)),d23.trans (ViewFrame.word hregion 8 (by decide)),
    d19.trans (ViewFrame.word hregion 12 (by decide)),d18.trans (ViewFrame.word hregion 16 (by decide)),(dcsr.trans bcsr).trans acsr⟩

theorem frame (ram : Word → BitVec 8) (sp f : Word) (c : Core) (x : Word)
    (hsp : ∀ i : Fin 96, x ≠ sp+BitVec.ofNat 32 i.val)
    (hf : ∀ i : Fin 17, x ≠ f+BitVec.ofNat 32 (20+i.val)) : memory ram sp f c x = ram x := by
  rw [memory,FutureCopy.frame _ _ _ hf]
  exact OuterSave.frame ram sp c x hsp
end E5R.Thermostat.WriteStart
