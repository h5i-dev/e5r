import Projects.thermostat.FormatEngineSave
import Projects.thermostat.FormatEngineSetup
import Projects.thermostat.FormatEngineReady
import Projects.thermostat.WordRegions
namespace E5R.Thermostat.FormatEngineEnter
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp obj args desc : Word) (first : BitVec 8)
    (hp : c.pc = 0x80004976#32) (hs : c.get 2 = sp+64#32)
    (h10 : c.get 10 = obj) (h11 : c.get 11 = 0x80005c04#32) (h13 : c.get 13 = args) (h12 : c.get 12 = desc)
    (hm : Memory.Block B sp 64) (ha : sp.toNat%4 = 0) (hargs : args &&& 1#32 = 0#32)
    (hfirst : ReadBytes.Byte B img ram desc first) (hn : first.toNat ≠ 0)
    (hsep : WordRegions.Disjoint desc 1 sp 64) (hrom : B.inRam 0x80005c10#32 4 = false) :
    ∃ d, DetSteps B img 28 ⟨c,ram⟩ ⟨d,FormatEngineSave.memory ram sp c⟩ ∧
      FormatEngineReady.Ready d sp obj args desc 0 first ∧ d.sameCsr c ∧ d.get 27 = c.get 27 := by
  let rr := FormatEngineSave.memory ram sp c
  have hb : ReadBytes.Byte B img rr desc first := hfirst.frame (FormatEngineSave.frame ram sp c desc (by
    intro i
    simpa only [BitVec.add_zero] using hsep ⟨0,by decide⟩ i))
  obtain ⟨a,ta,apc,asp,ar,ac⟩ := FormatEngineSave.contract B c ram sp hp hs hm ha
  obtain ⟨d,td,dpc,d8,d9,d18,d11,d19,d21,d24,d22,d23,d10,d25,d26,dr,dc⟩ := FormatEngineSetup.contract B a rr sp obj args desc first asp
    ((ar 10 (by decide)).trans h10) ((ar 11 (by decide)).trans h11) ((ar 13 (by decide)).trans h13)
    ((ar 12 (by decide)).trans h12) hargs hb hn hrom apc
  refine ⟨d,ta.trans td,?_,dc.trans ac,?_⟩
  · refine ⟨dpc,?_,d9,?_,d18,d19,d21,d22,d23,d24,d25,d26⟩
    · exact (dr 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans asp
    · exact (dr 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((ar 12 (by decide)).trans h12)
  · exact (dr 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (ar 27 (by decide))
end E5R.Thermostat.FormatEngineEnter
