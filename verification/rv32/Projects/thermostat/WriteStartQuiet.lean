-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.WriteStart
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.FutureCopyQuiet
import Projects.thermostat.FutureExtractQuiet
import Projects.thermostat.OuterSaveQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.WriteStart
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp f response : Word)
    (hp : c.pc = 0x800004c6#32) (hsp : c.get 2 = sp+96#32)
    (h11 : c.get 11 = f) (h10 : c.get 10 = response)
    (hm : Memory.Block B sp 96) (ha : sp.toNat%4 = 0)
    (hf : Memory.Block B f 41) (hfa : f.toNat%4 = 0) (hs : Separate f sp)
    (hz : ram (f+40#32) = 0#8) :
    ∃ d, Quiet.Steps B img 31 ⟨c,ram⟩ ⟨d,memory ram sp f c⟩ ∧ d.pc = 0x8000052e#32 ∧
      d.get 2 = sp ∧ d.get 8 = f ∧ d.get 9 = response ∧
      d.get 21 = ramRead ram (f+4#32) .w ∧ d.get 23 = ramRead ram (f+8#32) .w ∧
      d.get 19 = ramRead ram (f+12#32) .w ∧ d.get 18 = ramRead ram (f+16#32) .w ∧ d.sameCsr c := by
  let r := OuterSave.memory ram sp c
  obtain ⟨a,ta,apc,asp,aframe,acsr⟩ := E5R.Thermostat.OuterSave.contract_quiet B c ram sp hp hsp hm ha
  have a11 : a.get 11 = f := (aframe 11 (by decide)).trans h11
  have a10 : a.get 10 = response := (aframe 10 (by decide)).trans h10
  have hz' : r (f+40#32) = 0#8 := (future_region ram sp f c hs ⟨40,by decide⟩).trans hz
  obtain ⟨b,tb,bpc,b8,b9,bframe,bcsr⟩ := E5R.Thermostat.FutureExtract.fresh_quiet B a r f response apc a11 a10 hf hz'
  obtain ⟨d,td,dpc,d21,d23,d19,d18,dframe,dcsr⟩ := E5R.Thermostat.FutureCopy.contract_quiet B b r f bpc b8 hf hfa
  have reg2 : d.get 2 = sp := (dframe 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    ((bframe 2 (by decide) (by decide) (by decide)).trans asp)
  have reg8 : d.get 8 = f := (dframe 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b8
  have reg9 : d.get 9 = response := (dframe 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b9
  have hregion := future_region ram sp f c hs
  exact ⟨d,(ta.trans tb).trans td,dpc,reg2,reg8,reg9,
    d21.trans (ViewFrame.word hregion 4 (by decide)),d23.trans (ViewFrame.word hregion 8 (by decide)),
    d19.trans (ViewFrame.word hregion 12 (by decide)),d18.trans (ViewFrame.word hregion 16 (by decide)),(dcsr.trans bcsr).trans acsr⟩

end E5R.Thermostat.WriteStart
