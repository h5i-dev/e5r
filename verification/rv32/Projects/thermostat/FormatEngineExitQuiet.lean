-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.FormatEngineExit
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.FormatEngineRestoreQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.FormatEngineExit
theorem contract_quiet (B : Board) (original z : Core) (before ram : Word → BitVec 8) (sp : Word)
    (hp : z.pc = 0x80004b18#32) (hsp : z.get 2 = sp) (hosp : original.get 2 = sp+64#32)
    (hm : Memory.Block B sp 64) (ha : sp.toNat%4 = 0)
    (hc : z.sameCsr original) (h27 : z.get 27 = original.get 27)
    (hf : ViewFrame.Region (FormatEngineSave.memory before sp original) ram (sp+16#32) 48) :
    ∃ d, Quiet.Steps B img 14 ⟨z,ram⟩ ⟨d,ram⟩ ∧ FormatCursor.Returned original d ∧ d.get 10 = z.get 10 := by
  obtain ⟨d,td,dpc,dsp,hd,dr,dc⟩ := E5R.Thermostat.FormatEngineRestore.contract_quiet B z ram hp
    (by simpa only [hsp] using hm) (by simpa only [hsp] using ha)
  have hs := FormatEngineSave.saved before sp original
  have hw1 : ramRead ram (z.get 2+60#32) .w = original.get 1 := by
    have hh := ViewFrame.word hf 44 (by decide)
    rw [BitVec.add_assoc,show 16#32+BitVec.ofNat 32 44 = 60#32 by decide +kernel] at hh
    rw [hsp];exact hh.trans hs.1
  have hw8 : ramRead ram (z.get 2+56#32) .w = original.get 8 := by
    have hh := ViewFrame.word hf 40 (by decide)
    rw [BitVec.add_assoc,show 16#32+BitVec.ofNat 32 40 = 56#32 by decide +kernel] at hh
    rw [hsp];exact hh.trans hs.2.1
  have hw9 : ramRead ram (z.get 2+52#32) .w = original.get 9 := by
    have hh := ViewFrame.word hf 36 (by decide)
    rw [BitVec.add_assoc,show 16#32+BitVec.ofNat 32 36 = 52#32 by decide +kernel] at hh
    rw [hsp];exact hh.trans hs.2.2.1
  have hw18 : ramRead ram (z.get 2+48#32) .w = original.get 18 := by
    have hh := ViewFrame.word hf 32 (by decide)
    rw [BitVec.add_assoc,show 16#32+BitVec.ofNat 32 32 = 48#32 by decide +kernel] at hh
    rw [hsp];exact hh.trans hs.2.2.2.1
  have hw19 : ramRead ram (z.get 2+44#32) .w = original.get 19 := by
    have hh := ViewFrame.word hf 28 (by decide)
    rw [BitVec.add_assoc,show 16#32+BitVec.ofNat 32 28 = 44#32 by decide +kernel] at hh
    rw [hsp];exact hh.trans hs.2.2.2.2.1
  have hw20 : ramRead ram (z.get 2+40#32) .w = original.get 20 := by
    have hh := ViewFrame.word hf 24 (by decide)
    rw [BitVec.add_assoc,show 16#32+BitVec.ofNat 32 24 = 40#32 by decide +kernel] at hh
    rw [hsp];exact hh.trans hs.2.2.2.2.2.1
  have hw21 : ramRead ram (z.get 2+36#32) .w = original.get 21 := by
    have hh := ViewFrame.word hf 20 (by decide)
    rw [BitVec.add_assoc,show 16#32+BitVec.ofNat 32 20 = 36#32 by decide +kernel] at hh
    rw [hsp];exact hh.trans hs.2.2.2.2.2.2.1
  have hw22 : ramRead ram (z.get 2+32#32) .w = original.get 22 := by
    have hh := ViewFrame.word hf 16 (by decide)
    rw [BitVec.add_assoc,show 16#32+BitVec.ofNat 32 16 = 32#32 by decide +kernel] at hh
    rw [hsp];exact hh.trans hs.2.2.2.2.2.2.2.1
  have hw23 : ramRead ram (z.get 2+28#32) .w = original.get 23 := by
    have hh := ViewFrame.word hf 12 (by decide)
    rw [BitVec.add_assoc,show 16#32+BitVec.ofNat 32 12 = 28#32 by decide +kernel] at hh
    rw [hsp];exact hh.trans hs.2.2.2.2.2.2.2.2.1
  have hw24 : ramRead ram (z.get 2+24#32) .w = original.get 24 := by
    have hh := ViewFrame.word hf 8 (by decide)
    rw [BitVec.add_assoc,show 16#32+BitVec.ofNat 32 8 = 24#32 by decide +kernel] at hh
    rw [hsp];exact hh.trans hs.2.2.2.2.2.2.2.2.2.1
  have hw25 : ramRead ram (z.get 2+20#32) .w = original.get 25 := by
    have hh := ViewFrame.word hf 4 (by decide)
    rw [BitVec.add_assoc,show 16#32+BitVec.ofNat 32 4 = 20#32 by decide +kernel] at hh
    rw [hsp];exact hh.trans hs.2.2.2.2.2.2.2.2.2.2.1
  have hw26 : ramRead ram (z.get 2+16#32) .w = original.get 26 := by
    have hh := ViewFrame.word hf 0 (by decide)
    rw [BitVec.add_assoc,show 16#32+BitVec.ofNat 32 0 = 16#32 by decide +kernel] at hh
    rw [hsp];exact hh.trans hs.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨d,td,?_,dr 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  refine ⟨by rw [dpc,hw1],by rw [dsp,hsp,←hosp],dc.trans hc,
    hd.x1.trans hw1,hd.x8.trans hw8,hd.x9.trans hw9,hd.x18.trans hw18,hd.x19.trans hw19,hd.x20.trans hw20,hd.x21.trans hw21,hd.x22.trans hw22,hd.x23.trans hw23,hd.x24.trans hw24,hd.x25.trans hw25,hd.x26.trans hw26,?_⟩
  exact (dr 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h27

end E5R.Thermostat.FormatEngineExit
