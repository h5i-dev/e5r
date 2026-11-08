-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.I16Exit
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.I16RestoreQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.I16Exit
theorem contract_quiet (B : Board) (original a z : Core) (before ram : Word → BitVec 8) (sp fmt : Word) (v : BitVec 16) (off len : Nat)
    (ha : I16Ready.Ready original a sp fmt v off len) (hz : FormatCursor.Returned a z)
    (hsp : original.get 2 = sp+16#32) (hm : Memory.Block B sp 16) (hal : sp.toNat%4 = 0)
    (hf : ViewFrame.Region (I16Save.memory before sp original) ram (sp+8#32) 8) :
    ∃ d, Quiet.Steps B img 4 ⟨z,ram⟩ ⟨d,ram⟩ ∧ FormatCursor.Returned original d ∧ d.get 10 = z.get 10 := by
  have zpc : z.pc = 0x80004f88#32 := by rw [hz.pc,ha.x1];decide +kernel
  have zsp : z.get 2 = sp := hz.sp.trans ha.spReg
  obtain ⟨d,td,dpc,dsp,d1,d8,dr,dc⟩ := E5R.Thermostat.I16Restore.contract_quiet B z ram zpc
    (by simpa only [zsp] using hm) (by simpa only [zsp] using hal)
  have hs := I16Save.saved before sp original
  have hw12 : ramRead ram (z.get 2+12#32) .w = original.get 1 := by
    have hh := ViewFrame.word hf 4 (by decide)
    rw [BitVec.add_assoc,show 8#32+BitVec.ofNat 32 4 = 12#32 by decide +kernel] at hh
    rw [zsp];exact hh.trans hs.1
  have hw8 : ramRead ram (z.get 2+8#32) .w = original.get 8 := by
    have hh := ViewFrame.word hf 0 (by decide)
    simp only [BitVec.add_zero] at hh
    rw [zsp];exact hh.trans hs.2
  refine ⟨d,td,?_,dr 10 (by decide) (by decide) (by decide)⟩
  refine ⟨by rw [dpc,hw12],by rw [dsp,zsp,←hsp],(dc.trans hz.csr).trans ha.csr,
    d1.trans hw12,d8.trans hw8,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (dr 9 (by decide) (by decide) (by decide)).trans (hz.x9.trans (ha.saved 9 (Or.inl rfl)))
  · exact (dr 18 (by decide) (by decide) (by decide)).trans (hz.x18.trans (ha.saved 18 (Or.inr (by decide))))
  · exact (dr 19 (by decide) (by decide) (by decide)).trans (hz.x19.trans (ha.saved 19 (Or.inr (by decide))))
  · exact (dr 20 (by decide) (by decide) (by decide)).trans (hz.x20.trans (ha.saved 20 (Or.inr (by decide))))
  · exact (dr 21 (by decide) (by decide) (by decide)).trans (hz.x21.trans (ha.saved 21 (Or.inr (by decide))))
  · exact (dr 22 (by decide) (by decide) (by decide)).trans (hz.x22.trans (ha.saved 22 (Or.inr (by decide))))
  · exact (dr 23 (by decide) (by decide) (by decide)).trans (hz.x23.trans (ha.saved 23 (Or.inr (by decide))))
  · exact (dr 24 (by decide) (by decide) (by decide)).trans (hz.x24.trans (ha.saved 24 (Or.inr (by decide))))
  · exact (dr 25 (by decide) (by decide) (by decide)).trans (hz.x25.trans (ha.saved 25 (Or.inr (by decide))))
  · exact (dr 26 (by decide) (by decide) (by decide)).trans (hz.x26.trans (ha.saved 26 (Or.inr (by decide))))
  · exact (dr 27 (by decide) (by decide) (by decide)).trans (hz.x27.trans (ha.saved 27 (Or.inr (by decide))))

end E5R.Thermostat.I16Exit
