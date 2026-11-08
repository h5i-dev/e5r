-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ErrorExit
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.ErrorReturnQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.ErrorExit
theorem contract_quiet (B : Board) (original a z : Core) (before ram : Word → BitVec 8) (sp dst : Word) (e : Spec.Error)
    (h : ErrorPrepare.Ready original a sp dst e) (hz : FormatCursor.Returned a z)
    (hsp : original.get 2=sp+16#32) (hm : Memory.Block B sp 16) (ha : sp.toNat%4=0)
    (hf : ViewFrame.Region (ErrorSave.memory before sp original) ram (sp+4#32) 12) :
    ∃ d, Quiet.Steps B img 7 ⟨z,ram⟩ ⟨d,ram⟩ ∧ FormatCursor.Returned original d ∧
      d.get 10=ErrorLiterals.status e ∧ d.get 11=BitVec.ofNat 32 (ReplyJson.errorBody e).length := by
  have zpc : z.pc=0x80001e96#32 := by rw [hz.pc,h.ra];decide +kernel
  have zsp : z.get 2=sp := hz.sp.trans h.stack
  have hs := ErrorSave.saved before sp original
  have word12 : ramRead ram (sp+12#32) .w=original.get 1 := by
    have hh := ViewFrame.word hf 8 (by decide)
    rw [BitVec.add_assoc,show 4#32+BitVec.ofNat 32 8=12#32 by decide +kernel] at hh
    exact hh.trans hs.1
  have word8 : ramRead ram (sp+8#32) .w=original.get 8 := by
    have hh := ViewFrame.word hf 4 (by decide)
    rw [BitVec.add_assoc,show 4#32+BitVec.ofNat 32 4=8#32 by decide +kernel] at hh
    exact hh.trans hs.2.1
  have word4 : ramRead ram (sp+4#32) .w=original.get 9 := by
    have hh := ViewFrame.word hf 0 (by decide)
    simp only [BitVec.add_zero] at hh
    exact hh.trans hs.2.2
  obtain ⟨d,td,dpc,dsp,d10,d11,d1,d8,d9,dr,dc⟩ := E5R.Thermostat.ErrorReturn.contract_quiet B z ram sp
    (BitVec.ofNat 32 (ReplyJson.errorBody e).length) (ErrorLiterals.status e) (original.get 1) (original.get 8) (original.get 9)
    zpc zsp (hz.x8.trans h.savedLength) (hz.x9.trans h.savedStatus) hm ha word12 word8 word4
  have keep (r : Reg) (hr : 18≤r.val ∧ r.val≤27) : d.get r=original.get r := by
    have ne (q : Reg) (hq : q.val<18) : r≠q := by intro he;subst r;omega
    exact (dr r (ne 10 (by decide)) (ne 11 (by decide)) (ne 1 (by decide)) (ne 8 (by decide)) (ne 9 (by decide)) (ne 2 (by decide))).trans
      ((Callee.of_returned hz r (Or.inr (Or.inr hr))).trans (h.saved r hr))
  refine ⟨d,td,?_,d10,d11⟩
  exact ⟨dpc,dsp.trans hsp.symm,(dc.trans hz.csr).trans h.csr,d1,d8,d9,
    keep 18 (by decide),keep 19 (by decide),keep 20 (by decide),keep 21 (by decide),keep 22 (by decide),
    keep 23 (by decide),keep 24 (by decide),keep 25 (by decide),keep 26 (by decide),keep 27 (by decide)⟩

end E5R.Thermostat.ErrorExit
