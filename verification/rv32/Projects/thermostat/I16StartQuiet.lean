-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.I16Start
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.I16MagnitudeQuiet
import Projects.thermostat.I16SaveQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.I16Start
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp ptr fmt : Word) (v : BitVec 16)
    (hp : c.pc = 0x80004e5e#32) (hsp : c.get 2 = sp+16#32)
    (h10 : c.get 10 = ptr) (h11 : c.get 11 = fmt)
    (hst : Memory.Block B sp 16) (hsa : sp.toNat%4 = 0)
    (hm : Memory.Block B ptr 2) (ha : ptr.toNat%2 = 0)
    (hv : extend .h true (ramRead ram ptr .h) = SignedMagnitude.input v)
    (hsep : WordRegions.Disjoint ptr 2 sp 16) :
    ∃ d, Quiet.Steps B img 14 ⟨c,ram⟩ ⟨d,I16Save.memory ram sp c⟩ ∧ Ready c d sp fmt v := by
  let r0 := I16Save.memory ram sp c
  have ho : ViewFrame.Region ram r0 ptr 2 := fun i => I16Save.frame ram sp c _ (hsep i)
  have hv0 : extend .h true (ramRead r0 ptr .h) = SignedMagnitude.input v := by
    have hh := ViewFrame.half ho 0 (by decide)
    simp only [BitVec.add_zero] at hh
    rw [hh];exact hv
  obtain ⟨a,ta,apc,asp,ar,ac⟩ := E5R.Thermostat.I16Save.contract_quiet B c ram sp hp hsp hst hsa
  obtain ⟨b,tb,bpc,b8,b13,b10,b15,b11,b12,b14,b16,br,bc⟩ := E5R.Thermostat.I16Magnitude.contract_quiet B a r0 sp ptr fmt v asp
    ((ar 10 (by decide)).trans h10) ((ar 11 (by decide)).trans h11) hm ha hv0 apc
  refine ⟨b,ta.trans tb,bpc,?_,b10,b11,b12,b13,b14,b16,bc.trans ac,?_⟩
  · exact (br 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans asp
  · intro reg hr
    have hn (q : Reg) (hq : q.val < 18) (h9 : q ≠ 9) := I16Protected.ne reg q hr hq h9
    exact (br reg (hn 8 (by decide) (by decide)) (hn 13 (by decide) (by decide)) (hn 10 (by decide) (by decide))
      (hn 15 (by decide) (by decide)) (hn 11 (by decide) (by decide)) (hn 12 (by decide) (by decide))
      (hn 14 (by decide) (by decide)) (hn 16 (by decide) (by decide))).trans (ar reg (hn 2 (by decide) (by decide)))

end E5R.Thermostat.I16Start
