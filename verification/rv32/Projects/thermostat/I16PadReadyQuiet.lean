-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.I16PadReady
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.I16PadCallQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.I16PadReady
theorem contract_quiet (B : Board) (original c : Core) (ram : Word → BitVec 8) (sp fmt : Word) (v : BitVec 16) (idx : Nat)
    (hi : idx ≤ 4) (hs : c.get 2 = sp) (h10 : c.get 10 = SignedMagnitude.input v)
    (h13 : c.get 13 = fmt) (h14 : c.get 14 = BitVec.ofNat 32 idx) (hp : c.pc = 0x80004f6a#32)
    (hc : c.sameCsr original) (hf : I16Protected.Frame original c) :
    ∃ d, Quiet.Steps B img 11 ⟨c,ram⟩ ⟨d,ram⟩ ∧ I16Ready.Ready original d sp fmt v (3+idx) (5-idx) := by
  obtain ⟨d,td,dpc,d10,d15,d12,d11,d14,d13,d1,dr,dc⟩ := E5R.Thermostat.I16PadCall.contract_quiet B c ram sp fmt v idx hi hs h10 h13 h14 hp
  refine ⟨d,td,dpc,?_,d1,d10,d11,d12,d13,?_,d15,dc.trans hc,?_⟩
  · exact (dr 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs
  · simpa only [BitVec.add_assoc,BitVec.ofNat_add] using d14
  · intro r hr
    have hn (q : Reg) (hq : q.val < 18) (h9 : q ≠ 9) := I16Protected.ne r q hr hq h9
    exact (dr r (hn 10 (by decide) (by decide)) (hn 15 (by decide) (by decide)) (hn 12 (by decide) (by decide))
      (hn 11 (by decide) (by decide)) (hn 14 (by decide) (by decide)) (hn 13 (by decide) (by decide))
      (hn 1 (by decide) (by decide))).trans (hf r hr)

end E5R.Thermostat.I16PadReady
