-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.AuthCompare
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.AuthLoopQuiet
import Projects.thermostat.AuthStopQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.AuthCompare
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp p q : Word)
    (xs ys : List (BitVec 8)) (hl : xs.length = ys.length) (hne : xs ≠ [])
    (hx : ReadBytes.Span B img ram p xs) (hy : ReadBytes.Span B img ram q ys)
    (hp : c.pc = 0x80000582#32) (hsp : c.get 2 = sp) (hm : Memory.Block B sp 25)
    (h10 : c.get 10 = 0#32) (h11 : c.get 11 = q) (h12 : c.get 12 = p)
    (h13 : c.get 13 = q+BitVec.ofNat 32 xs.length) :
    ∃ d, Quiet.Steps B img (7*xs.length+4) ⟨c,ram⟩
      ⟨d,ramPut ram (sp+24#32) (AuthSpec.diff xs ys 0#8)⟩ ∧
      d.pc = (if xs = ys then 0x800005e2#32 else 0x800005a2#32) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 14 → r ≠ 15 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,ta,apc,a10,a11,a12,aframe,acsr⟩ := E5R.Thermostat.AuthLoop.contract_quiet B ram xs ys hl hne p q hx hy c 0#8 hp h10 h11 h12 h13
  have asp : a.get 2 = sp := (aframe 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsp
  obtain ⟨d,td,dpc,d10,dframe,dcsr⟩ := E5R.Thermostat.AuthStop.contract_quiet B a ram sp (AuthSpec.diff xs ys 0#8) apc asp a10 hm
  have he : AuthSpec.diff xs ys 0#8 = 0#8 ↔ xs = ys := by
    simpa only [true_and] using AuthSpec.diff_zero xs ys 0#8 hl
  refine ⟨d,ta.trans td,?_,?_,dcsr.trans acsr⟩
  · simpa only [he] using dpc
  · intro r h1 h2 h3 h4 h5;exact (dframe r h1).trans (aframe r h1 h2 h3 h4 h5)

end E5R.Thermostat.AuthCompare
