import Projects.thermostat.SliceDisplayEntry
import Projects.thermostat.StringDisplayTail
namespace E5R.Thermostat.SliceDisplay
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (ptr src len fmt : Word)
    (hp : c.pc = 0x8000228c#32) (h10 : c.get 10 = ptr) (h11 : c.get 11 = fmt)
    (hm : Memory.Block B ptr 8) (ha : ptr.toNat%4 = 0)
    (hsrc : ramRead ram ptr .w = src) (hlen : ramRead ram (ptr+4#32) .w = len) :
    ∃ d, DetSteps B img 14 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004790#32 ∧
      d.get 10 = fmt ∧ d.get 11 = src ∧ d.get 12 = len ∧
      (∀ r : Reg, r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 10 → r ≠ 11 → r ≠ 6 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,ta,apc,a12,a13,a14,a10,a11,a6,ar,ac⟩ := SliceDisplayEntry.contract B c ram ptr src len fmt h10 h11 hm ha hsrc hlen hp
  obtain ⟨d,td,dpc,d13,d11,d10,d12,d6,dr,dc⟩ := StringDisplayTail.contract B a ram src len fmt a10 a11 a12 apc
  refine ⟨d,ta.trans td,dpc,d10,d11,d12,?_,dc.trans ac⟩
  intro r h12 h13 h14 h10 h11 h6
  exact (dr r h13 h11 h10 h12 h6).trans (ar r h12 h13 h14 h10 h11 h6)
end E5R.Thermostat.SliceDisplay
