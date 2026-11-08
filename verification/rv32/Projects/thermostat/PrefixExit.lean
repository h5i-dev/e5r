import Projects.thermostat.PrefixRestore
import Projects.thermostat.PrefixSave
import Projects.thermostat.CursorExit
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.PrefixExit
open E5R E5R.Thermostat

theorem contract (B : Board) (original c : Core) (before ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc = 0x80004e4e#32) (hsp : c.get 2 = sp) (horig : original.get 2 = sp+32#32)
    (hm : Memory.Block B sp 32) (ha : sp.toNat%4 = 0) (hcsr : c.sameCsr original)
    (hf : ViewFrame.Region (PrefixSave.memory before sp original) ram sp 32)
    (hu : ∀ r : Reg, 21 ≤ r.val → c.get r = original.get r) :
    ∃ d, DetSteps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧ CursorExit.Returned original d ∧
      d.get 20 = original.get 20 ∧ (∀ r : Reg, 21 ≤ r.val → d.get r = original.get r) ∧ d.get 10 = c.get 10 := by
  obtain ⟨d,td,dpc,dsp,ds,dr,dc⟩ := PrefixRestore.contract B c ram hp
    (by simpa only [hsp] using hm) (by simpa only [hsp] using ha)
  have hw (k : Nat) (hk : k+4 ≤ 32) :
      ramRead ram (c.get 2+BitVec.ofNat 32 k) .w = ramRead (PrefixSave.memory before sp original) (sp+BitVec.ofNat 32 k) .w := by
    rw [hsp];exact ViewFrame.word hf k hk
  have hs := PrefixSave.saved before sp original
  refine ⟨d,td,?_,ds.x20.trans ((hw 8 (by decide)).trans hs.2.2.2.2.2),?_,dr 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  · refine ⟨by rw [dpc,hw 28 (by decide),hs.1],by rw [dsp,hsp,←horig],dc.trans hcsr,?_,?_,?_,?_,?_⟩
    · exact ds.x1.trans ((hw 28 (by decide)).trans hs.1)
    · exact ds.x8.trans ((hw 24 (by decide)).trans hs.2.1)
    · exact ds.x9.trans ((hw 20 (by decide)).trans hs.2.2.1)
    · exact ds.x18.trans ((hw 16 (by decide)).trans hs.2.2.2.1)
    · exact ds.x19.trans ((hw 12 (by decide)).trans hs.2.2.2.2.1)
  · intro r hr
    have hn (k : Reg) (hk : k.val < 21) : r ≠ k := by
      intro he;have hv := congrArg Fin.val he;omega
    exact (dr r (hn 1 (by decide)) (hn 2 (by decide)) (hn 8 (by decide)) (hn 9 (by decide))
      (hn 18 (by decide)) (hn 19 (by decide)) (hn 20 (by decide))).trans (hu r hr)
end E5R.Thermostat.PrefixExit
