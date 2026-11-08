import Projects.thermostat.CharFinish
import Projects.thermostat.CharSave
import Projects.thermostat.CursorExit
import Projects.thermostat.ViewFrame
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.CharExit
open E5R E5R.Thermostat

theorem contract (B : Board) (original c : Core) (before ram : Word → BitVec 8) (sp : Word) (remaining : Nat)
    (hp : c.pc = 0x800023b8#32) (hsp : c.get 2 = sp) (horig : original.get 2 = sp+32#32)
    (h18 : c.get 18 = BitVec.ofNat 32 remaining) (h8 : c.get 8 = 1#32)
    (hr : remaining < 2^32) (hm : Memory.Block B sp 32) (ha : sp.toNat%4 = 0)
    (hcsr : c.sameCsr original) (hframe : ViewFrame.Region (CharSave.memory before sp original) ram (sp+12#32) 20)
    (hhigh : HighFrame.Frame original c) :
    ∃ d, DetSteps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧ CursorExit.Returned original d ∧
      d.get 10 = CharFinish.flagWord remaining 1 ∧ HighFrame.Frame original d := by
  obtain ⟨d,td,dpc,dsp,d10,dsaved,dcsr,dhigh⟩ := CharFinish.contract B c ram remaining 1 hp h18 h8 hr (by decide)
    (by simpa only [hsp] using hm) (by simpa only [hsp] using ha)
  have hw (k : Nat) (hk : 12 ≤ k ∧ k+4 ≤ 32) :
      ramRead ram (c.get 2+BitVec.ofNat 32 k) .w = ramRead (CharSave.memory before sp original) (sp+BitVec.ofNat 32 k) .w := by
    rw [hsp]
    have hh := ViewFrame.word hframe (k-12) (by omega)
    have he : (sp+12#32)+BitVec.ofNat 32 (k-12) = sp+BitVec.ofNat 32 k := by
      rw [BitVec.add_assoc,←BitVec.ofNat_add,show 12+(k-12) = k by omega]
    rw [he] at hh;exact hh
  have hs := CharSave.saved before sp original
  refine ⟨d,td,?_,d10,HighFrame.trans hhigh dhigh⟩
  refine ⟨by rw [dpc,hw 28 (by decide),hs.1],by rw [dsp,hsp,←horig],dcsr.trans hcsr,?_,?_,?_,?_,?_⟩
  · exact dsaved.x1 |>.trans ((hw 28 (by decide)).trans hs.1)
  · exact dsaved.x8 |>.trans ((hw 24 (by decide)).trans hs.2.1)
  · exact dsaved.x9 |>.trans ((hw 20 (by decide)).trans hs.2.2.1)
  · exact dsaved.x18 |>.trans ((hw 16 (by decide)).trans hs.2.2.2.1)
  · exact dsaved.x19 |>.trans ((hw 12 (by decide)).trans hs.2.2.2.2)
end E5R.Thermostat.CharExit
