import Projects.thermostat.CursorExit
import Projects.thermostat.CursorFinishFull
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.CursorExit
open E5R E5R.Thermostat

theorem contract_full (B : Board) (original c : Core) (before ram : Word → BitVec 8) (sp : Word) (remaining len : Nat)
    (hp : c.pc = 0x800022dc#32) (hsp : c.get 2 = sp) (horig : original.get 2 = sp+32#32)
    (h18 : c.get 18 = BitVec.ofNat 32 remaining) (h8 : c.get 8 = BitVec.ofNat 32 len)
    (hr : remaining < 2^32) (hl : len < 2^32) (hm : Memory.Block B sp 32) (ha : sp.toNat%4 = 0)
    (hcsr : c.sameCsr original) (hframe : ViewFrame.Region (CursorSave.memory before sp original) ram sp 32) (hhigh : HighFrame.Frame original c) :
    ∃ d, DetSteps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧ Returned original d ∧ d.get 10 = CursorFinish.flagWord remaining len ∧ HighFrame.Frame original d := by
  obtain ⟨d,td,dpc,dsp,d10,dsaved,dcsr,dhigh⟩ := CursorFinish.contract_full B c ram remaining len hp h18 h8 hr hl
    (by simpa only [hsp] using hm) (by simpa only [hsp] using ha)
  have hw (k : Nat) (hk : k+4 ≤ 32) :
      ramRead ram (c.get 2+BitVec.ofNat 32 k) .w = ramRead (CursorSave.memory before sp original) (sp+BitVec.ofNat 32 k) .w := by
    rw [hsp];exact ViewFrame.word hframe k hk
  have hs := CursorSave.saved before sp original
  refine ⟨d,td,?_,d10,HighFrame.trans hhigh dhigh⟩
  refine ⟨by rw [dpc,hw 28 (by decide),hs.1],by rw [dsp,hsp,←horig],dcsr.trans hcsr,?_,?_,?_,?_,?_⟩
  · exact dsaved.x1 |>.trans ((hw 28 (by decide)).trans hs.1)
  · exact dsaved.x8 |>.trans ((hw 24 (by decide)).trans hs.2.1)
  · exact dsaved.x9 |>.trans ((hw 20 (by decide)).trans hs.2.2.1)
  · exact dsaved.x18 |>.trans ((hw 16 (by decide)).trans hs.2.2.2.1)
  · exact dsaved.x19 |>.trans ((hw 12 (by decide)).trans hs.2.2.2.2)end E5R.Thermostat.CursorExit
