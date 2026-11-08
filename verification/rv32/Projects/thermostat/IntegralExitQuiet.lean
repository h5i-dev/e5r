-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.IntegralExit
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.IntegralRestoreQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.IntegralExit
theorem contract_quiet (B : Board) (original c : Core) (before ram : Word → BitVec 8) (sp writer src len : Word)
    (hp : c.pc = 0x800046a4#32) (hsp : c.get 2 = sp) (horig : original.get 2 = sp+64#32)
    (hm : Memory.Block B sp 64) (ha : sp.toNat%4 = 0) (hcsr : c.sameCsr original)
    (hf : ViewFrame.Region (IntegralSave.memory before sp original) ram sp 64)
    (h6 : c.get 6 = 0x800022a0#32) (h10 : c.get 10 = writer) (h11 : c.get 11 = src) (h12 : c.get 12 = len) :
    ∃ d, Quiet.Steps B img 15 ⟨c,ram⟩ ⟨d,ram⟩ ∧ IntegralReady.Ready original d writer src len := by
  obtain ⟨d,td,dpc,dsp,dc,ds,d10,d11,d12⟩ := E5R.Thermostat.IntegralRestore.contract_quiet B c ram hp
    (by simpa only [hsp] using hm) (by simpa only [hsp] using ha)
  have hw (k : Nat) (hk : k+4 ≤ 64) :
      ramRead ram (c.get 2+BitVec.ofNat 32 k) .w = ramRead (IntegralSave.memory before sp original) (sp+BitVec.ofNat 32 k) .w := by
    rw [hsp];exact ViewFrame.word hf k hk
  have hs := IntegralSave.saved before sp original
  refine ⟨d,td,?_,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_⟩
  · rw [dpc,h6];decide +kernel
  · rw [dsp,hsp,←horig]
  · exact d10.trans h10
  · exact d11.trans h11
  · exact d12.trans h12
  · exact dc.trans hcsr
  · exact ds.x1.trans ((hw 60 (by decide)).trans hs.1)
  · exact ds.x8.trans ((hw 56 (by decide)).trans hs.2.1)
  · exact ds.x9.trans ((hw 52 (by decide)).trans hs.2.2.1)
  · exact ds.x18.trans ((hw 48 (by decide)).trans hs.2.2.2.1)
  · exact ds.x19.trans ((hw 44 (by decide)).trans hs.2.2.2.2.1)
  · exact ds.x20.trans ((hw 40 (by decide)).trans hs.2.2.2.2.2.1)
  · exact ds.x21.trans ((hw 36 (by decide)).trans hs.2.2.2.2.2.2.1)
  · exact ds.x22.trans ((hw 32 (by decide)).trans hs.2.2.2.2.2.2.2.1)
  · exact ds.x23.trans ((hw 28 (by decide)).trans hs.2.2.2.2.2.2.2.2.1)
  · exact ds.x24.trans ((hw 24 (by decide)).trans hs.2.2.2.2.2.2.2.2.2.1)
  · exact ds.x25.trans ((hw 20 (by decide)).trans hs.2.2.2.2.2.2.2.2.2.2.1)
  · exact ds.x26.trans ((hw 16 (by decide)).trans hs.2.2.2.2.2.2.2.2.2.2.2.1)
  · exact ds.x27.trans ((hw 12 (by decide)).trans hs.2.2.2.2.2.2.2.2.2.2.2.2)

end E5R.Thermostat.IntegralExit
