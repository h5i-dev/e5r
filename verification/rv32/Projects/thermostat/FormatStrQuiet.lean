-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.FormatStr
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.FormatStrDispatchQuiet
import Projects.thermostat.FormatStrGuardQuiet
import Projects.thermostat.FormatStrRestoreQuiet
import Projects.thermostat.FormatStrSaveQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.FormatStr
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp fmt writer flags : Word)
    (hp : c.pc = 0x80004790#32) (hsp : c.get 2 = sp+64#32) (h10 : c.get 10 = fmt)
    (hst : Memory.Block B sp 64) (hsa : sp.toNat%4 = 0)
    (hm : Memory.Block B fmt 12) (ha : fmt.toNat%4 = 0)
    (hw : ramRead ram fmt .w = writer) (hv : ramRead ram (fmt+4#32) .w = 0x80005c04#32)
    (hf : ramRead ram (fmt+8#32) .w = flags) (hmask : flags &&& 0x18000000#32 = 0#32)
    (hsep : WordRegions.Disjoint fmt 12 sp 64) (hrom : B.inRam 0x80005c10#32 4 = false) :
    ∃ d, Quiet.Steps B img 37 ⟨c,ram⟩ ⟨d,FormatStrSave.memory ram sp c⟩ ∧ Ready c d writer := by
  let r := FormatStrSave.memory ram sp c
  have ho : ViewFrame.Region ram r fmt 12 := fun i => FormatStrSave.frame ram sp c _ (hsep i)
  have hw' : ramRead r fmt .w = writer := by
    have hh := ViewFrame.word ho 0 (by decide)
    simp only [BitVec.add_zero] at hh
    exact hh.trans hw
  obtain ⟨a,ta,apc,asp,aframe,acsr⟩ := E5R.Thermostat.FormatStrSave.contract_quiet B c ram sp hp hsp hst hsa
  have a10 : a.get 10 = fmt := (aframe 10 (by decide)).trans h10
  obtain ⟨b,tb,bpc,bframe,bcsr⟩ := E5R.Thermostat.FormatStrGuard.contract_quiet B a r sp fmt flags apc asp a10 hm ha
    ((ViewFrame.word ho 8 (by decide)).trans hf) hmask
  have b10 : b.get 10 = fmt := (bframe 10 (by decide) (by decide) (by decide)).trans a10
  have bsp : b.get 2 = sp := (bframe 2 (by decide) (by decide) (by decide)).trans asp
  obtain ⟨u,tu,upc,u10,u6,uframe,ucsr⟩ := E5R.Thermostat.FormatStrDispatch.contract_quiet B b r fmt writer bpc b10 hm ha
    ((ViewFrame.word ho 4 (by decide)).trans hv) hw' hrom
  have usp : u.get 2 = sp := (uframe 2 (by decide) (by decide) (by decide)).trans bsp
  have u11 : u.get 11 = c.get 11 := (uframe 11 (by decide) (by decide) (by decide)).trans
    ((bframe 11 (by decide) (by decide) (by decide)).trans (aframe 11 (by decide)))
  have u12 : u.get 12 = c.get 12 := (uframe 12 (by decide) (by decide) (by decide)).trans
    ((bframe 12 (by decide) (by decide) (by decide)).trans (aframe 12 (by decide)))
  obtain ⟨d,td,dpc,dsp,dcsr,dsaved,d10,d11,d12⟩ := E5R.Thermostat.FormatStrRestore.contract_quiet B u r upc
    (by simpa only [usp] using hst) (by simpa only [usp] using hsa)
  have hs := FormatStrSave.saved ram sp c
  have hword (k : Nat) : ramRead r (u.get 2+BitVec.ofNat 32 k) .w = ramRead r (sp+BitVec.ofNat 32 k) .w := by rw [usp]
  refine ⟨d,((ta.trans tb).trans tu).trans td,?_⟩
  refine ⟨by rw [dpc,u6];decide +kernel,by rw [dsp,usp,←hsp],d10.trans u10,d11.trans u11,d12.trans u12,
    ((dcsr.trans ucsr).trans bcsr).trans acsr,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_⟩
  · exact dsaved.x1 |>.trans ((hword 60).trans hs.1)
  · exact dsaved.x8 |>.trans ((hword 56).trans hs.2.1)
  · exact dsaved.x9 |>.trans ((hword 52).trans hs.2.2.1)
  · exact dsaved.x18 |>.trans ((hword 48).trans hs.2.2.2.1)
  · exact dsaved.x19 |>.trans ((hword 44).trans hs.2.2.2.2.1)
  · exact dsaved.x20 |>.trans ((hword 40).trans hs.2.2.2.2.2.1)
  · exact dsaved.x21 |>.trans ((hword 36).trans hs.2.2.2.2.2.2.1)
  · exact dsaved.x22 |>.trans ((hword 32).trans hs.2.2.2.2.2.2.2.1)
  · exact dsaved.x23 |>.trans ((hword 28).trans hs.2.2.2.2.2.2.2.2.1)
  · exact dsaved.x24 |>.trans ((hword 24).trans hs.2.2.2.2.2.2.2.2.2.1)
  · exact dsaved.x25 |>.trans ((hword 20).trans hs.2.2.2.2.2.2.2.2.2.2.1)
  · exact dsaved.x26 |>.trans ((hword 16).trans hs.2.2.2.2.2.2.2.2.2.2.2.1)
  · exact dsaved.x27 |>.trans ((hword 12).trans hs.2.2.2.2.2.2.2.2.2.2.2.2)

end E5R.Thermostat.FormatStr
