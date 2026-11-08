-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CursorFinishFull
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.CursorFinishQuiet
import Projects.thermostat.CursorRestoreFullQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.CursorFinish
theorem contract_full_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (remaining len : Nat)
    (hp : c.pc = 0x800022dc#32) (h18 : c.get 18 = BitVec.ofNat 32 remaining) (h8 : c.get 8 = BitVec.ofNat 32 len)
    (hr : remaining < 2^32) (hl : len < 2^32) (hm : Memory.Block B (c.get 2) 32) (ha : (c.get 2).toNat%4 = 0) :
    ∃ d, Quiet.Steps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = ramRead ram (c.get 2+28#32) .w &&& ~~~1 ∧
      d.get 2 = c.get 2+32#32 ∧ d.get 10 = flagWord remaining len ∧ CursorRestore.Restored c d ram ∧ d.sameCsr c ∧ HighFrame.Frame c d := by
  let a := c.wr 10 (flagWord remaining len) 0x800022e0#32
  have ta : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := E5R.Thermostat.CursorFinish.flag_quiet B c ram remaining len hp h18 h8 hr hl
  have asp : a.get 2 = c.get 2 := Core.wr_get_ne _ _ _ _ _ (by decide)
  obtain ⟨d,td,dpc,dsp,dsaved,d10,dcsr,dhigh⟩ := E5R.Thermostat.CursorRestore.contract_full_quiet B a ram rfl (by simpa only [asp] using hm) (by simpa only [asp] using ha)
  refine ⟨d,.step ta td,by simpa only [asp] using dpc,by simpa only [asp] using dsp,?_,?_,dcsr.trans (by rfl),?_⟩
  · exact d10.trans (Core.wr_get_self _ _ _ _ (by decide))
  · constructor
    · simpa only [asp] using dsaved.x1
    · simpa only [asp] using dsaved.x8
    · simpa only [asp] using dsaved.x9
    · simpa only [asp] using dsaved.x18
    · simpa only [asp] using dsaved.x19
  · intro r hr
    exact (dhigh r hr).trans (Core.wr_get_ne _ _ _ _ _ (HighFrame.ne r 10 hr (by decide)))

end E5R.Thermostat.CursorFinish
