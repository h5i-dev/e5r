import Projects.thermostat.LoopReadCallSite
-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ReadAcquireIO
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.ReadAcquireQuiet
import Projects.thermostat.ReadCallSiteIOQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.LoopReadAcquire
open ReadAcquire
theorem contract_io_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot)
    (h : Pre B c ram s) :
    ∃ n d r, n ≤ 104 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      d.pc = 0x80001a38 ∧ d.get 2 = 0x80ffeb90 ∧ d.get 8 = c.get 8 ∧ d.get 9 = c.get 9 ∧
      d.sameCsr c ∧ Outcome.At r 0x80fffd38 (.ok ⟨none,s⟩) ∧
      Encoding.SnapshotAt r 0x80ffebc0 s ∧ ramRead r 0x80ffebbc .w = 0xffffffff#32 ∧
      (∀ x, (∀ i : Fin 20, x ≠ 0x80fffd38+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 80, x ≠ 0x80ffeb40+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 4, x ≠ 0x80ffebbc+BitVec.ofNat 32 i.val) → r x = ram x) ∧ d.get 25 = 0x80ffebc0 ∧ ReadBuffer.Frame c d ∧ d.get 19=c.get 19 ∧ d.get 23=c.get 23 ∧ d.get 26=c.get 26 := by
  have he : Memory.Block B (c.get 9) 14 := by
    rw [h.engine]
    exact Memory.sub_block (B := B) (p := 0x80ffeb40) (n := 5312) (off := 124) (m := 14)
      h.memory (by decide) (by decide)
  have ha : (c.get 9).toNat%4 = 0 := by rw [h.engine];decide +kernel
  have hb : ramRead ram (c.get 9) .w = 0#32 := by rw [h.engine];exact h.available
  have hr := E5R.Thermostat.ReadAcquire.available_quiet B c ram h.pc he ha hb
  obtain ⟨n,d,r,hn,hr',hpc,hsp,hfp,heng,hcsr,hout,hstate,hborrow,hframe,h25,hbuf,h19,h23,h26⟩ :=
    LoopReadCallSite.contract_io_quiet B (acquired c) (result ram (c.get 9)) s (establishes_pre B c ram s h)
  refine ⟨4+n,d,r,by omega,hr.trans hr',hpc,hsp,?_,?_,hcsr.trans (by rfl),hout,hstate,hborrow,?_,h25,?_,?_,?_,?_⟩
  · exact hfp.trans (by simp [acquired,Core.wr_get_ne])
  · exact heng.trans (by simp [acquired,Core.wr_get_ne])
  · intro x hxo hxs hxe
    rw [hframe x hxo hxs]
    exact frame ram (c.get 9) x (by simpa only [h.engine] using hxe)
  · intro reg hlive
    exact (hbuf reg hlive).trans (by
      rcases hlive with he|he|he <;> subst reg <;> simp [acquired,Core.wr_get_ne])

  · exact h19.trans (by simp [acquired,Core.wr_get_ne])
  · exact h23.trans (by simp [acquired,Core.wr_get_ne])
  · exact h26.trans (by simp [acquired,Core.wr_get_ne])
end E5R.Thermostat.LoopReadAcquire
