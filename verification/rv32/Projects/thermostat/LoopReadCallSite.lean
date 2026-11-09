-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ReadCallSiteIO
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.AdapterQuiet
import Projects.thermostat.ReadEntryQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.LoopReadCallSite
open ReadCallSite
theorem contract_io_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot)
    (h : Pre B c ram s) :
    ∃ n d r, n ≤ 100 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      d.pc = 0x80001a38 ∧ d.get 2 = 0x80ffeb90 ∧ d.get 8 = c.get 8 ∧ d.get 9 = c.get 9 ∧
      d.sameCsr c ∧ Outcome.At r 0x80fffd38 (.ok ⟨none,s⟩) ∧
      Encoding.SnapshotAt r 0x80ffebc0 s ∧ ramRead r 0x80ffebbc .w = 0xffffffff#32 ∧
      (∀ x, (∀ i : Fin 20, x ≠ 0x80fffd38+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 80, x ≠ 0x80ffeb40+BitVec.ofNat 32 i.val) → r x = ram x) ∧ d.get 25 = 0x80ffebc0 ∧ ReadBuffer.Frame c d ∧ d.get 19=c.get 19 ∧ d.get 23=c.get 23 ∧ d.get 26=c.get 26 := by
  obtain ⟨hout,hactor,hstate,hcmd,hbase,hsaved⟩ := pointers c h.sp h.engine
  have hsaveRam : B.inRam (Wrapper.saved (ReadEntry.setup c)) 4 = true := by
    rw [hsaved]
    exact Memory.block_access (B := B) (p := 0x80ffeb40) (n := 5312) (off := 76) (width := 4)
      h.memory (by decide) (by decide)
  have hsaveAlign : (Wrapper.saved (ReadEntry.setup c)).toNat%4 = 0 := by rw [hsaved];decide +kernel
  obtain ⟨n,m,d,hn,hr,hpost,hpc,hsp,hregs,hcsr⟩ := E5R.Thermostat.Adapter.contract_quiet B (ReadEntry.setup c) ram
    false s .read rfl hsaveRam hsaveAlign (establishes_pre B c ram s h)
    (by
      change ∀ k : Fin 4, ∀ i : Fin 20,
        Wrapper.saved (ReadEntry.setup c)+BitVec.ofNat 32 k.val ≠ (entry c).get 10+BitVec.ofNat 32 i.val
      rw [hsaved,hout]
      decide +kernel)
    (by
      change ∀ k : Fin 4, ∀ i : Fin 64,
        Wrapper.saved (ReadEntry.setup c)+BitVec.ofNat 32 k.val ≠ Stack.base (entry c)+BitVec.ofNat 32 i.val
      rw [hsaved,hbase]
      decide +kernel)
  change Call.Post (entry c) (savedRam c ram) m (Spec.transition false s .read) at hpost
  have hframe : ∀ x, (∀ i : Fin 20, x ≠ 0x80fffd38+BitVec.ofNat 32 i.val) →
      (∀ i : Fin 80, x ≠ 0x80ffeb40+BitVec.ofNat 32 i.val) → m.ram x = ram x := by
    intro x hxo hxs
    rw [hpost.frame x (by simpa only [hout] using hxo) (by
      intro i
      rw [hbase]
      exact hxs ⟨i.val,by have := i.isLt;omega⟩)]
    apply saved_frame c ram h.sp
    intro i
    have hi := i.isLt
    have ha : (0x80ffeb40 : Word)+BitVec.ofNat 32 76 = 0x80ffeb8c := by decide +kernel
    simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hxs ⟨76+i.val,by omega⟩
  have hsnap : Encoding.SnapshotAt m.ram 0x80ffebc0 s := by
    intro i
    rw [hframe _ (by
      have hh : ∀ i : Fin 10, ∀ j : Fin 20, (0x80ffebc0 : Word)+BitVec.ofNat 32 i.val ≠
          0x80fffd38+BitVec.ofNat 32 j.val := by decide +kernel
      exact hh i) (by
      have hh : ∀ i : Fin 10, ∀ j : Fin 80, (0x80ffebc0 : Word)+BitVec.ofNat 32 i.val ≠
          0x80ffeb40+BitVec.ofNat 32 j.val := by decide +kernel
      exact hh i)]
    exact h.state i
  have hborrow : ramRead m.ram 0x80ffebbc .w = 0xffffffff#32 := by
    rw [show ramRead m.ram 0x80ffebbc .w = ramRead ram 0x80ffebbc .w by
      apply ramRead_w_congr
      intro k hk
      apply hframe
      · exact (show ∀ k : Fin 4, ∀ j : Fin 20, (0x80ffebbc : Word)+BitVec.ofNat 32 k.val ≠
          0x80fffd38+BitVec.ofNat 32 j.val by decide +kernel) ⟨k,hk⟩
      · exact (show ∀ k : Fin 4, ∀ j : Fin 80, (0x80ffebbc : Word)+BitVec.ofNat 32 k.val ≠
          0x80ffeb40+BitVec.ofNat 32 j.val by decide +kernel) ⟨k,hk⟩]
    exact h.borrowed
  have h8 : d.get 8 = c.get 8 := by
    rw [hregs 8 (by decide) (by decide)]
    have hh := hpost.saved ⟨1,by decide⟩
    change m.core.get 8 = (entry c).get 8 at hh
    rw [hh]
    simp [entry,Wrapper.inner,ReadEntry.setup,Core.wr_get]
  have h9 : d.get 9 = c.get 9 := by
    rw [hregs 9 (by decide) (by decide)]
    have hh := hpost.saved ⟨2,by decide⟩
    change m.core.get 9 = (entry c).get 9 at hh
    rw [hh]
    simp [entry,Wrapper.inner,ReadEntry.setup,Core.wr_get]
  refine ⟨12+n,d,m.ram,by omega,(E5R.Thermostat.ReadEntry.contract_quiet B c ram h.pc).trans hr,?_,?_,h8,h9,
    hcsr.trans (by rfl),?_,hsnap,hborrow,hframe,?_,?_,?_,?_,?_⟩
  · simpa [ReadEntry.setup,Core.wr_get] using hpc
  · simpa [ReadEntry.setup,Core.wr_get,h.sp] using hsp
  · simpa only [hout,Spec.transition] using hpost.outcome
  · rw [hregs 25 (by decide) (by decide),hpost.upper 25 (by decide)]
    simp [entry,Wrapper.inner,ReadEntry.setup,Core.wr_get,h.engine]
  · intro reg hlive
    rcases hlive with he|he|he
    · subst reg
      rw [hregs 20 (by decide) (by decide)]
      have hh := hpost.saved ⟨5,by decide⟩
      change m.core.get 20=(entry c).get 20 at hh
      rw [hh]
      simp [entry,Wrapper.inner,ReadEntry.setup,Core.wr_get_ne]
    · subst reg
      rw [hregs 22 (by decide) (by decide),hpost.upper 22 (by decide)]
      simp [entry,Wrapper.inner,ReadEntry.setup,Core.wr_get_ne]
    · subst reg
      rw [hregs 24 (by decide) (by decide),hpost.upper 24 (by decide)]
      simp [entry,Wrapper.inner,ReadEntry.setup,Core.wr_get_ne]

  · rw [hregs 19 (by decide) (by decide)]
    have hh := hpost.saved ⟨4,by decide⟩
    change m.core.get 19=(entry c).get 19 at hh
    rw [hh]
    simp [entry,Wrapper.inner,ReadEntry.setup,Core.wr_get_ne]
  · rw [hregs 23 (by decide) (by decide),hpost.upper 23 (by decide)]
    simp [entry,Wrapper.inner,ReadEntry.setup,Core.wr_get_ne]
  · rw [hregs 26 (by decide) (by decide),hpost.upper 26 (by decide)]
    simp [entry,Wrapper.inner,ReadEntry.setup,Core.wr_get_ne]
end E5R.Thermostat.LoopReadCallSite
