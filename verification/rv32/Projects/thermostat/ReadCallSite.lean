import Projects.thermostat.ReadEntry
import Projects.thermostat.Adapter
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ReadCallSite
open E5R E5R.Thermostat

def entry (c : Core) := Wrapper.inner (ReadEntry.setup c)
def savedRam (c : Core) (ram : Word → BitVec 8) := Wrapper.save (ReadEntry.setup c) ram

structure Pre (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot) : Prop where
  pc : c.pc = 0x80001a12
  sp : c.get 2 = 0x80ffeb90
  engine : c.get 9 = 0x80ffebbc
  fp : c.get 8 = 0x80fff814
  memory : Memory.Block B 0x80ffeb40 5312
  state : Encoding.SnapshotAt ram 0x80ffebc0 s
  actor : ram 0x80fffe68 = 0
  command : Encoding.CommandAt ram 0x80fffb10 .read
  borrowed : ramRead ram 0x80ffebbc .w = 0xffffffff#32

theorem pointers (c : Core) (hsp : c.get 2 = 0x80ffeb90) (he : c.get 9 = 0x80ffebbc) :
    (entry c).get 10 = 0x80fffd38 ∧ (entry c).get 11 = 0x80fffe68 ∧
    (entry c).get 12 = 0x80ffebc0 ∧ (entry c).get 13 = 0x80fffb10 ∧
    Stack.base (entry c) = 0x80ffeb40 ∧
    Wrapper.saved (ReadEntry.setup c) = 0x80ffeb8c := by
  simp [entry,ReadEntry.setup,Wrapper.inner,Wrapper.low,Wrapper.saved,Stack.base,Core.wr_get,hsp,he]

theorem saved_frame (c : Core) (ram : Word → BitVec 8) (hsp : c.get 2 = 0x80ffeb90)
    (x : Word) (hx : ∀ i : Fin 4, x ≠ 0x80ffeb8c+BitVec.ofNat 32 i.val) :
    savedRam c ram x = ram x := by
  have hs : Wrapper.saved (ReadEntry.setup c) = 0x80ffeb8c := by
    simp [ReadEntry.setup,Wrapper.saved,Wrapper.low,Core.wr_get,hsp]
  unfold savedRam Wrapper.save
  rw [hs]
  exact ramWrite_w_other _ _ _ x (fun i hi => hx ⟨i,hi⟩)

theorem establishes_pre (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot)
    (h : Pre B c ram s) : Call.Pre B (entry c) (savedRam c ram) false s .read := by
  obtain ⟨hout,hactor,hstate,hcmd,hbase,hsaved⟩ := pointers c h.sp h.engine
  have mem (a : Word) (n off : Nat) (hn : 0 < n) (ha : a = 0x80ffeb40+BitVec.ofNat 32 off)
      (hb : off+n ≤ 5312) : Memory.Block B a n := by
    rw [ha]
    exact Memory.sub_block h.memory hn hb
  have hstateSaved : Encoding.SnapshotAt (savedRam c ram) 0x80ffebc0 s := by
    intro i
    rw [saved_frame c ram h.sp _ (by
      have hn : ∀ i : Fin 10, ∀ j : Fin 4,
          (0x80ffebc0 : Word)+BitVec.ofNat 32 i.val ≠ 0x80ffeb8c+BitVec.ofNat 32 j.val := by decide +kernel
      exact hn i)]
    exact h.state i
  have hcommandSaved : Encoding.CommandAt (savedRam c ram) 0x80fffb10 .read := by
    apply Encoding.command_preserve ram _ _ .read h.command
    intro i
    apply saved_frame c ram h.sp
    have hn : ∀ i j : Fin 4, (0x80fffb10 : Word)+BitVec.ofNat 32 i.val ≠
        0x80ffeb8c+BitVec.ofNat 32 j.val := by decide +kernel
    exact hn i
  refine ⟨rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hstate];exact mem _ 10 128 (by decide) (by decide +kernel) (by decide)
  · rw [hstate];decide +kernel
  · rw [hcmd];exact mem _ 4 4048 (by decide) (by decide +kernel) (by decide)
  · rw [hcmd];decide +kernel
  · rw [hactor];exact mem _ 1 4904 (by decide) (by decide +kernel) (by decide)
  · rw [hout];exact mem _ 20 4600 (by decide) (by decide +kernel) (by decide)
  · rw [hout];decide +kernel
  · rw [hbase];exact mem _ 64 0 (by decide) (by decide +kernel) (by decide)
  · rw [hbase];decide +kernel
  · rw [hstate];exact hstateSaved
  · rw [hcmd];exact hcommandSaved
  · rw [hactor,saved_frame c ram h.sp _ (by decide +kernel)]
    exact h.actor
  · unfold Call.Separate;rw [hstate,hbase];decide +kernel
  · unfold Call.Separate;rw [hcmd,hbase];decide +kernel
  · unfold Call.Separate;rw [hactor,hbase];decide +kernel
  · unfold Call.Separate;rw [hout,hbase];decide +kernel

/-- The actual separate Read-handler setup, adapter, kernel and return. This
    stops before Result dispatch; its borrow is still held at this boundary. -/
theorem contract_full (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot)
    (h : Pre B c ram s) :
    ∃ n d r, n ≤ 100 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      d.pc = 0x80001a38 ∧ d.get 2 = 0x80ffeb90 ∧ d.get 8 = c.get 8 ∧ d.get 9 = c.get 9 ∧
      d.sameCsr c ∧ Outcome.At r 0x80fffd38 (.ok ⟨none,s⟩) ∧
      Encoding.SnapshotAt r 0x80ffebc0 s ∧ ramRead r 0x80ffebbc .w = 0xffffffff#32 ∧
      (∀ x, (∀ i : Fin 20, x ≠ 0x80fffd38+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 80, x ≠ 0x80ffeb40+BitVec.ofNat 32 i.val) → r x = ram x) ∧ d.get 25 = 0x80ffebc0 := by
  obtain ⟨hout,hactor,hstate,hcmd,hbase,hsaved⟩ := pointers c h.sp h.engine
  have hsaveRam : B.inRam (Wrapper.saved (ReadEntry.setup c)) 4 = true := by
    rw [hsaved]
    exact Memory.block_access (B := B) (p := 0x80ffeb40) (n := 5312) (off := 76) (width := 4)
      h.memory (by decide) (by decide)
  have hsaveAlign : (Wrapper.saved (ReadEntry.setup c)).toNat%4 = 0 := by rw [hsaved];decide +kernel
  obtain ⟨n,m,d,hn,hr,hpost,hpc,hsp,hregs,hcsr⟩ := Adapter.contract B (ReadEntry.setup c) ram
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
  refine ⟨12+n,d,m.ram,by omega,(ReadEntry.contract B c ram h.pc).trans hr,?_,?_,h8,h9,
    hcsr.trans (by rfl),?_,hsnap,hborrow,hframe,?_⟩
  · simpa [ReadEntry.setup,Core.wr_get] using hpc
  · simpa [ReadEntry.setup,Core.wr_get,h.sp] using hsp
  · simpa only [hout,Spec.transition] using hpost.outcome
  · rw [hregs 25 (by decide) (by decide),hpost.upper 25 (by decide)]
    simp [entry,Wrapper.inner,ReadEntry.setup,Core.wr_get,h.engine]

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot)
    (h : Pre B c ram s) :
    ∃ n d r, n ≤ 100 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      d.pc = 0x80001a38 ∧ d.get 2 = 0x80ffeb90 ∧ d.get 8 = c.get 8 ∧ d.get 9 = c.get 9 ∧
      d.sameCsr c ∧ Outcome.At r 0x80fffd38 (.ok ⟨none,s⟩) ∧
      Encoding.SnapshotAt r 0x80ffebc0 s ∧ ramRead r 0x80ffebbc .w = 0xffffffff#32 ∧
      (∀ x, (∀ i : Fin 20, x ≠ 0x80fffd38+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 80, x ≠ 0x80ffeb40+BitVec.ofNat 32 i.val) → r x = ram x) := by
  obtain ⟨n,d,r,hn,hr,hpc,hsp,h8,h9,hcsr,hout,hsnap,hborrow,hframe,_⟩ := contract_full B c ram s h
  exact ⟨n,d,r,hn,hr,hpc,hsp,h8,h9,hcsr,hout,hsnap,hborrow,hframe⟩

end E5R.Thermostat.ReadCallSite
