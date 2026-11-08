import Projects.thermostat.ReadAcquire
import Projects.thermostat.ReadDispatch
import Projects.thermostat.ReadMarshal
import Projects.thermostat.ApplyAdapter
import Projects.thermostat.ReadState
import Projects.thermostat.ReadRestore
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ReadEngine
open E5R E5R.Thermostat

/-- Exact blocks that this inlined Read transaction is permitted to change. -/
def Away (x : Word) : Prop :=
  (∀ i : Fin 80, x ≠ 0x80ffeb40#32+BitVec.ofNat 32 i.val) ∧
  (∀ i : Fin 16, x ≠ 0x80ffeb98#32+BitVec.ofNat 32 i.val) ∧
  (∀ i : Fin 20, x ≠ 0x80fffd38#32+BitVec.ofNat 32 i.val) ∧
  (∀ i : Fin 10, x ≠ 0x80fffeb8#32+BitVec.ofNat 32 i.val) ∧
  (∀ i : Fin 14, x ≠ 0x80ffebbc#32+BitVec.ofNat 32 i.val)

structure Post (c d : Core) (ram ram' : Word → BitVec 8) (s : Spec.Snapshot) : Prop where
  pc : d.pc = 0x80001b5e#32
  sp : d.get 2 = 0x80ffeb90#32
  fp : d.get 8 = c.get 8
  engine : d.get 9 = c.get 9
  statePtr : d.get 25 = 0x80ffebc0#32
  csr : d.sameCsr c
  state : Encoding.SnapshotAt ram' 0x80ffebc0#32 s
  released : ramRead ram' 0x80ffebbc#32 .w = 0#32
  reply : Encoding.SnapshotAt ram' 0x80fffd38#32 s
  frame : ∀ x, Away x → ram' x = ram x

/-- Real separate Read acquisition, transition call, Result dispatch, Option
    extraction, apply, RAM persistence, borrow release and reply reconstruction.
    Stops before the response encoder, at the completed transaction boundary. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot)
    (h : ReadAcquire.Pre B c ram s) :
    ∃ n d r, n ≤ 194 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧ Post c d ram r s := by
  obtain ⟨n0,c0,r0,hn0,hr0,hpc0,hsp0,hfp0,heng0,hcsr0,hout0,hstate0,hborrow0,hframe0,h25⟩ :=
    ReadAcquire.contract_full B c ram s h
  have hfp0' : c0.get 8 = 0x80fff814#32 := hfp0.trans h.fp
  let cd := ReadDispatch.next c0 r0
  obtain ⟨hpcd,hspd,hfpd,hengd,h25d,hcsrd⟩ := ReadDispatch.fields c0 r0
  have hrd := ReadDispatch.contract B c0 r0 s hpc0 hfp0' h.memory hout0
  let cm := (ReadMarshal.execute cd r0).core
  let rm := ReadMarshal.memory r0
  have hrm := ReadMarshal.contract B cd r0 hpcd (hspd.trans hsp0) (hfpd.trans hfp0')
    (h25d.trans h25) (ReadDispatch.tag c0 r0 s hout0) h.memory
  obtain ⟨hpcm,hraM,houtM,hstateM,hwriteM,hspm,hfpm,hengm,h18m,h25m,hcsrm⟩ := ReadMarshal.fields cd r0
  change cm.get 10 = 0x80fffd38#32 at houtM
  have hspM : cm.get 2 = 0x80ffeb90#32 := hspm.trans (hspd.trans hsp0)
  have hfpM : cm.get 8 = 0x80fff814#32 := hfpm.trans (hfpd.trans hfp0')
  have hengM : cm.get 9 = 0x80ffebbc#32 := hengm.trans (hengd.trans (heng0.trans h.engine))
  have h25M : cm.get 25 = 0x80ffebc0#32 := h25m.trans (h25d.trans h25)
  have hmEngine (i : Fin 14) : rm (0x80ffebbc#32+BitVec.ofNat 32 i.val) =
      r0 (0x80ffebbc#32+BitVec.ofNat 32 i.val) := by
    apply ReadMarshal.frame
    · exact (show ∀ i : Fin 14, ∀ j : Fin 10, (0x80ffebbc#32+BitVec.ofNat 32 i.val) ≠
        0x80fffeb8#32+BitVec.ofNat 32 j.val by decide +kernel) i
    · exact (show ∀ i : Fin 14, ∀ j : Fin 16, (0x80ffebbc#32+BitVec.ofNat 32 i.val) ≠
        0x80ffeb98#32+BitVec.ofNat 32 j.val by decide +kernel) i
  have hstateRm : Encoding.SnapshotAt rm 0x80ffebc0#32 s := by
    intro i
    have hh := hmEngine ⟨4+i.val,by have := i.isLt;omega⟩
    have ha : (0x80ffebbc#32+BitVec.ofNat 32 (4+i.val)) = 0x80ffebc0#32+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [ha] at hh
    exact hh.trans (hstate0 i)
  have hborrowRm : ramRead rm 0x80ffebbc#32 .w = 0xffffffff#32 := by
    rw [show ramRead rm 0x80ffebbc#32 .w = ramRead r0 0x80ffebbc#32 .w by
      apply ramRead_w_congr;intro k hk;exact hmEngine ⟨k,by omega⟩]
    exact hborrow0
  have hcacheM : ReadCache.At cm rm s := ReadMarshal.cached cd r0 s hout0.2 (ReadDispatch.first c0 r0)
  have hslot : ApplyWrapper.saved cm = 0x80ffeb8c#32 := by
    simp [ApplyWrapper.saved,ApplyWrapper.low,hspM]
  have hslotFrame (x : Word) (hx : ∀ i : Fin 4, x ≠ 0x80ffeb8c#32+BitVec.ofNat 32 i.val) :
      ApplyWrapper.save cm rm x = rm x := by
    unfold ApplyWrapper.save
    rw [hslot]
    exact ramWrite_w_other _ _ _ x (fun k hk => hx ⟨k,hk⟩)
  have hss : Encoding.SnapshotAt (ApplyWrapper.save cm rm) (cm.get 11) s := by
    rw [hstateM]
    intro i
    rw [hslotFrame _ (by
      exact (show ∀ i : Fin 10, ∀ j : Fin 4, 0x80ffebc0#32+BitVec.ofNat 32 i.val ≠
        0x80ffeb8c#32+BitVec.ofNat 32 j.val by decide +kernel) i)]
    exact hstateRm i
  have hsw : Encoding.OptionAt (ApplyWrapper.save cm rm) (cm.get 12) none := by
    rw [hwriteM]
    change ApplyWrapper.save cm rm 0x80fffeb8#32 = 2#8
    rw [hslotFrame _ (by decide +kernel)]
    exact ReadMarshal.option_none r0
  have hmem (a : Word) (off n : Nat) (hn : 0 < n)
      (heq : a = 0x80ffeb40#32+BitVec.ofNat 32 off) (hfit : off+n ≤ 5312) : Memory.Block B a n := by
    rw [heq]
    exact Memory.sub_block h.memory hn hfit
  have hhalf (a : Word) (off : Nat) (heq : a = 0x80ffeb40#32+BitVec.ofNat 32 off)
      (hfit : off+10 ≤ 5312) (hal : a.toNat%2 = 0) : Apply.HalfBlock B a :=
    Memory.half_block (hmem a off 10 (by decide) heq hfit) hal
  obtain ⟨na,ca,ra,hna,hra,hpca,hspca,hcsrca,hcomputed,hframea,hregsa⟩ :=
    ApplyAdapter.contract B cm rm s none hpcm
      (by rw [hslot];exact Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 76) (width := 4) h.memory (by decide) (by decide))
      (by rw [hslot];decide +kernel)
      (by rw [hwriteM];exact Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4984) (width := 1) h.memory (by decide) (by decide))
      (by rw [hstateM];exact hhalf _ 128 (by decide +kernel) (by decide) (by decide +kernel))
      (by rw [hwriteM];exact hhalf _ 4984 (by decide +kernel) (by decide) (by decide +kernel))
      (by rw [houtM];exact hhalf _ 4600 (by decide +kernel) (by decide) (by decide +kernel))
      hss hsw (by rw [hslot,houtM];decide +kernel)
  have hpcA : ca.pc = 0x80001b12#32 := by rw [hpca,hraM];decide +kernel
  have hspA : ca.get 2 = 0x80ffeb90#32 := hspca.trans hspM
  have hfpa := hregsa 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have henga := hregsa 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h25a := hregsa 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hframeA (x : Word) (ho : ∀ i : Fin 10, x ≠ 0x80fffd38#32+BitVec.ofNat 32 i.val)
      (hs : ∀ i : Fin 4, x ≠ 0x80ffeb8c#32+BitVec.ofNat 32 i.val) : ra x = rm x :=
    hframea x (by simpa only [houtM] using ho) (by simpa only [hslot] using hs)
  have hcacheWords (a : Word) (ha : a = 0x80ffeb98#32 ∨ a = 0x80ffeba4#32 ∨ a = 0x80ffeb9c#32) :
      ramRead ra a .w = ramRead rm a .w := by
    apply ramRead_w_congr
    intro k hk
    apply hframeA
    · rcases ha with rfl|rfl|rfl <;> exact (show ∀ k : Fin 4, ∀ i : Fin 10,
        _+BitVec.ofNat 32 k.val ≠ 0x80fffd38#32+BitVec.ofNat 32 i.val by decide +kernel) ⟨k,hk⟩
    · rcases ha with rfl|rfl|rfl <;> exact (show ∀ k : Fin 4, ∀ i : Fin 4,
        _+BitVec.ofNat 32 k.val ≠ 0x80ffeb8c#32+BitVec.ofNat 32 i.val by decide +kernel) ⟨k,hk⟩
  have hcacheA : ReadCache.At ca ra s := ReadCache.preserve cm ca rm ra s hcacheM
    (hregsa 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hregsa 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hregsa 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hcacheWords _ (Or.inl rfl)) (hcacheWords _ (Or.inr (Or.inl rfl))) (hcacheWords _ (Or.inr (Or.inr rfl)))
  have hborrowA : ramRead ra 0x80ffebbc#32 .w = 0xffffffff#32 := by
    rw [show ramRead ra 0x80ffebbc#32 .w = ramRead rm 0x80ffebbc#32 .w by
      apply ramRead_w_congr
      intro k hk
      apply hframeA
      · exact (show ∀ k : Fin 4, ∀ i : Fin 10, 0x80ffebbc#32+BitVec.ofNat 32 k.val ≠
          0x80fffd38#32+BitVec.ofNat 32 i.val by decide +kernel) ⟨k,hk⟩
      · exact (show ∀ k i : Fin 4, 0x80ffebbc#32+BitVec.ofNat 32 k.val ≠
          0x80ffeb8c#32+BitVec.ofNat 32 i.val by decide +kernel) ⟨k,hk⟩]
    exact hborrowRm
  let cs := (ReadState.execute ca ra).core
  let rs := ReadState.memory ca ra
  have hrs := ReadState.contract B ca ra hpcA hspA (hfpa.trans hfpM) (h25a.trans h25M) (henga.trans hengM) h.memory
  obtain ⟨hpcs,hsps,hfps,hengs,h18s,h21s,h25s,h27s,hcsrs⟩ := ReadState.fields ca ra
  have hcomputed' : Encoding.SnapshotAt ra 0x80fffd38#32 s := by
    simpa only [houtM,Spec.apply] using hcomputed
  have hstateS : Encoding.SnapshotAt rs 0x80ffebc0#32 s := ReadState.source ca ra s hcomputed'
  have hreleasedS : ramRead rs 0x80ffebbc#32 .w = 0#32 := ReadState.released ca ra hborrowA
  have hsWords (a : Word) (ha : a = 0x80ffeb98#32 ∨ a = 0x80ffeba4#32 ∨ a = 0x80ffeb9c#32) :
      ramRead rs a .w = ramRead ra a .w := by
    apply ramRead_w_congr
    intro k hk
    apply ReadState.frame
    rcases ha with rfl|rfl|rfl <;> exact (show ∀ k : Fin 4, ∀ i : Fin 14,
      _+BitVec.ofNat 32 k.val ≠ 0x80ffebbc#32+BitVec.ofNat 32 i.val by decide +kernel) ⟨k,hk⟩
  have hcacheS : ReadCache.At cs rs s := ReadCache.preserve ca cs ra rs s hcacheA h18s h21s h27s
    (hsWords _ (Or.inl rfl)) (hsWords _ (Or.inr (Or.inl rfl))) (hsWords _ (Or.inr (Or.inr rfl)))
  let d := (ReadRestore.execute cs rs).core
  let r := ReadRestore.memory cs rs
  have hrr := ReadRestore.contract B cs rs hpcs (hsps.trans hspA) (hfps.trans (hfpa.trans hfpM))
    (h25s.trans (h25a.trans h25M)) (hengs.trans (henga.trans hengM)) h.memory
  obtain ⟨hpcR,hspR,hfpR,hengR,h18R,h21R,h25R,h27R,hcsrR⟩ := ReadRestore.fields cs rs
  have hrestoreEngine (i : Fin 14) : r (0x80ffebbc#32+BitVec.ofNat 32 i.val) =
      rs (0x80ffebbc#32+BitVec.ofNat 32 i.val) := by
    apply ReadRestore.frame
    exact (show ∀ i : Fin 14, ∀ j : Fin 10, 0x80ffebbc#32+BitVec.ofNat 32 i.val ≠
      0x80fffd38#32+BitVec.ofNat 32 j.val by decide +kernel) i
  refine ⟨n0+4+42+na+13+9,d,r,by omega,((((hr0.trans hrd).trans hrm).trans hra).trans hrs).trans hrr,?_⟩
  refine ⟨hpcR,hspR.trans (hsps.trans hspA),hfpR.trans (hfps.trans (hfpa.trans (hfpm.trans (hfpd.trans hfp0)))),
    hengR.trans (hengs.trans (henga.trans (hengm.trans (hengd.trans heng0)))),h25R.trans (h25s.trans (h25a.trans h25M)),
    hcsrR.trans (hcsrs.trans (hcsrca.trans (hcsrm.trans (hcsrd.trans hcsr0)))),?_,?_,ReadRestore.source cs rs s hcacheS,?_⟩
  · intro i
    have hh := hrestoreEngine ⟨4+i.val,by have := i.isLt;omega⟩
    have ha : (0x80ffebbc#32+BitVec.ofNat 32 (4+i.val)) = 0x80ffebc0#32+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [ha] at hh
    exact hh.trans (hstateS i)
  · rw [show ramRead r 0x80ffebbc#32 .w = ramRead rs 0x80ffebbc#32 .w by
      apply ramRead_w_congr;intro k hk;exact hrestoreEngine ⟨k,by omega⟩]
    exact hreleasedS
  · intro x hx
    change ReadRestore.memory cs rs x = ram x
    rw [ReadRestore.frame cs rs x (fun i => hx.2.2.1 ⟨i.val,by have := i.isLt;omega⟩)]
    change ReadState.memory ca ra x = ram x
    rw [ReadState.frame ca ra x hx.2.2.2.2]
    rw [hframeA x (fun i => hx.2.2.1 ⟨i.val,by have := i.isLt;omega⟩) (by
      intro i
      have ha : 0x80ffeb8c#32+BitVec.ofNat 32 i.val = 0x80ffeb40#32+BitVec.ofNat 32 (76+i.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha];exact hx.1 ⟨76+i.val,by have := i.isLt;omega⟩)]
    change ReadMarshal.memory r0 x = ram x
    rw [ReadMarshal.frame r0 x hx.2.2.2.1 hx.2.1]
    exact hframe0 x hx.2.2.1 hx.1 (fun i => hx.2.2.2.2 ⟨i.val,by have := i.isLt;omega⟩)

theorem contract_inv (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot)
    (h : ReadAcquire.Pre B c ram s) (hi : Spec.Inv s) :
    ∃ n d r, n ≤ 194 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      Post c d ram r s ∧ Engine.InvariantAt r (c.get 9) := by
  obtain ⟨n,d,r,hn,hr,hp⟩ := contract B c ram s h
  refine ⟨n,d,r,hn,hr,hp,?_⟩
  rw [h.engine]
  exact ⟨s,hp.state,hi⟩

end E5R.Thermostat.ReadEngine
