import Projects.thermostat.ReadCallSite
import Projects.thermostat.Acquire
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ReadAcquire
open E5R E5R.Thermostat

def result (ram : Word → BitVec 8) (eng : Word) := ramWrite ram eng 0xffffffff#32 .w

def acquired (c : Core) : Core := (c.wr 10 0xffffffff#32 0x80001a10).goto 0x80001a12

theorem frame (ram : Word → BitVec 8) (eng x : Word)
    (hx : ∀ i : Fin 4, x ≠ eng+BitVec.ofNat 32 i.val) : result ram eng x = ram x := by
  apply ramWrite_w_other
  intro k hk
  exact hx ⟨k,hk⟩

theorem snapshot (ram : Word → BitVec 8) (eng : Word) (s : Spec.Snapshot)
    (hs : Encoding.SnapshotAt ram (eng+4#32) s) : Encoding.SnapshotAt (result ram eng) (eng+4#32) s := by
  intro i
  rw [frame ram eng _ (by
    intro j he
    simp only [BitVec.add_assoc,BitVec.add_right_inj] at he
    have hn := congrArg BitVec.toNat he
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat] at hn
    have hi := i.isLt
    have hj := j.isLt
    omega)]
  exact hs i

/-- The four actual instructions acquire a free RefCell borrow. -/
theorem available (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80001a08) (he : Memory.Block B (c.get 9) 14)
    (ha : (c.get 9).toNat % 4 = 0) (hb : ramRead ram (c.get 9) .w = 0#32) :
    DetSteps B img 4 ⟨c,ram⟩ ⟨acquired c,result ram (c.get 9)⟩ := by
  let eng := c.get 9
  let v := ramRead ram eng .w
  let c1 := c.wr 10 v 0x80001a0a
  have hr : B.inRam eng 4 = true := by
    simpa using Memory.block_access (B := B) (p := eng) (n := 14) (off := 0) (width := 4) he (by decide) (by decide)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact rs2147490312) fun o => ?_
    rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .w) (a := eng) o ha hr,hp]
    rfl
  let c2 := c1.goto 0x80001a0e
  let c3 := c2.wr 10 0xffffffff#32 0x80001a10
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80001a0a : Word).getLsbD 0 = false;decide) rs2147490314 fun o => ?_
    have hv : c1.get 10 = 0#32 := by
      change v = 0#32
      exact hb
    rw [exec_branch,hv,Core.get_zero]
    rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80001a0e : Word).getLsbD 0 = false;decide) rs2147490318 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    simp only [alu,BitVec.zero_add]
    rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨acquired c,result ram eng⟩ := by
    refine detStep_of (by change (0x80001a10 : Word).getLsbD 0 = false;decide) rs2147490320 fun o => ?_
    have hs : c3.get 9 = eng := by simp [c3,c2,c1,eng,Core.wr_get_ne]
    have hv : c3.get 10 = 0xffffffff#32 := by simp [c3,Core.wr_get]
    rw [exec_store,hs,hv,BitVec.add_zero,interp_store_ram (B := B) (img := img) (w := .w) (a := eng) (v := 0xffffffff#32) o ha hr]
    change Result.ok (c3.goto 0x80001a12) (result ram eng) [] = _
    congr 1
    change ((c.wr 10 v 0x80001a0a).wr 10 0xffffffff#32 0x80001a12) = c.wr 10 0xffffffff#32 0x80001a12
    simp [Core.wr,Core.set]
    funext i
    by_cases hi : i = 10 <;> simp [hi]
  exact .step s0 (.step s1 (.step s2 (.single s3)))

/-- A nonzero word branches to the panic call boundary without RAM writes. -/
theorem unavailable (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80001a08) (he : Memory.Block B (c.get 9) 14)
    (ha : (c.get 9).toNat % 4 = 0) (hb : ramRead ram (c.get 9) .w ≠ 0#32) :
    DetSteps B img 2 ⟨c,ram⟩ ⟨c.wr 10 (ramRead ram (c.get 9) .w) 0x80001d16,ram⟩ := by
  let eng := c.get 9
  let v := ramRead ram eng .w
  let c1 := c.wr 10 v 0x80001a0a
  have hr : B.inRam eng 4 = true := by
    simpa using Memory.block_access (B := B) (p := eng) (n := 14) (off := 0) (width := 4) he (by decide) (by decide)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact rs2147490312) fun o => ?_
    rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .w) (a := eng) o ha hr,hp]
    rfl
  apply DetSteps.step s0
  apply DetSteps.single
  refine detStep_of (by change (0x80001a0a : Word).getLsbD 0 = false;decide) rs2147490314 fun o => ?_
  have hv : c1.get 10 = v := by simp [c1,Core.wr_get]
  rw [exec_branch,hv,Core.get_zero]
  have hb' : v ≠ 0#32 := hb
  have ht : taken .ne v 0 = true := by simp [taken,hb']
  rw [ht]
  simp only [ite_true]
  change interp B img o (jump c1 0x80001d16) ram 0 [] = _
  rw [jump_ok c1 _ (by decide)]
  rfl


/-- Actual separate Read caller before the RefCell acquisition. -/
structure Pre (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot) : Prop where
  pc : c.pc = 0x80001a08
  sp : c.get 2 = 0x80ffeb90
  engine : c.get 9 = 0x80ffebbc
  fp : c.get 8 = 0x80fff814
  memory : Memory.Block B 0x80ffeb40 5312
  state : Encoding.SnapshotAt ram 0x80ffebc0 s
  actor : ram 0x80fffe68 = 0
  command : Encoding.CommandAt ram 0x80fffb10 .read
  available : ramRead ram 0x80ffebbc .w = 0#32

theorem establishes_pre (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot)
    (h : Pre B c ram s) : ReadCallSite.Pre B (acquired c) (result ram (c.get 9)) s := by
  have hg (r : Reg) (hr : r ≠ 10) : (acquired c).get r = c.get r := by
    simp [acquired,Core.wr_get_ne,hr]
  have hf (x : Word) (hx : ∀ i : Fin 4, x ≠ 0x80ffebbc+BitVec.ofNat 32 i.val) :
      result ram (c.get 9) x = ram x := by
    apply frame
    simpa only [h.engine] using hx
  refine ⟨rfl,(hg 2 (by decide)).trans h.sp,(hg 9 (by decide)).trans h.engine,
    (hg 8 (by decide)).trans h.fp,h.memory,?_,?_,?_,?_⟩
  · have hs : (0x80ffebbc : Word)+4#32 = 0x80ffebc0 := by decide +kernel
    rw [h.engine,←hs]
    exact snapshot ram _ s (by rw [hs];exact h.state)
  · rw [hf _ (by decide +kernel)]
    exact h.actor
  · apply Encoding.command_preserve ram _ _ .read h.command
    intro i
    apply hf
    exact (show ∀ i j : Fin 4, (0x80fffb10 : Word)+BitVec.ofNat 32 i.val ≠
      0x80ffebbc+BitVec.ofNat 32 j.val by decide +kernel) i
  · rw [←h.engine]
    exact ramRead_ramWrite_w ram (c.get 9) 0xffffffff#32

/-- Free borrow acquisition through the distinct Read call site. The borrow
    is held here; persistence/release and response encoding are later code. -/
theorem contract_full (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot)
    (h : Pre B c ram s) :
    ∃ n d r, n ≤ 104 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      d.pc = 0x80001a38 ∧ d.get 2 = 0x80ffeb90 ∧ d.get 8 = c.get 8 ∧ d.get 9 = c.get 9 ∧
      d.sameCsr c ∧ Outcome.At r 0x80fffd38 (.ok ⟨none,s⟩) ∧
      Encoding.SnapshotAt r 0x80ffebc0 s ∧ ramRead r 0x80ffebbc .w = 0xffffffff#32 ∧
      (∀ x, (∀ i : Fin 20, x ≠ 0x80fffd38+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 80, x ≠ 0x80ffeb40+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 4, x ≠ 0x80ffebbc+BitVec.ofNat 32 i.val) → r x = ram x) ∧ d.get 25 = 0x80ffebc0 := by
  have he : Memory.Block B (c.get 9) 14 := by
    rw [h.engine]
    exact Memory.sub_block (B := B) (p := 0x80ffeb40) (n := 5312) (off := 124) (m := 14)
      h.memory (by decide) (by decide)
  have ha : (c.get 9).toNat%4 = 0 := by rw [h.engine];decide +kernel
  have hb : ramRead ram (c.get 9) .w = 0#32 := by rw [h.engine];exact h.available
  have hr := available B c ram h.pc he ha hb
  obtain ⟨n,d,r,hn,hr',hpc,hsp,hfp,heng,hcsr,hout,hstate,hborrow,hframe,h25⟩ :=
    ReadCallSite.contract_full B (acquired c) (result ram (c.get 9)) s (establishes_pre B c ram s h)
  refine ⟨4+n,d,r,by omega,hr.trans hr',hpc,hsp,?_,?_,hcsr.trans (by rfl),hout,hstate,hborrow,?_,h25⟩
  · exact hfp.trans (by simp [acquired,Core.wr_get_ne])
  · exact heng.trans (by simp [acquired,Core.wr_get_ne])
  · intro x hxo hxs hxe
    rw [hframe x hxo hxs]
    exact frame ram (c.get 9) x (by simpa only [h.engine] using hxe)
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot)
    (h : Pre B c ram s) :
    ∃ n d r, n ≤ 104 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      d.pc = 0x80001a38 ∧ d.get 2 = 0x80ffeb90 ∧ d.get 8 = c.get 8 ∧ d.get 9 = c.get 9 ∧
      d.sameCsr c ∧ Outcome.At r 0x80fffd38 (.ok ⟨none,s⟩) ∧
      Encoding.SnapshotAt r 0x80ffebc0 s ∧ ramRead r 0x80ffebbc .w = 0xffffffff#32 ∧
      (∀ x, (∀ i : Fin 20, x ≠ 0x80fffd38+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 80, x ≠ 0x80ffeb40+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 4, x ≠ 0x80ffebbc+BitVec.ofNat 32 i.val) → r x = ram x) := by
  obtain ⟨n,d,r,hn,hr,hpc,hsp,h8,h9,hcsr,hout,hsnap,hborrow,hframe,_⟩ := contract_full B c ram s h
  exact ⟨n,d,r,hn,hr,hpc,hsp,h8,h9,hcsr,hout,hsnap,hborrow,hframe⟩

end E5R.Thermostat.ReadAcquire
