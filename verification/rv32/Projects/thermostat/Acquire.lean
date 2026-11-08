import Projects.thermostat.AcquireCode
import Projects.thermostat.Engine
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.Acquire
open E5R E5R.Thermostat

def result (ram : Word → BitVec 8) (eng : Word) := ramWrite ram eng 0xffffffff#32 .w

def acquired (c : Core) : Core := (c.wr 10 0xffffffff#32 0x8000061e).goto 0x80000622

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
    (hp : c.pc = 0x80000614) (he : Memory.Block B (c.get 23) 14)
    (ha : (c.get 23).toNat % 4 = 0) (hb : ramRead ram (c.get 23) .w = 0#32) :
    DetSteps B img 4 ⟨c,ram⟩ ⟨acquired c,result ram (c.get 23)⟩ := by
  let eng := c.get 23
  let v := ramRead ram eng .w
  let c1 := c.wr 10 v 0x80000618
  have hr : B.inRam eng 4 = true := by
    simpa using Memory.block_access (B := B) (p := eng) (n := 14) (off := 0) (width := 4) he (by decide) (by decide)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact ac2147485204) fun o => ?_
    rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .w) (a := eng) o ha hr,hp]
    rfl
  let c2 := c1.goto 0x8000061c
  let c3 := c2.wr 10 0xffffffff#32 0x8000061e
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80000618 : Word).getLsbD 0 = false;decide) ac2147485208 fun o => ?_
    have hv : c1.get 10 = 0#32 := by
      change v = 0#32
      exact hb
    rw [exec_branch,hv,Core.get_zero]
    rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x8000061c : Word).getLsbD 0 = false;decide) ac2147485212 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    simp only [alu,BitVec.zero_add]
    rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨acquired c,result ram eng⟩ := by
    refine detStep_of (by change (0x8000061e : Word).getLsbD 0 = false;decide) ac2147485214 fun o => ?_
    have hs : c3.get 23 = eng := by simp [c3,c2,c1,eng,Core.wr_get_ne]
    have hv : c3.get 10 = 0xffffffff#32 := by simp [c3,Core.wr_get]
    rw [exec_store,hs,hv,BitVec.add_zero,interp_store_ram (B := B) (img := img) (w := .w) (a := eng) (v := 0xffffffff#32) o ha hr]
    change Result.ok (c3.goto 0x80000622) (result ram eng) [] = _
    congr 1
    change ((c.wr 10 v 0x80000618).wr 10 0xffffffff#32 0x80000622) = c.wr 10 0xffffffff#32 0x80000622
    simp [Core.wr,Core.set]
    funext i
    by_cases hi : i = 10 <;> simp [hi]
  exact .step s0 (.step s1 (.step s2 (.single s3)))

/-- A nonzero word branches to the panic call boundary without RAM writes. -/
theorem unavailable (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000614) (he : Memory.Block B (c.get 23) 14)
    (ha : (c.get 23).toNat % 4 = 0) (hb : ramRead ram (c.get 23) .w ≠ 0#32) :
    DetSteps B img 2 ⟨c,ram⟩ ⟨c.wr 10 (ramRead ram (c.get 23) .w) 0x80000766,ram⟩ := by
  let eng := c.get 23
  let v := ramRead ram eng .w
  let c1 := c.wr 10 v 0x80000618
  have hr : B.inRam eng 4 = true := by
    simpa using Memory.block_access (B := B) (p := eng) (n := 14) (off := 0) (width := 4) he (by decide) (by decide)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact ac2147485204) fun o => ?_
    rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .w) (a := eng) o ha hr,hp]
    rfl
  apply DetSteps.step s0
  apply DetSteps.single
  refine detStep_of (by change (0x80000618 : Word).getLsbD 0 = false;decide) ac2147485208 fun o => ?_
  have hv : c1.get 10 = v := by simp [c1,Core.wr_get]
  rw [exec_branch,hv,Core.get_zero]
  have hb' : v ≠ 0#32 := hb
  have ht : taken .ne v 0 = true := by simp [taken,hb']
  rw [ht]
  simp only [ite_true]
  change interp B img o (jump c1 0x80000766) ram 0 [] = _
  rw [jump_ok c1 _ (by decide)]
  rfl


/-- Typed caller layout before acquisition. The normalized PC only reuses
    the existing layout predicate; no acquired word is assumed. -/
structure Pre (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) : Prop where
  pc : c.pc = 0x80000614
  layout : ShellCall.Pre B (c.goto 0x80000622) ram p admin s cmd
  engineRam : Memory.Block B (c.get 23) 14
  engineAlign : (c.get 23).toNat % 4 = 0
  engineSep : Engine.Separate (c.get 23) p
  available : ramRead ram (c.get 23) .w = 0#32

theorem establishes_pre (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (h : Pre B c ram p admin s cmd) :
    Engine.Pre B (acquired c) (result ram (c.get 23)) p admin s cmd := by
  have hf : ∀ i : Fin 128, result ram (c.get 23) (p+BitVec.ofNat 32 i.val) = ram (p+BitVec.ofNat 32 i.val) := by
    intro i
    apply frame
    intro j
    exact Ne.symm (h.engineSep ⟨j.val,by have := j.isLt;omega⟩ i)
  have hg : ∀ r : Reg, r ≠ 10 → (acquired c).get r = c.get r := by
    intro r hr
    simp [acquired,Core.wr_get_ne,hr]
  have hget : (acquired c).get 23 = c.get 23 := hg 23 (by decide)
  refine ⟨?_,by simpa only [hget] using h.engineRam,by simpa only [hget] using h.engineAlign,
    by simpa only [hget] using h.engineSep,?_⟩
  · refine ⟨rfl,?_,h.layout.arena,h.layout.align,?_,?_,?_,?_,?_,?_⟩
    · simpa only [hg 2 (by decide),Core.goto_get] using h.layout.sp
    · simpa only [hget,Core.goto_get] using h.layout.stateRam
    · simpa only [hget,Core.goto_get] using h.layout.stateAlign
    · rw [hget]
      exact snapshot ram (c.get 23) s h.layout.stateAt
    · rw [hf ⟨89,by decide⟩]
      exact h.layout.actorAt
    · apply Encoding.command_preserve ram _ (p+90#32) cmd h.layout.commandAt
      intro i
      have hi := i.isLt
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hf ⟨90+i.val,by omega⟩
    · simpa only [hget,Core.goto_get] using h.layout.stateSep
  · rw [hget]
    exact ramRead_ramWrite_w ram (c.get 23) 0xffffffff#32

/-- Acquisition through actual committed state/reply for every typed command. -/
theorem contract_full (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (h : Pre B c ram p admin s cmd) :
    ∃ n d r, n ≤ 175 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      Engine.Post c d ram r p s (Spec.transition admin s cmd) ∧ Engine.TopSame p ram r := by
  have hr := available B c ram h.pc h.engineRam h.engineAlign h.available
  obtain ⟨n,d,r,hn,hr',hp,htop⟩ := Engine.contract_full B (acquired c) (result ram (c.get 23)) p admin s cmd
    (establishes_pre B c ram p admin s cmd h)
  have htop' : Engine.TopSame p ram r := by
    intro k
    rw [htop k]
    apply frame
    intro i
    exact Ne.symm (h.engineSep ⟨i.val,by have := i.isLt;omega⟩ ⟨124+k.val,by have := k.isLt;omega⟩)
  refine ⟨4+n,d,r,by omega,hr.trans hr',?_,htop'⟩
  have heng : (acquired c).get 23 = c.get 23 := by simp [acquired,Core.wr_get_ne]
  have hsp : (acquired c).get 2 = c.get 2 := by simp [acquired,Core.wr_get_ne]
  refine ⟨hp.pc,hp.sp.trans hsp,by simpa only [heng] using hp.statePtr,
    hp.enginePtr.trans heng,hp.csr.trans (by rfl),by simpa only [heng] using hp.state,
    by simpa only [heng] using hp.released,hp.reply,?_⟩
  intro x hxa hxe
  rw [hp.frame x hxa (by simpa only [heng] using hxe)]
  apply frame
  intro i
  exact hxe ⟨i.val,by have := i.isLt;omega⟩

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (h : Pre B c ram p admin s cmd) :
    ∃ n d r, n ≤ 175 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      Engine.Post c d ram r p s (Spec.transition admin s cmd) := by
  obtain ⟨n,d,r,hn,hr,hp,_⟩ := contract_full B c ram p admin s cmd h
  exact ⟨n,d,r,hn,hr,hp⟩

theorem contract_inv (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (h : Pre B c ram p admin s cmd)
    (hi : Spec.Inv s) :
    ∃ n d r, n ≤ 175 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      Engine.Post c d ram r p s (Spec.transition admin s cmd) ∧ Engine.InvariantAt r (c.get 23) := by
  obtain ⟨n,d,r,hn,hr,hp⟩ := contract B c ram p admin s cmd h
  exact ⟨n,d,r,hn,hr,hp,_,hp.state,Spec.commit_inv admin s cmd hi⟩
end E5R.Thermostat.Acquire
