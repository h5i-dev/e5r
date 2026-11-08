import Projects.thermostat.WireCaller
import Projects.thermostat.Acquire
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.DecodedEngine
open E5R E5R.Thermostat

/-- Live handler objects before unpacking the decoder result. There is no
    CommandAt or acquired borrow assumption. Authentication remains upstream. -/
structure Pre (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) : Prop where
  pc : c.pc = 0x800005f4#32
  sp : c.get 2 = p+80#32
  arena : Memory.Block B p 128
  align : p.toNat%4 = 0
  engineRam : Memory.Block B (c.get 23) 14
  engineAlign : (c.get 23).toNat%4 = 0
  engineSep : Engine.Separate (c.get 23) p
  state : Encoding.SnapshotAt ram (c.get 23+4#32) s
  actor : ram (p+89#32) = Encoding.boolByte admin
  borrow : ramRead ram (c.get 23) .w = 0#32

theorem establishes_pre (B : Board) (c d : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (h : Pre B c ram p admin s)
    (hp : d.pc = 0x80000614#32)
    (hc : Encoding.CommandAt (WireCallerBytes.memory ram (p+80#32) (c.get 10)) ((p+80#32)+10#32) cmd)
    (hr : ∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 20 → d.get r = c.get r) :
    Acquire.Pre B d (WireCallerBytes.memory ram (p+80#32) (c.get 10)) p admin s cmd := by
  let mem := WireCallerBytes.memory ram (p+80#32) (c.get 10)
  have ptr : (p+80#32)+10#32 = p+90#32 := by rw [BitVec.add_assoc];rfl
  have h23 : d.get 23 = c.get 23 := hr 23 (by decide) (by decide) (by decide)
  have h2 : d.get 2 = p+80#32 := (hr 2 (by decide) (by decide) (by decide)).trans h.sp
  have frame (x : Word) (hx : ∀ i : Fin 4, x ≠ (p+90#32)+BitVec.ofNat 32 i.val) : mem x = ram x := by
    apply WireCallerBytes.frame
    simpa only [ptr] using hx
  have engineFrame (i : Fin 14) : mem (c.get 23+BitVec.ofNat 32 i.val) = ram (c.get 23+BitVec.ofNat 32 i.val) := by
    apply frame
    intro j
    have he := h.engineSep i ⟨90+j.val,by have := j.isLt;omega⟩
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using he
  have state : Encoding.SnapshotAt mem (c.get 23+4#32) s := by
    intro i
    have hi := engineFrame ⟨4+i.val,by have := i.isLt;omega⟩
    have hp : (c.get 23+4#32)+BitVec.ofNat 32 i.val = c.get 23+BitVec.ofNat 32 (4+i.val) := by
      rw [BitVec.add_assoc,←BitVec.ofNat_add]
    rw [hp,hi];simpa only [hp] using h.state i
  have actor : mem (p+89#32) = Encoding.boolByte admin := by
    rw [frame _ (by
      intro j
      have hj := j.isLt
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using ShellCall.offset_ne p 89 (90+j.val) (by decide) (by omega) (by omega))]
    exact h.actor
  have borrow : ramRead mem (c.get 23) .w = 0#32 := by
    have he : ramRead mem (c.get 23) .w = ramRead ram (c.get 23) .w := by
      apply ramRead_w_congr
      intro k hk;exact engineFrame ⟨k,by omega⟩
    exact he.trans h.borrow
  refine ⟨hp,?_,by simpa only [h23] using h.engineRam,by simpa only [h23] using h.engineAlign,
    by simpa only [h23] using h.engineSep,by simpa only [h23] using borrow⟩
  refine ⟨rfl,h2,h.arena,h.align,?_,?_,?_,actor,?_,?_⟩
  · simpa only [Core.goto_get,h23] using Memory.sub_block (off := 4) (m := 10) h.engineRam (by decide) (by decide)
  · rw [Core.goto_get,h23];exact Memory.half_aligned _ 2 (by have := h.engineAlign;omega)
  · simpa only [Core.goto_get,h23] using state
  · simpa only [ptr] using hc
  · intro i j
    rw [Core.goto_get,h23]
    have he := h.engineSep ⟨4+i.val,by have := i.isLt;omega⟩ j
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using he

theorem contract_full_inv (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (h : Pre B c ram p admin s)
    (hc : WireSpec.CommandWord (c.get 10) cmd) (hi : Spec.Inv s) :
    ∃ a n d r, n ≤ 183 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      Engine.Post a d (WireCallerBytes.memory ram (p+80#32) (c.get 10)) r p s (Spec.transition admin s cmd) ∧
      Engine.InvariantAt r (c.get 23) ∧
      (∀ reg : Reg, reg ≠ 11 → reg ≠ 12 → reg ≠ 20 → a.get reg = c.get reg) ∧ a.sameCsr c := by
  have hm : Memory.Block B (p+80#32) 16 := Memory.sub_block h.arena (by decide) (by decide)
  have ha : (p+80#32).toNat%2 = 0 := Memory.half_aligned p 40 (by have := h.align;omega)
  obtain ⟨a,ht,hpc,hcommand,hregs,hcsr⟩ := WireCaller.ok B c ram (p+80#32) cmd h.pc h.sp hc hm ha
  have pre := establishes_pre B c a ram p admin s cmd h hpc hcommand hregs
  obtain ⟨n,d,r,hn,td,hpost,hinv⟩ := Acquire.contract_inv B a (WireCallerBytes.memory ram (p+80#32) (c.get 10)) p admin s cmd pre hi
  have heng : a.get 23 = c.get 23 := hregs 23 (by decide) (by decide) (by decide)
  refine ⟨a,8+n,d,r,by omega,ht.trans td,hpost,?_,hregs,hcsr⟩
  simpa only [heng] using hinv

theorem contract_inv (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (h : Pre B c ram p admin s)
    (hc : WireSpec.CommandWord (c.get 10) cmd) (hi : Spec.Inv s) :
    ∃ a n d r, n ≤ 183 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      Engine.Post a d (WireCallerBytes.memory ram (p+80#32) (c.get 10)) r p s (Spec.transition admin s cmd) ∧
      Engine.InvariantAt r (c.get 23) := by
  obtain ⟨a,n,d,r,hn,ht,hpost,hinv,_,_⟩ := contract_full_inv B c ram p admin s cmd h hc hi
  exact ⟨a,n,d,r,hn,ht,hpost,hinv⟩
end E5R.Thermostat.DecodedEngine
