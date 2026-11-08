import Projects.thermostat.Wire
import Projects.thermostat.DecodedEngine
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.WireEngine
open E5R E5R.Thermostat

theorem layout (B : Board) (c d : Core) (ram : Word → BitVec 8) (p : Word)
    (path body : List (BitVec 8)) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot)
    (h : DecodedEngine.Pre B (c.goto 0x800005f4#32) ram p admin s)
    (hret : c.get 1 = 0x800005f4#32) (hd : Wire.Post c d path body first) :
    DecodedEngine.Pre B d (DecodeSave.memory ram (p+64#32) c) p admin s := by
  have h23 : d.get 23 = c.get 23 := hd.frame 23 (by decide)
  have engineFrame (i : Fin 14) :
      DecodeSave.memory ram (p+64#32) c (c.get 23+BitVec.ofNat 32 i.val) = ram (c.get 23+BitVec.ofNat 32 i.val) := by
    apply DecodeSave.frame
    intro j
    have hh := h.engineSep i ⟨64+j.val,by have := j.isLt;omega⟩
    simpa only [Core.goto_get,BitVec.ofNat_add,BitVec.add_assoc] using hh
  refine ⟨?_,?_,h.arena,h.align,?_,?_,?_,?_,?_,?_⟩
  · rw [hd.pc,hret];decide +kernel
  · exact hd.sp.trans h.sp
  · simpa only [h23,Core.goto_get] using h.engineRam
  · simpa only [h23,Core.goto_get] using h.engineAlign
  · simpa only [h23,Core.goto_get] using h.engineSep
  · rw [h23]
    intro i
    have hi := engineFrame ⟨4+i.val,by have := i.isLt;omega⟩
    have hp : (c.get 23+4#32)+BitVec.ofNat 32 i.val = c.get 23+BitVec.ofNat 32 (4+i.val) := by rw [BitVec.add_assoc,←BitVec.ofNat_add]
    rw [hp,hi];simpa only [Core.goto_get,hp] using h.state i
  · rw [DecodeSave.frame ram (p+64#32) c _ (by
      intro j
      have hj := j.isLt
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using ShellCall.offset_ne p 89 (64+j.val) (by decide) (by omega) (by omega))]
    exact h.actor
  · rw [h23]
    have he : ramRead (DecodeSave.memory ram (p+64#32) c) (c.get 23) .w = ramRead ram (c.get 23) .w := by
      apply ramRead_w_congr
      intro k hk;exact engineFrame ⟨k,by omega⟩
    exact he.trans h.borrow

theorem contract_inv (B : Board) (c : Core) (ram : Word → BitVec 8) (p req pathPtr bodyPtr : Word)
    (path body : List (BitVec 8)) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command)
    (hwire : Wire.Pre B c ram (p+64#32) req pathPtr bodyPtr path body first)
    (hlayout : DecodedEngine.Pre B (c.goto 0x800005f4#32) ram p admin s)
    (hra : c.get 1 = 0x800005f4#32) (hdecode : WireSpec.decode path body first = .ok cmd) (hi : Spec.Inv s) :
    ∃ n d r, n ≤ 18*body.length+486 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      Engine.Post c d ram r p s (Spec.transition admin s cmd) ∧ Engine.InvariantAt r (c.get 23) := by
  obtain ⟨a,n,hn,ht,hpost⟩ := Wire.contract B c ram (p+64#32) req pathPtr bodyPtr path body first hwire
  have hlayout' := layout B c a ram p path body first admin s hlayout hra hpost
  have hc : WireSpec.CommandWord (a.get 10) cmd := by
    have hh := hpost.result;rw [hdecode] at hh;exact hh
  obtain ⟨b,k,d,r,hk,td,hengine,hinv,bframe,bcsr⟩ := DecodedEngine.contract_full_inv B a (DecodeSave.memory ram (p+64#32) c)
    p admin s cmd hlayout' hc hi
  have ha23 : a.get 23 = c.get 23 := hpost.frame 23 (by decide)
  have hb23 : b.get 23 = a.get 23 := bframe 23 (by decide) (by decide) (by decide)
  have hb2 : b.get 2 = c.get 2 := (bframe 2 (by decide) (by decide) (by decide)).trans hpost.sp
  refine ⟨n+k,d,r,by omega,ht.trans td,?_,by simpa only [ha23] using hinv⟩
  refine ⟨hengine.pc,?_,?_,?_,?_,?_,?_,hengine.reply,?_⟩
  · exact hengine.sp.trans hb2
  · simpa only [hb23,ha23] using hengine.statePtr
  · simpa only [hb23,ha23] using hengine.enginePtr
  · exact (hengine.csr.trans bcsr).trans hpost.csr
  · simpa only [hb23,ha23] using hengine.state
  · simpa only [hb23,ha23] using hengine.released
  · intro x hxa hxe
    rw [hengine.frame x hxa (by simpa only [hb23,ha23] using hxe)]
    rw [WireCallerBytes.frame _ _ _ _ (by
      intro i
      have hi := i.isLt
      have he : (p+80#32)+10#32 = p+90#32 := by rw [BitVec.add_assoc];rfl
      simpa only [he,BitVec.ofNat_add,BitVec.add_assoc] using hxa ⟨90+i.val,by omega⟩)]
    apply DecodeSave.frame
    intro i
    have hi := i.isLt
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hxa ⟨64+i.val,by omega⟩

theorem rejected (B : Board) (c : Core) (ram : Word → BitVec 8) (p req pathPtr bodyPtr : Word)
    (path body : List (BitVec 8)) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) (status : Nat)
    (hwire : Wire.Pre B c ram (p+64#32) req pathPtr bodyPtr path body first)
    (hlayout : DecodedEngine.Pre B (c.goto 0x800005f4#32) ram p admin s)
    (hra : c.get 1 = 0x800005f4#32) (hdecode : WireSpec.decode path body first = .error status) :
    ∃ n d, n ≤ 18*body.length+307 ∧
      DetSteps B img n ⟨c,ram⟩ ⟨d,DecodeSave.memory ram (p+64#32) c⟩ ∧
      d.pc = 0x800005a2#32 ∧ (d.get 20).toNat = status ∧
      Encoding.SnapshotAt (DecodeSave.memory ram (p+64#32) c) (c.get 23+4#32) s ∧
      ramRead (DecodeSave.memory ram (p+64#32) c) (c.get 23) .w = 0#32 := by
  obtain ⟨a,n,hn,ht,hpost⟩ := Wire.contract B c ram (p+64#32) req pathPtr bodyPtr path body first hwire
  have hlayout' := layout B c a ram p path body first admin s hlayout hra hpost
  have he : WireSpec.ResultWord (a.get 10) (.error status) := by
    have hh := hpost.result;rw [hdecode] at hh;exact hh
  obtain ⟨d,td,hpc,hstatus,_,_⟩ := WireCaller.error B a (DecodeSave.memory ram (p+64#32) c) status hlayout'.pc he
  have h23 : a.get 23 = c.get 23 := hpost.frame 23 (by decide)
  exact ⟨n+4,d,by omega,ht.trans td,hpc,hstatus,by simpa only [h23] using hlayout'.state,
    by simpa only [h23] using hlayout'.borrow⟩

theorem closed_contract_inv (B : Board) (c : Core) (ram : Word → BitVec 8) (p req pathPtr bodyPtr : Word)
    (path body : List (BitVec 8)) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command)
    (hwire : Wire.Pre B c ram (p+64#32) req pathPtr bodyPtr path body first)
    (hlayout : DecodedEngine.Pre B (c.goto 0x800005f4#32) ram p admin s)
    (hra : c.get 1 = 0x800005f4#32) (hdecode : WireSpec.decode path body first = .ok cmd)
    (hi : Spec.Inv s) (hm : c.mie_ = false) :
    ∃ n d r, n ≤ 18*body.length+486 ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      Engine.Post c d ram r p s (Spec.transition admin s cmd) ∧ Engine.InvariantAt r (c.get 23) := by
  obtain ⟨n,d,r,hn,ht,hpost,hinv⟩ := contract_inv B c ram p req pathPtr bodyPtr path body first admin s cmd hwire hlayout hra hdecode hi
  exact ⟨n,d,r,hn,Interrupt.close ht hm,hpost,hinv⟩
end E5R.Thermostat.WireEngine
