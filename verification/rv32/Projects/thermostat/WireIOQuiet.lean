-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.WireIO
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.DecodedIOQuiet
import Projects.thermostat.WireQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.WireTight
theorem contract_io_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p req pathPtr bodyPtr : Word)
    (path body : List (BitVec 8)) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command)
    (hwire : Wire.Pre B c ram (p+64#32) req pathPtr bodyPtr path body first)
    (hlayout : DecodedEngine.Pre B (c.goto 0x800005f4#32) ram p admin s)
    (hra : c.get 1 = 0x800005f4#32) (hdecode : WireSpec.decode path body first = .ok cmd) (hi : Spec.Inv s) :
    ∃ n d r, n ≤ 18*body.length+486 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      Engine.Post c d ram r p s (Spec.transition admin s cmd) ∧ Engine.InvariantAt r (c.get 23) ∧ Engine.TopSame p ram r ∧ BufferRegs.Frame c d ∧
      (∀ err, Spec.transition admin s cmd = .error err → d.get 10 = BitVec.ofNat 32 (Errors.code err).toNat) := by
  obtain ⟨a,n,hn,ht,hpost⟩ := E5R.Thermostat.Wire.contract_quiet B c ram (p+64#32) req pathPtr bodyPtr path body first hwire
  have hlayout' := WireEngine.layout B c a ram p path body first admin s hlayout hra hpost
  have hc : WireSpec.CommandWord (a.get 10) cmd := by
    have hh := hpost.result;rw [hdecode] at hh;exact hh
  obtain ⟨b,k,d,r,hk,td,hengine,hinv,bframe,bcsr,htop,hbuf,herr⟩ := E5R.Thermostat.DecodedTight.contract_io_quiet B a (DecodeSave.memory ram (p+64#32) c)
    p admin s cmd hlayout' hc hi
  have ha23 : a.get 23 = c.get 23 := hpost.frame 23 (by decide)
  have hb23 : b.get 23 = a.get 23 := bframe 23 (by decide) (by decide) (by decide)
  have hb2 : b.get 2 = c.get 2 := (bframe 2 (by decide) (by decide) (by decide)).trans hpost.sp
  refine ⟨n+k,d,r,by omega,ht.trans td,?_,by simpa only [ha23] using hinv,?_,?_,herr⟩
  · refine ⟨hengine.pc,?_,?_,?_,?_,?_,?_,hengine.reply,?_⟩
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
  · intro k
    rw [htop k]
    apply DecodeSave.frame
    intro i
    have hi := i.isLt
    have hk := k.isLt
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using
      ShellCall.offset_ne p (124+k.val) (64+i.val) (by omega) (by omega) (by omega)


  · constructor
    · exact hbuf.capacity |>.trans (hpost.frame 18 (by decide))
    · exact hbuf.pointer |>.trans (hpost.frame 19 (by decide))
    · exact hbuf.future |>.trans (hpost.s0)
    · exact hbuf.response |>.trans (hpost.s1)
    · exact hbuf.completion |>.trans (hpost.frame 22 (by decide))

end E5R.Thermostat.WireTight
