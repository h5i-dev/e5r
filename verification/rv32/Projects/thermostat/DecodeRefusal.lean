import Projects.thermostat.RequestPrepare
import Projects.thermostat.WireReject
import Projects.thermostat.RefusalEntry
import Projects.thermostat.StatusReturn
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.DecodeRefusal
open E5R E5R.Thermostat

theorem contract_inv (B : Board) (c : Core) (ram : Word → BitVec 8) (p req eng rawPtr pathPtr bodyPtr out f : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) (status : Nat)
    (h : TxnInput.Pre B c ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (h8 : c.get 8 = f) (h9 : c.get 9 = out)
    (hquery : ReadBytes.Span B img ram 0x80005b68#32 (WireSpec.ascii "authorization"))
    (hprefix : ReadBytes.Span B img ram 0x80005b75#32 (WireSpec.ascii "Bearer "))
    (hkeybytes : ReadBytes.Span B img ram 0x80005b7c#32 (WireSpec.ascii "dev-key"))
    (hallow : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = true)
    (hdecode : WireSpec.decode path body first = .error status)
    (hi : Spec.Inv s)
    (ho : Memory.Block B out 15) (hoa : out.toNat%4 = 0) (hf : Memory.Block B f 41)
    (hst : Memory.Block B (p+80#32) 96)
    (hso : WordRegions.Disjoint (p+80#32) 96 out 15) (hsf : WordRegions.Disjoint (p+80#32) 96 f 41)
    (hof : WordRegions.Disjoint out 15 f 41)
    (heo : WordRegions.Disjoint eng 25 out 15) (hef : WordRegions.Disjoint eng 25 f 41) :
    ∃ d n r, n ≤ 212*entries.length+18*body.length+483 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      d.pc = ramRead ram ((p+80#32)+92#32) .w &&& ~~~1 ∧ d.get 2 = (p+80#32)+96#32 ∧ d.sameCsr c ∧
      OuterReturn.Restored c d ram ∧ StatusMemory.At r out (BitVec.ofNat 32 status) ∧
      Encoding.SnapshotAt r (eng+4#32) s ∧ ramRead r eng .w = 0#32 ∧ Engine.InvariantAt r eng ∧ r (f+36#32) = 1#8 ∧ r (f+40#32) = 1#8 := by
  let value := HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries
  let bram := TxnScratch.memory ram (p+80#32) value admin
  obtain ⟨b,n,hn,ta,hwire,hlayout,b1,bsp,hb23,bcsr,b8,b9,b22⟩ := RequestPrepare.prepare B c ram p req eng rawPtr pathPtr bodyPtr
    raw path body entries first admin s h hquery hprefix hkeybytes hallow
  let aram := DecodeSave.memory bram (p+64#32) b
  obtain ⟨k,a,hk,tw,apc,astatus,asnap,aborrow,asp',a8',a9',a22',a23',acsr'⟩ :=
    WireReject.rejected B b bram p req pathPtr bodyPtr path body first admin s status hwire hlayout b1 hdecode
  have a8 : a.get 8 = f := (a8'.trans b8).trans h8
  have a9 : a.get 9 = out := (a9'.trans b9).trans h9
  have a22 : a.get 22 = 1#32 := a22'.trans b22
  have a20 : a.get 20 = BitVec.ofNat 32 status := by rw [←astatus];simp
  have asp : a.get 2 = p+80#32 := (asp'.trans bsp).trans h.sp
  have b23 : b.get 23 = eng := hb23.trans h.engine
  have acsr : a.sameCsr c := acsr'.trans bcsr
  obtain ⟨z,tz,zpc,z10,z18,zframe,zcsr⟩ := RefusalEntry.present B a aram apc
  have z8 : z.get 8 = f := (zframe 8 (by decide) (by decide)).trans a8
  have z9 : z.get 9 = out := (zframe 9 (by decide) (by decide)).trans a9
  have z20 : z.get 20 = BitVec.ofNat 32 status := (zframe 20 (by decide) (by decide)).trans a20
  have z22 : z.get 22 = 1#32 := (zframe 22 (by decide) (by decide)).trans a22
  have zsp : z.get 2 = p+80#32 := (zframe 2 (by decide) (by decide)).trans asp
  obtain ⟨d,td,dpc,dsp,dcsr,dsaved,dresponse,dflag36,dflag40⟩ := StatusReturn.contract B z aram out f (BitVec.ofNat 32 status)
    zpc z8 z9 z10 z18 z20 z22 ho hoa hf
    (by simpa only [zsp] using hst) (by simpa only [zsp] using Memory.word_aligned p 20 h.aligned)
    (by simpa only [zsp] using hso) (by simpa only [zsp] using hsf) hof
  have hstack (off : Nat) (ho : 44 ≤ off) (hb : off+4 ≤ 96) :
      ramRead aram (z.get 2+BitVec.ofNat 32 off) .w = ramRead ram (c.get 2+BitVec.ofNat 32 off) .w := by
    rw [zsp,h.sp]
    apply ramRead_w_congr
    intro i hi
    change DecodeSave.memory bram (p+64#32) b (((p+80#32)+BitVec.ofNat 32 off)+BitVec.ofNat 32 i) = _
    rw [DecodeSave.frame bram (p+64#32) b _ (by
      intro j
      have hj := j.isLt
      have hh := Bytes.offset_ne p (80+off+i) (64+j.val) (by omega) (by omega) (by omega)
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hh)]
    apply TxnScratch.frame
    · have hh := Bytes.offset_ne (p+80#32) (off+i) 9 (by omega) (by decide) (by omega)
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hh
    · have hh := Bytes.offset_ne (p+80#32) (off+i) 24 (by omega) (by decide) (by omega)
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hh
  let final := StatusResponse.memory aram out f (BitVec.ofNat 32 status)
  have he : ViewFrame.Region aram final eng 25 := by
    intro i
    exact StatusMemory.frame aram out f (BitVec.ofNat 32 status) _ (heo i) (hef i)
  have hs0 : Encoding.SnapshotAt aram (eng+4#32) s := by simpa only [b23] using asnap
  have hs := ViewFrame.snapshot hs0 he
  have hw : ramRead final eng .w = 0#32 := by
    have hh := ViewFrame.word he 0 (by decide)
    simp only [BitVec.add_zero] at hh
    exact hh.trans (by simpa only [b23] using aborrow)
  refine ⟨d,n+k+26,final,by omega,((ta.trans tw).trans tz).trans td,?_,by simpa only [zsp] using dsp,
    (dcsr.trans zcsr).trans acsr,?_,dresponse,hs,hw,⟨s,hs,hi⟩,dflag36,dflag40⟩
  · rw [dpc,hstack 92 (by decide) (by decide),h.sp]
  · constructor
    · exact dsaved.x1 |>.trans (hstack 92 (by decide) (by decide))
    · exact dsaved.x8 |>.trans (hstack 88 (by decide) (by decide))
    · exact dsaved.x9 |>.trans (hstack 84 (by decide) (by decide))
    · exact dsaved.x18 |>.trans (hstack 80 (by decide) (by decide))
    · exact dsaved.x19 |>.trans (hstack 76 (by decide) (by decide))
    · exact dsaved.x20 |>.trans (hstack 72 (by decide) (by decide))
    · exact dsaved.x21 |>.trans (hstack 68 (by decide) (by decide))
    · exact dsaved.x22 |>.trans (hstack 64 (by decide) (by decide))
    · exact dsaved.x23 |>.trans (hstack 60 (by decide) (by decide))
    · exact dsaved.x24 |>.trans (hstack 56 (by decide) (by decide))
    · exact dsaved.x25 |>.trans (hstack 52 (by decide) (by decide))
    · exact dsaved.x26 |>.trans (hstack 48 (by decide) (by decide))
    · exact dsaved.x27 |>.trans (hstack 44 (by decide) (by decide))
end E5R.Thermostat.DecodeRefusal
