import Projects.thermostat.RequestAuthEnd
import Projects.thermostat.RefusalEntry
import Projects.thermostat.StatusReturn
import Projects.thermostat.TxnInput
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.RequestRefusal
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp out f : Word) (value : Option (List (BitVec 8))) :=
  StatusResponse.memory (RequestAuth.memory ram sp value) out f 401#32

theorem end_branch {d : Core} {value : Option (List (BitVec 8))} (hp : d.pc = RequestAuth.endPc value)
    (hz : value = none → d.get 10 = 0#32)
    (hdeny : AuthSpec.authorized value (WireSpec.ascii "dev-key") = false) :
    d.pc = 0x800005a2#32 ∨ (d.pc = 0x800005a8#32 ∧ d.get 10 = 0#32) := by
  cases value with
  | none => exact Or.inr ⟨hp,hz rfl⟩
  | some xs =>
    exact Or.inl (by simpa only [RequestAuth.endPc,hdeny,Bool.false_eq_true,ite_false] using hp)

/-- Actual header lookup/authentication/refusal Response/handler RET, including
    absent headers and every rejected byte value. No decoder or engine is run. -/
theorem contract_inv (B : Board) (c : Core) (ram : Word → BitVec 8) (p req eng rawPtr pathPtr bodyPtr out f : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot)
    (h : TxnInput.Pre B c ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (h8 : c.get 8 = f) (h9 : c.get 9 = out)
    (hquery : ReadBytes.Span B img ram 0x80005b68#32 (WireSpec.ascii "authorization"))
    (hprefix : ReadBytes.Span B img ram 0x80005b75#32 (WireSpec.ascii "Bearer "))
    (hkeybytes : ReadBytes.Span B img ram 0x80005b7c#32 (WireSpec.ascii "dev-key"))
    (hdeny : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = false)
    (hi : Spec.Inv s)
    (ho : Memory.Block B out 15) (hoa : out.toNat%4 = 0) (hf : Memory.Block B f 41)
    (hst : Memory.Block B (p+80#32) 96)
    (hso : WordRegions.Disjoint (p+80#32) 96 out 15) (hsf : WordRegions.Disjoint (p+80#32) 96 f 41)
    (hof : WordRegions.Disjoint out 15 f 41)
    (heo : WordRegions.Disjoint eng 25 out 15) (hef : WordRegions.Disjoint eng 25 f 41) :
    ∃ d n, n ≤ 212*entries.length+171 ∧ DetSteps B img n ⟨c,ram⟩
      ⟨d,memory ram (p+80#32) out f (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries)⟩ ∧
      d.pc = ramRead ram ((p+80#32)+92#32) .w &&& ~~~1 ∧ d.get 2 = (p+80#32)+96#32 ∧ d.sameCsr c ∧
      OuterReturn.Restored c d ram ∧
      StatusMemory.At (memory ram (p+80#32) out f (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries)) out 401#32 ∧
      Encoding.SnapshotAt (memory ram (p+80#32) out f (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries)) (eng+4#32) s ∧
      ramRead (memory ram (p+80#32) out f (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries)) eng .w = 0#32 ∧
      Engine.InvariantAt (memory ram (p+80#32) out f (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries)) eng := by
  let value := HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries
  let aram := RequestAuth.memory ram (p+80#32) value
  have happ24 : Memory.Block B eng 24 := by simpa only [BitVec.add_zero] using Memory.sub_block (off := 0) (m := 24) h.app (by decide) (by decide)
  obtain ⟨a,n,hn,ta,apc,a20,a22,aframe,acsr,az⟩ := RequestAuthEnd.contract B c ram req rawPtr eng (p+80#32) raw entries
    h.headers hquery hprefix hkeybytes h.pc h.request h.engine h.sp happ24 h.appAligned
    (Memory.sub_block h.arena (by decide) (by decide)) h.keyLength h.keyPointer
  have a8 : a.get 8 = f := (aframe 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8
  have a9 : a.get 9 = out := (aframe 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h9
  have asp : a.get 2 = p+80#32 := (aframe 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.sp
  obtain ⟨z,k,hk,tz,zpc,z10,z18,zframe,zcsr⟩ := RefusalEntry.choose B a aram (end_branch apc az hdeny)
  have z8 : z.get 8 = f := (zframe 8 (by decide) (by decide)).trans a8
  have z9 : z.get 9 = out := (zframe 9 (by decide) (by decide)).trans a9
  have z20 : z.get 20 = 401#32 := (zframe 20 (by decide) (by decide)).trans a20
  have z22 : z.get 22 = 1#32 := (zframe 22 (by decide) (by decide)).trans a22
  have zsp : z.get 2 = p+80#32 := (zframe 2 (by decide) (by decide)).trans asp
  obtain ⟨d,td,dpc,dsp,dcsr,dsaved,dresponse,_,_⟩ := StatusReturn.contract B z aram out f 401#32
    zpc z8 z9 z10 z18 z20 z22 ho hoa hf
    (by simpa only [zsp] using hst) (by simpa only [zsp] using Memory.word_aligned p 20 h.aligned)
    (by simpa only [zsp] using hso) (by simpa only [zsp] using hsf) hof
  have hstack (off : Nat) (ho : 44 ≤ off) (hb : off+4 ≤ 96) :
      ramRead aram (z.get 2+BitVec.ofNat 32 off) .w = ramRead ram (c.get 2+BitVec.ofNat 32 off) .w := by
    rw [zsp,h.sp]
    apply ramRead_w_congr
    intro i hi
    apply RequestAuth.memory_frame
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact Bytes.offset_ne (p+80#32) (off+i) 24 (by omega) (by decide) (by omega)
  have he : ViewFrame.Region ram (memory ram (p+80#32) out f value) eng 25 := by
    intro i
    exact (StatusMemory.frame aram out f 401#32 _ (heo i) (hef i)).trans
      (TxnScratch.auth_region ram p eng 25 value h.appSeparate i)
  have hs := ViewFrame.snapshot h.state he
  have hw : ramRead (memory ram (p+80#32) out f value) eng .w = 0#32 := by
    have hh := ViewFrame.word he 0 (by decide)
    simpa only [BitVec.add_zero,h.borrow] using hh
  refine ⟨d,n+k+23,by omega,(ta.trans tz).trans td,?_,by simpa only [zsp] using dsp,
    (dcsr.trans zcsr).trans acsr,?_,dresponse,hs,hw,⟨s,hs,hi⟩⟩
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
end E5R.Thermostat.RequestRefusal
