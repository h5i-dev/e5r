import Projects.thermostat.RequestTransaction
import Projects.thermostat.BufferReady
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.RequestTransaction
open E5R E5R.Thermostat

theorem prepare_io (B : Board) (c : Core) (ram : Word → BitVec 8) (p req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot)
    (h : TxnInput.Pre B c ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hquery : ReadBytes.Span B img ram 0x80005b68#32 (WireSpec.ascii "authorization"))
    (hprefix : ReadBytes.Span B img ram 0x80005b75#32 (WireSpec.ascii "Bearer "))
    (hkeybytes : ReadBytes.Span B img ram 0x80005b7c#32 (WireSpec.ascii "dev-key"))
    (hallow : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = true)
 :
    ∃ b n, n ≤ 212*entries.length+150 ∧ DetSteps B img n ⟨c,ram⟩
      ⟨b,TxnScratch.memory ram (p+80#32) (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) admin⟩ ∧
      Wire.Pre B b (TxnScratch.memory ram (p+80#32) (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) admin)
        (p+64#32) req pathPtr bodyPtr path body first ∧
      DecodedEngine.Pre B (b.goto 0x800005f4#32)
        (TxnScratch.memory ram (p+80#32) (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) admin) p admin s ∧
      b.get 1 = 0x800005f4#32 ∧ b.get 2 = c.get 2 ∧ b.get 23 = c.get 23 ∧ b.sameCsr c ∧ BufferRegs.Ready c b := by
  let value := HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries
  let aram := RequestAuth.memory ram (p+80#32) value
  let bram := TxnScratch.memory ram (p+80#32) value admin
  have hsp25 : Memory.Block B (p+80#32) 25 := Memory.sub_block h.arena (by decide) (by decide)
  have hsp10 : Memory.Block B (p+80#32) 10 := Memory.sub_block h.arena (by decide) (by decide)
  have happ24 : Memory.Block B eng 24 := by simpa only [BitVec.add_zero] using Memory.sub_block (off := 0) (m := 24) h.app (by decide) (by decide)
  obtain ⟨a,n,hn,ta,apc,_,a22,aframe,acsr⟩ := RequestAuth.contract B c ram req rawPtr eng (p+80#32) raw entries
    h.headers hquery hprefix hkeybytes h.pc h.request h.engine h.sp happ24 h.appAligned hsp25 h.keyLength h.keyPointer
  have apc' : a.pc = 0x800005e2#32 := apc.trans (authorized_pc value hallow)
  have asp : a.get 2 = p+80#32 := (aframe 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.sp
  have a21 : a.get 21 = req := (aframe 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.request
  have a23 : a.get 23 = eng := (aframe 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.engine
  have haAdmin : aram (eng+24#32) = Encoding.boolByte admin := by
    have hr := TxnScratch.auth_region ram p eng 25 value h.appSeparate
    have hh := hr ⟨24,by decide⟩
    exact hh.trans h.principal
  obtain ⟨b,tb,bpc,b10,b1,bframe,bcsr⟩ := WriteEntry.contract B a aram eng (p+80#32) req admin apc' a23 asp a21 h.app hsp10 haAdmin
  have bsp : b.get 2 = p+80#32 := (bframe 2 (by decide) (by decide)).trans asp
  have b23 : b.get 23 = eng := (bframe 23 (by decide) (by decide)).trans a23
  have hb23 : b.get 23 = c.get 23 := b23.trans h.engine.symm
  have hwire := TxnInput.wire_pre B c b ram p req eng rawPtr pathPtr bodyPtr raw path body entries first value admin s h bpc bsp b10
  have hlayout := TxnInput.decoded_layout B c b ram p req eng rawPtr pathPtr bodyPtr raw path body entries first value admin s h bsp b23
  refine ⟨b,n+5,by omega,ta.trans tb,hwire,hlayout,b1,bsp.trans h.sp.symm,hb23,bcsr.trans acsr,?_⟩
  constructor
  · exact (bframe 18 (by decide) (by decide)).trans (aframe 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact (bframe 19 (by decide) (by decide)).trans (aframe 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact (bframe 8 (by decide) (by decide)).trans (aframe 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact (bframe 9 (by decide) (by decide)).trans (aframe 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact (bframe 22 (by decide) (by decide)).trans a22
end E5R.Thermostat.RequestTransaction
