import Projects.thermostat.TxnInput
import Projects.thermostat.WriteEntry
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.RequestTransaction
open E5R E5R.Thermostat

theorem authorized_pc (v : Option (List (BitVec 8))) (h : AuthSpec.authorized v (WireSpec.ascii "dev-key") = true) :
    RequestAuth.endPc v = 0x800005e2#32 := by
  cases v with
  | none => change false = true at h;cases h
  | some header => simp only [RequestAuth.endPc,h,ite_true]

/-- Actual Request authentication through principal extraction, decoder call,
    typed-byte derivation, acquisition and committed engine transaction. -/
theorem prepare (B : Board) (c : Core) (ram : Word → BitVec 8) (p req eng rawPtr pathPtr bodyPtr : Word)
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
      b.get 1 = 0x800005f4#32 ∧ b.get 2 = c.get 2 ∧ b.get 23 = c.get 23 ∧ b.sameCsr c := by
  let value := HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries
  let aram := RequestAuth.memory ram (p+80#32) value
  let bram := TxnScratch.memory ram (p+80#32) value admin
  have hsp25 : Memory.Block B (p+80#32) 25 := Memory.sub_block h.arena (by decide) (by decide)
  have hsp10 : Memory.Block B (p+80#32) 10 := Memory.sub_block h.arena (by decide) (by decide)
  have happ24 : Memory.Block B eng 24 := by simpa only [BitVec.add_zero] using Memory.sub_block (off := 0) (m := 24) h.app (by decide) (by decide)
  obtain ⟨a,n,hn,ta,apc,_,_,aframe,acsr⟩ := RequestAuth.contract B c ram req rawPtr eng (p+80#32) raw entries
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
  exact ⟨b,n+5,by omega,ta.trans tb,hwire,hlayout,b1,bsp.trans h.sp.symm,hb23,bcsr.trans acsr⟩

theorem contract_inv (B : Board) (c : Core) (ram : Word → BitVec 8) (p req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command)
    (h : TxnInput.Pre B c ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hquery : ReadBytes.Span B img ram 0x80005b68#32 (WireSpec.ascii "authorization"))
    (hprefix : ReadBytes.Span B img ram 0x80005b75#32 (WireSpec.ascii "Bearer "))
    (hkeybytes : ReadBytes.Span B img ram 0x80005b7c#32 (WireSpec.ascii "dev-key"))
    (hallow : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = true)
    (hdecode : WireSpec.decode path body first = .ok cmd) (hi : Spec.Inv s) :
    ∃ n d r, n ≤ 212*entries.length+18*body.length+636 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      Engine.Post c d ram r p s (Spec.transition admin s cmd) ∧ Engine.InvariantAt r (c.get 23) := by
  let value := HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries
  let bram := TxnScratch.memory ram (p+80#32) value admin
  obtain ⟨b,n,hn,ta,hwire,hlayout,b1,bsp,hb23,bcsr⟩ := prepare B c ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s h hquery hprefix hkeybytes hallow
  obtain ⟨k,d,r,hk,td,hpost,hinv⟩ := WireEngine.contract_inv B b bram p req pathPtr bodyPtr path body first admin s cmd hwire hlayout b1 hdecode hi
  refine ⟨n+k,d,r,by omega,ta.trans td,?_,by simpa only [hb23] using hinv⟩
  refine ⟨hpost.pc,hpost.sp.trans bsp,?_,?_,hpost.csr.trans bcsr,?_,?_,hpost.reply,?_⟩
  · simpa only [hb23] using hpost.statePtr
  · exact hpost.enginePtr.trans hb23
  · simpa only [hb23] using hpost.state
  · simpa only [hb23] using hpost.released
  · intro x hxa hxe
    rw [hpost.frame x hxa (by simpa only [hb23] using hxe)]
    exact TxnScratch.outside ram p x value admin hxa
/-- Refused credentials never enter the decoder or acquire the mutable borrow. -/
theorem auth_rejected (B : Board) (c : Core) (ram : Word → BitVec 8) (p req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot)
    (h : TxnInput.Pre B c ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hquery : ReadBytes.Span B img ram 0x80005b68#32 (WireSpec.ascii "authorization"))
    (hprefix : ReadBytes.Span B img ram 0x80005b75#32 (WireSpec.ascii "Bearer "))
    (hkeybytes : ReadBytes.Span B img ram 0x80005b7c#32 (WireSpec.ascii "dev-key"))
    (hdeny : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = false)
    (hi : Spec.Inv s) :
    ∃ d n, n ≤ 212*entries.length+145 ∧ DetSteps B img n ⟨c,ram⟩
      ⟨d,RequestAuth.memory ram (p+80#32) (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries)⟩ ∧
      (d.pc = 0x800005a8#32 ∨ d.pc = 0x800005a2#32) ∧ d.get 20 = 401#32 ∧
      Encoding.SnapshotAt (RequestAuth.memory ram (p+80#32) (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries)) (eng+4#32) s ∧
      ramRead (RequestAuth.memory ram (p+80#32) (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries)) eng .w = 0#32 ∧
      Engine.InvariantAt (RequestAuth.memory ram (p+80#32) (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries)) eng := by
  let value := HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries
  have happ24 : Memory.Block B eng 24 := by simpa only [BitVec.add_zero] using Memory.sub_block (off := 0) (m := 24) h.app (by decide) (by decide)
  obtain ⟨d,n,hn,td,dpc,d20,_,_,_⟩ := RequestAuth.contract B c ram req rawPtr eng (p+80#32) raw entries
    h.headers hquery hprefix hkeybytes h.pc h.request h.engine h.sp happ24 h.appAligned
    (Memory.sub_block h.arena (by decide) (by decide)) h.keyLength h.keyPointer
  have hr := TxnScratch.auth_region ram p eng 25 value h.appSeparate
  have hs := ViewFrame.snapshot h.state hr
  have hw : ramRead (RequestAuth.memory ram (p+80#32) value) eng .w = 0#32 := by
    have hh := ViewFrame.word hr 0 (by decide)
    simpa only [BitVec.add_zero,h.borrow] using hh
  refine ⟨d,n,hn,td,?_,d20,hs,hw,⟨s,hs,hi⟩⟩
  cases hv : value with
  | none => exact Or.inl (by simpa only [show HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries = value from rfl,hv,RequestAuth.endPc] using dpc)
  | some header =>
    have hd : AuthSpec.authorized (some header) (WireSpec.ascii "dev-key") = false := by simpa only [show HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries = value from rfl,hv] using hdeny
    exact Or.inr (by simpa only [show HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries = value from rfl,hv,RequestAuth.endPc,hd,Bool.false_eq_true,ite_false] using dpc)

/-- Authenticated requests rejected by the byte decoder preserve state and the free borrow. -/
theorem decode_rejected (B : Board) (c : Core) (ram : Word → BitVec 8) (p req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) (status : Nat)
    (h : TxnInput.Pre B c ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hquery : ReadBytes.Span B img ram 0x80005b68#32 (WireSpec.ascii "authorization"))
    (hprefix : ReadBytes.Span B img ram 0x80005b75#32 (WireSpec.ascii "Bearer "))
    (hkeybytes : ReadBytes.Span B img ram 0x80005b7c#32 (WireSpec.ascii "dev-key"))
    (hallow : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = true)
    (hdecode : WireSpec.decode path body first = .error status) (hi : Spec.Inv s) :
    ∃ n d r, n ≤ 212*entries.length+18*body.length+457 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      d.pc = 0x800005a2#32 ∧ (d.get 20).toNat = status ∧ Encoding.SnapshotAt r (eng+4#32) s ∧
      ramRead r eng .w = 0#32 ∧ Engine.InvariantAt r eng := by
  let value := HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries
  let bram := TxnScratch.memory ram (p+80#32) value admin
  obtain ⟨b,n,hn,ta,hwire,hlayout,b1,_,hb23,_⟩ := prepare B c ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s h hquery hprefix hkeybytes hallow
  obtain ⟨k,d,hk,td,dpc,dstatus,ds,db⟩ := WireEngine.rejected B b bram p req pathPtr bodyPtr path body first admin s status hwire hlayout b1 hdecode
  have b23 : b.get 23 = eng := hb23.trans h.engine
  have hs : Encoding.SnapshotAt (DecodeSave.memory bram (p+64#32) b) (eng+4#32) s := by simpa only [b23] using ds
  refine ⟨n+k,d,DecodeSave.memory bram (p+64#32) b,by omega,ta.trans td,dpc,dstatus,hs,?_,⟨s,hs,hi⟩⟩
  simpa only [b23] using db
end E5R.Thermostat.RequestTransaction
