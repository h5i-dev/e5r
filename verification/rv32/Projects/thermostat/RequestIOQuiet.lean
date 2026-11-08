-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.RequestIO
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.RequestPrepareIOQuiet
import Projects.thermostat.WireIOQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.RequestTight
theorem contract_io_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command)
    (h : TxnInput.Pre B c ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hquery : ReadBytes.Span B img ram 0x80005b68#32 (WireSpec.ascii "authorization"))
    (hprefix : ReadBytes.Span B img ram 0x80005b75#32 (WireSpec.ascii "Bearer "))
    (hkeybytes : ReadBytes.Span B img ram 0x80005b7c#32 (WireSpec.ascii "dev-key"))
    (hallow : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = true)
    (hdecode : WireSpec.decode path body first = .ok cmd) (hi : Spec.Inv s) :
    ∃ n d r, n ≤ 212*entries.length+18*body.length+636 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      Engine.Post c d ram r p s (Spec.transition admin s cmd) ∧ Engine.InvariantAt r (c.get 23) ∧ Engine.TopSame p ram r ∧ BufferRegs.Ready c d ∧
      (∀ err, Spec.transition admin s cmd = .error err → d.get 10 = BitVec.ofNat 32 (Errors.code err).toNat) := by
  let value := HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries
  let bram := TxnScratch.memory ram (p+80#32) value admin
  obtain ⟨b,n,hn,ta,hwire,hlayout,b1,bsp,hb23,bcsr,hready⟩ := E5R.Thermostat.RequestTransaction.prepare_io_quiet B c ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s h hquery hprefix hkeybytes hallow
  obtain ⟨k,d,r,hk,td,hpost,hinv,htop,hbuf,herr⟩ := E5R.Thermostat.WireTight.contract_io_quiet B b bram p req pathPtr bodyPtr path body first admin s cmd hwire hlayout b1 hdecode hi
  refine ⟨n+k,d,r,by omega,ta.trans td,?_,by simpa only [hb23] using hinv,?_,hready.trans hbuf,herr⟩
  · refine ⟨hpost.pc,hpost.sp.trans bsp,?_,?_,hpost.csr.trans bcsr,?_,?_,hpost.reply,?_⟩
    · simpa only [hb23] using hpost.statePtr
    · exact hpost.enginePtr.trans hb23
    · simpa only [hb23] using hpost.state
    · simpa only [hb23] using hpost.released
    · intro x hxa hxe
      rw [hpost.frame x hxa (by simpa only [hb23] using hxe)]
      exact TxnScratch.outside ram p x value admin hxa
  · intro k
    rw [htop k]
    apply TxnScratch.frame
    · have hk := k.isLt
      have hp : (p+80#32)+9#32 = p+89#32 := by rw [BitVec.add_assoc];rfl
      rw [hp]
      exact ShellCall.offset_ne p (124+k.val) 89 (by omega) (by decide) (by omega)
    · have hk := k.isLt
      have hp : (p+80#32)+24#32 = p+104#32 := by rw [BitVec.add_assoc];rfl
      rw [hp]
      exact ShellCall.offset_ne p (124+k.val) 104 (by omega) (by decide) (by omega)

end E5R.Thermostat.RequestTight
