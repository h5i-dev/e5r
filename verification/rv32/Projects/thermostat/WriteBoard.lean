import Projects.thermostat.WriteBody
import Projects.thermostat.AuthLiterals
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.WriteBoard
open E5R E5R.Thermostat

theorem contract_inv (c : Core) (ram : Word → BitVec 8) (p f response req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command)
    (h : WriteInput.Pre UartPlatform.board c ram p f response req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hallow : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = true)
    (hdecode : WireSpec.decode path body first = .ok cmd) (hi : Spec.Inv s)
 :
    ∃ n d r, n ≤ 212*entries.length+18*body.length+667 ∧ DetSteps UartPlatform.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      WriteBody.Post c d ram r p f eng s (Spec.transition admin s cmd) ∧ Engine.InvariantAt r eng := by
  exact WriteBody.contract_inv UartPlatform.board c ram p f response req eng rawPtr pathPtr bodyPtr
    raw path body entries first admin s cmd h hallow hdecode hi
    (AuthLiterals.header _) (AuthLiterals.bearer _) (AuthLiterals.key _)

theorem closed_contract_inv (c : Core) (ram : Word → BitVec 8) (p f response req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command)
    (h : WriteInput.Pre UartPlatform.board c ram p f response req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hallow : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = true)
    (hdecode : WireSpec.decode path body first = .ok cmd) (hi : Spec.Inv s) (hm : c.mie_ = false)
 :
    ∃ n d r, n ≤ 212*entries.length+18*body.length+667 ∧ Trace.Closed UartPlatform.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      WriteBody.Post c d ram r p f eng s (Spec.transition admin s cmd) ∧ Engine.InvariantAt r eng := by
  obtain ⟨n,d,r,hn,ht,hpost,hinv⟩ := contract_inv c ram p f response req eng rawPtr pathPtr bodyPtr raw path body entries first admin s cmd h hallow hdecode hi
  exact ⟨n,d,r,hn,Interrupt.close ht hm,hpost,hinv⟩
end E5R.Thermostat.WriteBoard
