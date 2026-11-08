-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.RequestAuth
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.BearerAuthQuiet
import Projects.thermostat.HeaderCallerQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.RequestAuth
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (req rawPtr eng sp : Word)
    (raw : List (BitVec 8)) (entries : List HeaderSpec.Entry) (h : Header.Pre B ram req rawPtr raw entries)
    (hquery : ReadBytes.Span B img ram 0x80005b68#32 (WireSpec.ascii "authorization"))
    (hprefix : ReadBytes.Span B img ram 0x80005b75#32 (WireSpec.ascii "Bearer "))
    (hkeybytes : ReadBytes.Span B img ram 0x80005b7c#32 (WireSpec.ascii "dev-key"))
    (hp : c.pc = 0x8000052e#32) (h21 : c.get 21 = req) (h23 : c.get 23 = eng) (hsp : c.get 2 = sp)
    (hm : Memory.Block B eng 24) (ha : eng.toNat%4 = 0) (hs : Memory.Block B sp 25)
    (hlen : ramRead ram (eng+20#32) .w = 7#32) (hkey : ramRead ram (eng+16#32) .w = 0x80005b7c#32) :
    ∃ d n, n ≤ 212*entries.length+145 ∧ Quiet.Steps B img n ⟨c,ram⟩
      ⟨d,memory ram sp (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries)⟩ ∧
      d.pc = endPc (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) ∧
      d.get 20 = 401#32 ∧ d.get 22 = 1#32 ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,n,hn,ta,apc,hresult,aframe,acsr⟩ := E5R.Thermostat.HeaderCaller.contract_quiet B c ram req rawPtr raw entries h hquery hp h21
  have asp : a.get 2 = sp := (aframe 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsp
  have a23 : a.get 23 = eng := (aframe 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h23
  cases hv : HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries with
  | none =>
    rw [hv] at hresult
    obtain ⟨d,k,hk,td,dpc,d20,d22,dframe,dcsr⟩ := E5R.Thermostat.BearerAuth.missing_quiet B a ram apc hresult
    refine ⟨d,n+k,by omega,?_,by simpa only [hv,endPc] using dpc,d20,d22,?_,dcsr.trans acsr⟩
    · simpa only [hv,memory] using ta.trans td
    · intro r h1 h5 h6 h7 h20 h22 h24 h25 h28 h29 hr
      exact (dframe r h1 h20 h22 h24 h25 (by omega)).trans (aframe r h1 h5 h6 h7 h28 h29 hr)
  | some header =>
    rw [hv] at hresult
    obtain ⟨nonzero,alen,hspan⟩ := hresult
    obtain ⟨d,k,hk,td,dpc,d20,d22,dframe,dcsr⟩ := E5R.Thermostat.BearerAuth.contract_quiet B a ram eng sp (a.get 10) header hspan nonzero
      hprefix hkeybytes apc asp a23 rfl alen hm ha hs hlen hkey
    refine ⟨d,n+k,by omega,?_,?_,d20,d22,?_,dcsr.trans acsr⟩
    · simpa only [hv,memory] using ta.trans td
    · simpa only [hv,endPc,BearerAuth.matches_auth_spec] using dpc
    · intro r h1 h5 h6 h7 h20 h22 h24 h25 h28 h29 hr
      exact (dframe r h1 h20 h22 h24 h25 (by omega)).trans (aframe r h1 h5 h6 h7 h28 h29 hr)

end E5R.Thermostat.RequestAuth
