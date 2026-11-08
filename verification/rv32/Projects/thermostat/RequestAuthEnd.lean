import Projects.thermostat.RequestAuth
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.RequestAuthEnd
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (req rawPtr eng sp : Word)
    (raw : List (BitVec 8)) (entries : List HeaderSpec.Entry) (h : Header.Pre B ram req rawPtr raw entries)
    (hquery : ReadBytes.Span B img ram 0x80005b68#32 (WireSpec.ascii "authorization"))
    (hprefix : ReadBytes.Span B img ram 0x80005b75#32 (WireSpec.ascii "Bearer "))
    (hkeybytes : ReadBytes.Span B img ram 0x80005b7c#32 (WireSpec.ascii "dev-key"))
    (hp : c.pc = 0x8000052e#32) (h21 : c.get 21 = req) (h23 : c.get 23 = eng) (hsp : c.get 2 = sp)
    (hm : Memory.Block B eng 24) (ha : eng.toNat%4 = 0) (hs : Memory.Block B sp 25)
    (hlen : ramRead ram (eng+20#32) .w = 7#32) (hkey : ramRead ram (eng+16#32) .w = 0x80005b7c#32) :
    ∃ d n, n ≤ 212*entries.length+145 ∧ DetSteps B img n ⟨c,ram⟩
      ⟨d,RequestAuth.memory ram sp (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries)⟩ ∧
      d.pc = RequestAuth.endPc (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) ∧
      d.get 20 = 401#32 ∧ d.get 22 = 1#32 ∧ RequestAuth.Frame c d ∧ d.sameCsr c ∧
      (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries = none → d.get 10 = 0#32) := by
  obtain ⟨a,n,hn,ta,apc,hresult,aframe,acsr⟩ := HeaderCaller.contract B c ram req rawPtr raw entries h hquery hp h21
  have asp : a.get 2 = sp := (aframe 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsp
  have a23 : a.get 23 = eng := (aframe 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h23
  cases hv : HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries with
  | none =>
    rw [hv] at hresult
    obtain ⟨d,k,hk,td,dpc,d20,d22,dframe,dcsr⟩ := BearerGuard.contract B a ram 0#32 (a.get 11).toNat
      (a.get 11).isLt apc hresult (by simp)
    have dpc' : d.pc = 0x800005a8#32 := by simpa only [ite_true] using dpc
    refine ⟨d,n+k,by omega,?_,by simpa only [hv,RequestAuth.endPc] using dpc',d20,d22,?_,dcsr.trans acsr,?_⟩
    · simpa only [hv,RequestAuth.memory] using ta.trans td
    · intro r h1 h5 h6 h7 h20 h22 h24 h25 h28 h29 hr
      exact (dframe r (Header.outside r 12 hr (by decide)) h20 h22).trans (aframe r h1 h5 h6 h7 h28 h29 hr)
    · intro _;exact (dframe 10 (by decide) (by decide) (by decide)).trans hresult
  | some header =>
    rw [hv] at hresult
    obtain ⟨nonzero,alen,hspan⟩ := hresult
    obtain ⟨d,k,hk,td,dpc,d20,d22,dframe,dcsr⟩ := BearerAuth.contract B a ram eng sp (a.get 10) header hspan nonzero
      hprefix hkeybytes apc asp a23 rfl alen hm ha hs hlen hkey
    refine ⟨d,n+k,by omega,?_,?_,d20,d22,?_,dcsr.trans acsr,?_⟩
    · simpa only [hv,RequestAuth.memory] using ta.trans td
    · simpa only [hv,RequestAuth.endPc,BearerAuth.matches_auth_spec] using dpc
    · intro r h1 h5 h6 h7 h20 h22 h24 h25 h28 h29 hr
      exact (dframe r h1 h20 h22 h24 h25 (by omega)).trans (aframe r h1 h5 h6 h7 h28 h29 hr)
    · intro hn;cases hn

end E5R.Thermostat.RequestAuthEnd
