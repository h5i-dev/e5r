import Projects.thermostat.HeaderCaller
import Projects.thermostat.BearerAuth
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.RequestAuth
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) : Option (List (BitVec 8)) → Word → BitVec 8
  | none => ram
  | some header => BearerAuth.memory ram sp header

def endPc : Option (List (BitVec 8)) → Word
  | none => 0x800005a8#32
  | some header => if AuthSpec.authorized (some header) (WireSpec.ascii "dev-key") then 0x800005e2#32 else 0x800005a2#32

def Frame (c d : Core) : Prop := ∀ r : Reg, r ≠ 1 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 20 → r ≠ 22 →
  r ≠ 24 → r ≠ 25 → r ≠ 28 → r ≠ 29 → r.val < 10 ∨ 17 < r.val → d.get r = c.get r

/-- Actual header query setup/call/lookup/RET, missing/short/Bearer prefix,
    configured-key comparison and real authentication branch, from Request RAM. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (req rawPtr eng sp : Word)
    (raw : List (BitVec 8)) (entries : List HeaderSpec.Entry) (h : Header.Pre B ram req rawPtr raw entries)
    (hquery : ReadBytes.Span B img ram 0x80005b68#32 (WireSpec.ascii "authorization"))
    (hprefix : ReadBytes.Span B img ram 0x80005b75#32 (WireSpec.ascii "Bearer "))
    (hkeybytes : ReadBytes.Span B img ram 0x80005b7c#32 (WireSpec.ascii "dev-key"))
    (hp : c.pc = 0x8000052e#32) (h21 : c.get 21 = req) (h23 : c.get 23 = eng) (hsp : c.get 2 = sp)
    (hm : Memory.Block B eng 24) (ha : eng.toNat%4 = 0) (hs : Memory.Block B sp 25)
    (hlen : ramRead ram (eng+20#32) .w = 7#32) (hkey : ramRead ram (eng+16#32) .w = 0x80005b7c#32) :
    ∃ d n, n ≤ 212*entries.length+145 ∧ DetSteps B img n ⟨c,ram⟩
      ⟨d,memory ram sp (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries)⟩ ∧
      d.pc = endPc (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) ∧
      d.get 20 = 401#32 ∧ d.get 22 = 1#32 ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,n,hn,ta,apc,hresult,aframe,acsr⟩ := HeaderCaller.contract B c ram req rawPtr raw entries h hquery hp h21
  have asp : a.get 2 = sp := (aframe 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsp
  have a23 : a.get 23 = eng := (aframe 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h23
  cases hv : HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries with
  | none =>
    rw [hv] at hresult
    obtain ⟨d,k,hk,td,dpc,d20,d22,dframe,dcsr⟩ := BearerAuth.missing B a ram apc hresult
    refine ⟨d,n+k,by omega,?_,by simpa only [hv,endPc] using dpc,d20,d22,?_,dcsr.trans acsr⟩
    · simpa only [hv,memory] using ta.trans td
    · intro r h1 h5 h6 h7 h20 h22 h24 h25 h28 h29 hr
      exact (dframe r h1 h20 h22 h24 h25 (by omega)).trans (aframe r h1 h5 h6 h7 h28 h29 hr)
  | some header =>
    rw [hv] at hresult
    obtain ⟨nonzero,alen,hspan⟩ := hresult
    obtain ⟨d,k,hk,td,dpc,d20,d22,dframe,dcsr⟩ := BearerAuth.contract B a ram eng sp (a.get 10) header hspan nonzero
      hprefix hkeybytes apc asp a23 rfl alen hm ha hs hlen hkey
    refine ⟨d,n+k,by omega,?_,?_,d20,d22,?_,dcsr.trans acsr⟩
    · simpa only [hv,memory] using ta.trans td
    · simpa only [hv,endPc,BearerAuth.matches_auth_spec] using dpc
    · intro r h1 h5 h6 h7 h20 h22 h24 h25 h28 h29 hr
      exact (dframe r h1 h20 h22 h24 h25 (by omega)).trans (aframe r h1 h5 h6 h7 h28 h29 hr)

theorem memory_frame (ram : Word → BitVec 8) (sp x : Word) (v : Option (List (BitVec 8))) (hx : x ≠ sp+24#32) :
    memory ram sp v x = ram x := by
  cases v with
  | none => rfl
  | some header =>
    simp only [memory,BearerAuth.memory,AuthCheck.memory]
    split
    · split
      · exact ramPut_ne _ hx
      · rfl
    · rfl
end E5R.Thermostat.RequestAuth
