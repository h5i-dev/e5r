import Projects.thermostat.BearerGuard
import Projects.thermostat.BearerPrefix
import Projects.thermostat.BearerMath
import Projects.thermostat.AuthCheck
import Projects.thermostat.Subspan
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.BearerAuth
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) (header : List (BitVec 8)) : Word → BitVec 8 :=
  if header.take 7 = WireSpec.ascii "Bearer " then
    AuthCheck.memory ram sp (header.drop 7) (WireSpec.ascii "dev-key") else ram

def Frame (c d : Core) : Prop := ∀ r : Reg, r ≠ 1 → r ≠ 20 → r ≠ 22 → r ≠ 24 → r ≠ 25 →
  r.val < 10 ∨ 15 < r.val → d.get r = c.get r

theorem outside (r k : Reg) (hr : r.val < 10 ∨ 15 < r.val) (hk : 10 ≤ k.val ∧ k.val ≤ 15) : r ≠ k := by
  intro he;have hv := congrArg Fin.val he;omega

/-- The present-header path, starting before missing/short checks. Raw checked
    header bytes determine exact Bearer-prefix and configured-key acceptance. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (eng sp p : Word) (header : List (BitVec 8))
    (hheader : Bytes.Span B ram p header) (hnonzero : p ≠ 0#32)
    (hprefix : ReadBytes.Span B img ram 0x80005b75#32 (WireSpec.ascii "Bearer "))
    (hkeybytes : ReadBytes.Span B img ram 0x80005b7c#32 (WireSpec.ascii "dev-key"))
    (hp : c.pc = 0x80000542#32) (hsp : c.get 2 = sp) (h23 : c.get 23 = eng)
    (h10 : c.get 10 = p) (h11 : c.get 11 = BitVec.ofNat 32 header.length)
    (hm : Memory.Block B eng 24) (ha : eng.toNat%4 = 0) (hs : Memory.Block B sp 25)
    (hlen : ramRead ram (eng+20#32) .w = 7#32) (hkey : ramRead ram (eng+16#32) .w = 0x80005b7c#32) :
    ∃ d n, n ≤ 126 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,memory ram sp header⟩ ∧
      d.pc = (if header = WireSpec.ascii "Bearer "++WireSpec.ascii "dev-key" then 0x800005e2#32 else 0x800005a2#32) ∧
      d.get 20 = 401#32 ∧ d.get 22 = 1#32 ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,n,hn,ta,apc,a20,a22,aframe,acsr⟩ := BearerGuard.contract B c ram p header.length hheader.length hp h10 h11
  have aspp : a.get 2 = sp := (aframe 2 (by decide) (by decide) (by decide)).trans hsp
  have a23 : a.get 23 = eng := (aframe 23 (by decide) (by decide) (by decide)).trans h23
  have a10 : a.get 10 = p := (aframe 10 (by decide) (by decide) (by decide)).trans h10
  have a11 : a.get 11 = BitVec.ofNat 32 header.length := (aframe 11 (by decide) (by decide) (by decide)).trans h11
  by_cases hshort : header.length < 7
  · have hno : header.take 7 ≠ WireSpec.ascii "Bearer " := by intro hh;have := BearerMath.enough header hh;omega
    have hneq : header ≠ WireSpec.ascii "Bearer "++WireSpec.ascii "dev-key" := by
      intro hh;have he := congrArg List.length hh;change header.length = 14 at he;omega
    refine ⟨a,n,by omega,?_,?_,a20,a22,?_,acsr⟩
    · simpa only [memory,ite_eq_right hno] using ta
    · simpa only [ite_eq_right hnonzero,ite_eq_left hshort,ite_eq_right hneq] using apc
    · intro r h1 h20 h22 h24 h25 hr;exact aframe r (outside r 12 hr (by decide)) h20 h22
  · have hlong : 7 ≤ header.length := by omega
    have apc' : a.pc = 0x80000550#32 := by simpa only [ite_eq_right hnonzero,ite_eq_right hshort] using apc
    have hpre : ReadBytes.Span B img ram p (header.take 7) := ReadBytes.of_ram (Bytes.take_span hheader 7)
    have hprelen : (header.take 7).length = 7 := by rw [List.length_take,Nat.min_eq_left hlong]
    obtain ⟨b,k,hk,tb,bpc,b24,b25,bframe,bcsr⟩ := BearerPrefix.contract B a ram p (BitVec.ofNat 32 header.length)
      (header.take 7) hpre hprelen hprefix apc' a10 a11
    have b20 : b.get 20 = 401#32 := (bframe 20 (by decide) (by decide) (by decide) (by decide)).trans a20
    have b22 : b.get 22 = 1#32 := (bframe 22 (by decide) (by decide) (by decide) (by decide)).trans a22
    by_cases hmatch : header.take 7 = WireSpec.ascii "Bearer "
    · have bpc' : b.pc = 0x80000568#32 := by simpa only [ite_eq_left hmatch] using bpc
      have htok : ReadBytes.Span B img ram (p+7#32) (header.drop 7) := ReadBytes.of_ram (Bytes.drop_span hheader 7 hlong)
      have hl : (header.drop 7).length+7 = header.length := by rw [List.length_drop];omega
      have b25' : b.get 25 = BitVec.ofNat 32 ((header.drop 7).length+7) := by simpa only [hl] using b25
      have bsp : b.get 2 = sp := (bframe 2 (by decide) (by decide) (by decide) (by decide)).trans aspp
      have b23 : b.get 23 = eng := (bframe 23 (by decide) (by decide) (by decide) (by decide)).trans a23
      obtain ⟨d,j,hj,td,dpc,dframe,dcsr⟩ := AuthCheck.contract B b ram eng sp p 0x80005b7c#32 (header.drop 7)
        (WireSpec.ascii "dev-key") rfl (by simpa only [hl] using hheader.length) htok hkeybytes bpc' bsp b23 b24 b25' hm ha hs hlen hkey
      refine ⟨d,n+(k+j),by omega,?_,?_,?_,?_,?_,(dcsr.trans bcsr).trans acsr⟩
      · simpa only [memory,ite_eq_left hmatch] using ta.trans (tb.trans td)
      · simpa only [BearerMath.split_eq header _ hmatch] using dpc
      · exact (dframe 20 (by decide)).trans b20
      · exact (dframe 22 (by decide)).trans b22
      · intro r h1 h20 h22 h24 h25 hr
        exact (dframe r hr).trans
          ((bframe r h1 h24 h25 (by omega)).trans (aframe r (outside r 12 hr (by decide)) h20 h22))
    · have hneq : header ≠ WireSpec.ascii "Bearer "++WireSpec.ascii "dev-key" := by
        intro hh;apply hmatch;rw [hh];change (WireSpec.ascii "Bearer "++WireSpec.ascii "dev-key").take (WireSpec.ascii "Bearer ").length = _;simp
      refine ⟨b,n+k,by omega,?_,?_,b20,b22,?_,bcsr.trans acsr⟩
      · simpa only [memory,ite_eq_right hmatch] using ta.trans tb
      · simpa only [ite_eq_right hmatch,ite_eq_right hneq] using bpc
      · intro r h1 h20 h22 h24 h25 hr
        exact (bframe r h1 h24 h25 (by omega)).trans (aframe r (outside r 12 hr (by decide)) h20 h22)
theorem closed_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (eng sp p : Word) (header : List (BitVec 8))
    (hheader : Bytes.Span B ram p header) (hnonzero : p ≠ 0#32)
    (hprefix : ReadBytes.Span B img ram 0x80005b75#32 (WireSpec.ascii "Bearer "))
    (hkeybytes : ReadBytes.Span B img ram 0x80005b7c#32 (WireSpec.ascii "dev-key"))
    (hp : c.pc = 0x80000542#32) (hsp : c.get 2 = sp) (h23 : c.get 23 = eng)
    (h10 : c.get 10 = p) (h11 : c.get 11 = BitVec.ofNat 32 header.length)
    (hm : Memory.Block B eng 24) (ha : eng.toNat%4 = 0) (hs : Memory.Block B sp 25)
    (hlen : ramRead ram (eng+20#32) .w = 7#32) (hkey : ramRead ram (eng+16#32) .w = 0x80005b7c#32) (hmask : c.mie_ = false) :
    ∃ d n, n ≤ 126 ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,memory ram sp header⟩ ∧
      d.pc = (if header = WireSpec.ascii "Bearer "++WireSpec.ascii "dev-key" then 0x800005e2#32 else 0x800005a2#32) ∧
      d.get 20 = 401#32 ∧ d.get 22 = 1#32 ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨d,n,hn,ht,hpc,h20,h22,hframe,hcsr⟩ := contract B c ram eng sp p header hheader hnonzero hprefix hkeybytes hp hsp h23 h10 h11 hm ha hs hlen hkey
  exact ⟨d,n,hn,Interrupt.close ht hmask,hpc,h20,h22,hframe,hcsr⟩

theorem missing (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000542#32) (h10 : c.get 10 = 0#32) :
    ∃ d n, n ≤ 5 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800005a8#32 ∧
      d.get 20 = 401#32 ∧ d.get 22 = 1#32 ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨d,n,hn,ht,hpc,h20,h22,hframe,hcsr⟩ := BearerGuard.contract B c ram 0#32 (c.get 11).toNat
    (c.get 11).isLt hp h10 (by simp)
  refine ⟨d,n,hn,ht,by simpa only [ite_true] using hpc,h20,h22,?_,hcsr⟩
  intro r h1 h20 h22 h24 h25 hr
  exact hframe r (outside r 12 hr (by decide)) h20 h22

theorem matches_auth_spec (header : List (BitVec 8)) :
    (if header = WireSpec.ascii "Bearer "++WireSpec.ascii "dev-key" then 0x800005e2#32 else 0x800005a2#32) =
      (if AuthSpec.authorized (some header) (WireSpec.ascii "dev-key") then 0x800005e2#32 else 0x800005a2#32) := by
  rw [BearerMath.authorized]
  simp only [decide_eq_true_eq]
end E5R.Thermostat.BearerAuth
