-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.HeaderScan
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.HeaderNoneQuiet
import Projects.thermostat.HeaderOuterQuiet
import Projects.thermostat.HeaderTryQuiet
import Projects.thermostat.HeaderValueQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.HeaderScan
theorem contract_quiet (B : Board) (ram : Word → BitVec 8) (p q : Word) (raw query : List (BitVec 8))
    (hraw : Bytes.Span B ram p raw) (hquery : ReadBytes.Span B img ram q query) (hq : query.length = 13)
    (hpos : 0 < p.toNat) (hbound : p.toNat+raw.length < 2^32)
    (entries : List HeaderSpec.Entry) (table : Word) (htab : HeaderInput.Table B ram table raw.length entries) (hne : entries ≠ [])
    (c : Core) (hp : c.pc = 0x800026e8#32) (h16 : c.get 16 = table) (h17 : c.get 17 = table+BitVec.ofNat 32 (16*entries.length))
    (h15 : c.get 15 = p) (h11 : c.get 11 = q) (h12 : c.get 12 = BitVec.ofNat 32 raw.length) (h13 : c.get 13 = 13#32) :
    ∃ d n, n ≤ 212*entries.length+2 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = c.get 1 &&& ~~~1 ∧
      HeaderResult.At B ram p raw d (HeaderSpec.find raw query entries) ∧ HeaderResult.Frame c d ∧ d.sameCsr c := by
  induction entries generalizing table c with
  | nil => contradiction
  | cons e es ih =>
    have hc := htab.head
    obtain ⟨a,n,hn,ta,apc,aframe,acsr⟩ := E5R.Thermostat.HeaderTry.contract_quiet B c ram table p q raw query e hc hraw hquery hq hp h16 h15 h11 h12 h13
    have a16 : a.get 16 = table := (aframe 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h16
    have a17 : a.get 17 = table+BitVec.ofNat 32 (16*(e::es).length) :=
      (aframe 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h17
    have a15 : a.get 15 = p := (aframe 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h15
    have a11 : a.get 11 = q := (aframe 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h11
    have a12 : a.get 12 = BitVec.ofNat 32 raw.length :=
      (aframe 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h12
    have a13 : a.get 13 = 13#32 := (aframe 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h13
    have a1 : a.get 1 = c.get 1 := aframe 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    cases he : HeaderSpec.same (HeaderSpec.name raw e) query with
    | true =>
      have apc' : a.pc = 0x80002738#32 := by simpa only [he,ite_true] using apc
      obtain ⟨d,td,dpc,d10,d11,dspan,dframe,dcsr⟩ := E5R.Thermostat.HeaderValue.contract_quiet B a ram table p raw e hc hraw apc' a16 a15 a12
      have nonzero : d.get 10 ≠ 0#32 := by
        rw [d10]
        apply HeaderResult.pointer_nonzero p e.valueStart raw.length hpos hbound
        have hb := hc.bounds
        change _ ∧ _ ∧ e.valueStart ≤ e.valueEnd ∧ e.valueEnd ≤ raw.length at hb
        omega
      refine ⟨d,n+7,by simp only [List.length_cons];omega,ta.trans td,by rw [dpc,a1],?_,?_,dcsr.trans acsr⟩
      · simpa only [HeaderSpec.find,he,ite_true] using (show HeaderResult.At B ram p raw d (some e) from ⟨d10,d11,dspan,nonzero⟩)
      · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9
        exact (dframe r h4 h5).trans (aframe r h1 h2 h3 h4 h6 h8 h9)
    | false =>
      have apc' : a.pc = 0x800026e2#32 := by simpa only [he,Bool.false_eq_true,ite_false] using apc
      obtain ⟨b,tb,bpc,b16,bframe,bcsr⟩ := E5R.Thermostat.HeaderOuter.contract_quiet B a ram table (e::es).length (by simp) htab.bounded apc' a16 a17
      have b1 : b.get 1 = c.get 1 := (bframe 1 (by decide)).trans a1
      cases es with
      | nil =>
        have bpc' : b.pc = 0x8000274e#32 := by simpa only [List.length_cons,List.length_nil,ite_true] using bpc
        obtain ⟨d,td,dpc,d10,dframe,dcsr⟩ := E5R.Thermostat.HeaderNone.contract_quiet B b ram bpc'
        refine ⟨d,n+(2+2),by simp;omega,ta.trans (tb.trans td),by rw [dpc,b1],?_,?_,(dcsr.trans bcsr).trans acsr⟩
        · simpa only [HeaderSpec.find,he,Bool.false_eq_true,ite_false] using (show HeaderResult.At B ram p raw d none from d10)
        · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9
          exact (dframe r h4).trans ((bframe r h7).trans (aframe r h1 h2 h3 h4 h6 h8 h9))
      | cons z zs =>
        have bpc' : b.pc = 0x800026e8#32 := by
          have hh : (e::z::zs).length ≠ 1 := by simp
          simpa only [ite_eq_right hh] using bpc
        have hend : (table+16#32)+BitVec.ofNat 32 (16*(z::zs).length) = table+BitVec.ofNat 32 (16*(e::z::zs).length) := by
          rw [BitVec.add_assoc,←BitVec.ofNat_add]
          apply congrArg (fun k : Nat => table+BitVec.ofNat 32 k)
          simp only [List.length_cons];omega
        have b17 : b.get 17 = (table+16#32)+BitVec.ofNat 32 (16*(z::zs).length) := by rw [bframe 17 (by decide),a17,hend]
        have b15 : b.get 15 = p := (bframe 15 (by decide)).trans a15
        have b11 : b.get 11 = q := (bframe 11 (by decide)).trans a11
        have b12 : b.get 12 = BitVec.ofNat 32 raw.length := (bframe 12 (by decide)).trans a12
        have b13 : b.get 13 = 13#32 := (bframe 13 (by decide)).trans a13
        obtain ⟨d,k,hk,td,dpc,dresult,dframe,dcsr⟩ := ih (table+16#32) htab.tail (by simp) b bpc' b16 b17 b15 b11 b12 b13
        refine ⟨d,n+(2+k),by simp only [List.length_cons] at hk ⊢;omega,ta.trans (tb.trans td),by rw [dpc,b1],?_,?_,(dcsr.trans bcsr).trans acsr⟩
        · simpa only [HeaderSpec.find,he,Bool.false_eq_true,ite_false] using dresult
        · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9
          exact (dframe r h1 h2 h3 h4 h5 h6 h7 h8 h9).trans ((bframe r h7).trans (aframe r h1 h2 h3 h4 h6 h8 h9))

end E5R.Thermostat.HeaderScan
