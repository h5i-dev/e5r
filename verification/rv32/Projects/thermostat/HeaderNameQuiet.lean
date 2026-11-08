-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.HeaderName
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.HeaderAdvanceQuiet
import Projects.thermostat.HeaderNameHeadQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.HeaderName
theorem contract_quiet (B : Board) (ram : Word → BitVec 8) (xs ys : List (BitVec 8))
    (hl : xs.length = ys.length) (hne : xs ≠ []) (p q : Word)
    (hx : ReadBytes.Span B img ram p xs) (hy : ReadBytes.Span B img ram q ys)
    (c : Core) (hp : c.pc = 0x80002706#32) (h10 : c.get 10 = p) (h14 : c.get 14 = q)
    (h5 : c.get 5 = BitVec.ofNat 32 xs.length) :
    ∃ d n, n ≤ 15*xs.length ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if HeaderSpec.same xs ys then 0x80002738#32 else 0x800026e2#32) ∧ Frame c d ∧ d.sameCsr c := by
  induction xs generalizing ys p q c with
  | nil => contradiction
  | cons a as ih =>
    cases ys with
    | nil => simp at hl
    | cons b bs =>
      have hlen : as.length = bs.length := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hl
      obtain ⟨u,tu,upc,uregs,ucsr⟩ := E5R.Thermostat.HeaderNameHead.contract_quiet B c ram p q a b hp h10 h14 (ReadBytes.head hx) (ReadBytes.head hy)
      by_cases he : HeaderSpec.lower a = HeaderSpec.lower b
      · have upc' : u.pc = 0x8000272e#32 := by simpa only [ite_eq_left he] using upc
        obtain ⟨v,tv,vpc,v10,v14,v5,vregs,vcsr⟩ := E5R.Thermostat.HeaderAdvance.contract_quiet B u ram p q (a::as).length
          (by simp) hx.length upc'
          ((uregs 10 (by decide) (by decide) (by decide) (by decide)).trans h10)
          ((uregs 14 (by decide) (by decide) (by decide) (by decide)).trans h14)
          ((uregs 5 (by decide) (by decide) (by decide) (by decide)).trans h5)
        cases as with
        | nil =>
          have hb : bs = [] := by apply List.eq_nil_of_length_eq_zero;simpa only [List.length_nil] using hlen.symm
          subst bs
          refine ⟨v,15,by simp,tu.trans tv,?_,?_,vcsr.trans ucsr⟩
          · have hh : HeaderSpec.same [a] [b] = true := by simp [HeaderSpec.same,he]
            simpa only [List.length_cons,List.length_nil,ite_true,hh] using vpc
          · intro r h1 h2 h3 h4 h5 h6 h7
            exact (vregs r h1 h4 h5).trans (uregs r h2 h3 h6 h7)
        | cons z zs =>
          have vpc' : v.pc = 0x80002706#32 := by
            have hn : (a::z::zs).length ≠ 1 := by simp
            simpa only [ite_eq_right hn] using vpc
          have v5' : v.get 5 = BitVec.ofNat 32 (z::zs).length := by simpa only [List.length_cons,Nat.add_sub_cancel] using v5
          obtain ⟨d,k,hk,td,dpc,dframe,dcsr⟩ := ih bs hlen (by simp) (p+1#32) (q+1#32)
            (ReadBytes.tail hx) (ReadBytes.tail hy) v vpc' v10 v14 v5'
          refine ⟨d,11+(4+k),by simp only [List.length_cons] at hk ⊢;omega,tu.trans (tv.trans td),?_,?_,(dcsr.trans vcsr).trans ucsr⟩
          · simpa only [HeaderMath.same_cons,decide_eq_true he,Bool.true_and] using dpc
          · intro r h1 h2 h3 h4 h5 h6 h7
            exact (dframe r h1 h2 h3 h4 h5 h6 h7).trans ((vregs r h1 h4 h5).trans (uregs r h2 h3 h6 h7))
      · refine ⟨u,11,by simp only [List.length_cons];omega,tu,?_,?_,ucsr⟩
        · simpa only [HeaderMath.same_cons,decide_eq_false he,Bool.false_and,Bool.false_eq_true,ite_false,ite_eq_right he] using upc
        · intro r h1 h2 h3 h4 h5 h6 h7
          exact uregs r h2 h3 h6 h7

end E5R.Thermostat.HeaderName
