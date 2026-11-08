import Projects.thermostat.MemcmpHead
import Projects.thermostat.MemcmpAdvance
import Projects.thermostat.MemcmpReturn
import Projects.thermostat.MemcmpSpec
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.MemcmpLoop
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r.val < 10 ∨ 14 < r.val → d.get r = c.get r

theorem outside (r k : Reg) (hr : r.val < 10 ∨ 14 < r.val) (hk : 10 ≤ k.val ∧ k.val ≤ 14) : r ≠ k := by
  intro he;have hv := congrArg Fin.val he;omega

theorem contract (B : Board) (ram : Word → BitVec 8) (xs ys : List (BitVec 8))
    (hl : xs.length = ys.length) (hne : xs ≠ []) (p q : Word)
    (hx : ReadBytes.Span B img ram p xs) (hy : ReadBytes.Span B img ram q ys)
    (c : Core) (hp : c.pc = 0x80005164#32) (h10 : c.get 10 = p)
    (h11 : c.get 11 = q) (h12 : c.get 12 = BitVec.ofNat 32 xs.length) :
    ∃ d n, n ≤ 7*xs.length+2 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = c.get 1 &&& ~~~1 ∧ d.get 10 = MemcmpSpec.value xs ys ∧ Frame c d ∧ d.sameCsr c := by
  induction xs generalizing ys p q c with
  | nil => contradiction
  | cons a as ih =>
    cases ys with
    | nil => simp at hl
    | cons b bs =>
      have hlen : as.length = bs.length := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hl
      obtain ⟨u,tu,upc,u13,u14,uregs,ucsr⟩ := MemcmpHead.contract B c ram p q a b hp h10 h11 (ReadBytes.head hx) (ReadBytes.head hy)
      have ura : u.get 1 = c.get 1 := uregs 1 (by decide) (by decide)
      by_cases he : a = b
      · have upc' : u.pc = 0x80005170#32 := by simpa only [ite_eq_left he] using upc
        obtain ⟨v,tv,vpc,v10,v11,v12,vregs,vcsr⟩ := MemcmpAdvance.contract B u ram p q (a::as).length
          (by simp) hx.length upc'
          ((uregs 10 (by decide) (by decide)).trans h10) ((uregs 11 (by decide) (by decide)).trans h11)
          ((uregs 12 (by decide) (by decide)).trans h12)
        have vra : v.get 1 = c.get 1 := (vregs 1 (by decide) (by decide) (by decide)).trans ura
        cases as with
        | nil =>
          have hb : bs = [] := by apply List.eq_nil_of_length_eq_zero;simpa only [List.length_nil] using hlen.symm
          subst bs
          have vpc' : v.pc = 0x80005178#32 := by simpa only [List.length_cons,List.length_nil,ite_true] using vpc
          obtain ⟨d,td,dpc,d10,dregs,dcsr⟩ := MemcmpReturn.zero B v ram vpc'
          refine ⟨d,9,by simp,tu.trans (tv.trans td),by rw [dpc,vra],?_,?_,(dcsr.trans vcsr).trans ucsr⟩
          · rw [MemcmpSpec.value,ite_eq_left he];exact d10
          · intro r hr
            exact (dregs r (outside r 10 hr (by decide))).trans
              ((vregs r (outside r 10 hr (by decide)) (outside r 11 hr (by decide)) (outside r 12 hr (by decide))).trans
                (uregs r (outside r 13 hr (by decide)) (outside r 14 hr (by decide))))
        | cons z zs =>
          have vpc' : v.pc = 0x80005164#32 := by
            have hn : (a::z::zs).length ≠ 1 := by simp
            simpa only [ite_eq_right hn] using vpc
          have v12' : v.get 12 = BitVec.ofNat 32 (z::zs).length := by simpa only [List.length_cons,Nat.add_sub_cancel] using v12
          obtain ⟨d,k,hk,td,dpc,d10,dframe,dcsr⟩ := ih bs hlen (by simp) (p+1#32) (q+1#32)
            (ReadBytes.tail hx) (ReadBytes.tail hy) v vpc' v10 v11 v12'
          refine ⟨d,3+(4+k),by simp only [List.length_cons] at hk ⊢;omega,tu.trans (tv.trans td),by rw [dpc,vra],?_,?_,(dcsr.trans vcsr).trans ucsr⟩
          · rw [MemcmpSpec.value,ite_eq_left he];exact d10
          · intro r hr
            exact (dframe r hr).trans
              ((vregs r (outside r 10 hr (by decide)) (outside r 11 hr (by decide)) (outside r 12 hr (by decide))).trans
                (uregs r (outside r 13 hr (by decide)) (outside r 14 hr (by decide))))
      · have upc' : u.pc = 0x8000517c#32 := by simpa only [ite_eq_right he] using upc
        obtain ⟨d,td,dpc,d10,dregs,dcsr⟩ := MemcmpReturn.diff B u ram upc'
        refine ⟨d,5,by simp only [List.length_cons];omega,tu.trans td,by rw [dpc,ura],?_,?_,dcsr.trans ucsr⟩
        · rw [MemcmpSpec.value,ite_eq_right he];rw [d10,u13,u14]
        · intro r hr
          exact (dregs r (outside r 10 hr (by decide))).trans
            (uregs r (outside r 13 hr (by decide)) (outside r 14 hr (by decide)))
end E5R.Thermostat.MemcmpLoop
