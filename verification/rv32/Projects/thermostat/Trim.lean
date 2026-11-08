import Projects.thermostat.TrimFlow
import Projects.thermostat.Interrupt
import Projects.thermostat.TrimLeft
import Projects.thermostat.TrimRight
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.Trim
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r.val < 8 ∨ r.val = 10 ∨ 16 < r.val → d.get r = c.get r

theorem outside (r : Reg) (hr : r.val < 8 ∨ r.val = 10 ∨ 16 < r.val) (j : Reg)
    (hj : j.val = 8 ∨ j.val = 9 ∨ 11 ≤ j.val ∧ j.val ≤ 16) : r ≠ j := by
  intro he;rw [he] at hr;omega

theorem Frame.trans {a b c : Core} (hab : Frame a b) (hbc : Frame b c) : Frame a c :=
  fun r hr => (hbc r hr).trans (hab r hr)

/-- Complete actual inlined trim, including empty and all-whitespace input.
    The input is arbitrary bytes in checked RAM. The downstream pointer and
    length describe exactly the independent trim, and RAM remains unchanged. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (hs : Bytes.Span B ram p xs) (hp : c.pc = 0x80001f7e#32)
    (h11 : c.get 11 = p) (h12 : c.get 12 = BitVec.ofNat 32 xs.length) :
    ∃ d k, k ≤ 18*xs.length+25 ∧ DetSteps B img k ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80001fb4#32 ∧
      d.get 8 = p+BitVec.ofNat 32 (xs.length-(TrimMath.left xs).length) ∧
      d.get 9 = BitVec.ofNat 32 (TrimMath.trim xs).length ∧
      Bytes.Span B ram (d.get 8) (TrimMath.trim xs) ∧ Frame c d ∧ d.sameCsr c := by
  cases xs with
  | nil =>
    let a := c.goto 0x80001fb0#32
    have se : DetStep B img ⟨c,ram⟩ ⟨a,ram⟩ := by
      simpa only [show BitVec.ofNat 32 ([] : List (BitVec 8)).length = 0#32 from rfl,ite_true] using
        TrimFlow.entry B c ram (BitVec.ofNat 32 ([] : List (BitVec 8)).length) hp h12
    have st := TrimFlow.empty_contract B a p ram rfl h11
    obtain ⟨hpc,h9,h8,hregs,hcsr⟩ := TrimFlow.empty_fields a p
    refine ⟨TrimFlow.empty a p,3,by decide,(DetSteps.single se).trans st,hpc,?_,?_,?_,?_,hcsr⟩
    · simpa [TrimMath.left] using h8
    · simpa [TrimMath.trim,TrimMath.left] using h9
    · rw [h8]
      exact Bytes.empty B ram p
    · intro r hr;exact hregs r (outside r hr _ (by decide)) (outside r hr _ (by decide))
  | cons b bs =>
    let xs := b::bs
    let ds := TrimMath.left xs
    let q := p+BitVec.ofNat 32 (xs.length-ds.length)
    have hbound : ds.length ≤ xs.length := TrimMath.left_length xs
    have hnz : BitVec.ofNat 32 xs.length ≠ 0#32 := by
      intro he
      have hh := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hs.length] at hh
      change xs.length = 0 at hh
      simp [xs] at hh
    let a := c.goto 0x80001f80#32
    have se : DetStep B img ⟨c,ram⟩ ⟨a,ram⟩ := by
      simpa only [ite_eq_right hnz] using TrimFlow.entry B c ram (BitVec.ofNat 32 xs.length) hp h12
    have st := TrimFlow.leftSetup_contract B a p (BitVec.ofNat 32 xs.length) ram rfl h11 h12
    let u := TrimFlow.leftSetup a p (BitVec.ofNat 32 xs.length)
    obtain ⟨upc,u13,u15,u14,u8,u9,uregs,ucsr⟩ := TrimFlow.leftSetup_fields a p (BitVec.ofNat 32 xs.length)
    have fu : Frame c u := by
      intro r hr;exact uregs r (outside r hr _ (by decide)) (outside r hr _ (by decide))
        (outside r hr _ (by decide)) (outside r hr _ (by decide)) (outside r hr _ (by decide))
    obtain ⟨v,kl,hkl,hl,vpc,v9,v8,vregs,vcsr⟩ := TrimLeft.loop B u ram p xs hs (by simp [xs]) upc u8 u9 u14 u15
    change v.pc = (if ds = [] then 0x80001fac#32 else 0x8000210e#32) at vpc
    have fv : Frame u v := by
      intro r hr;exact vregs r (outside r hr _ (by decide)) (outside r hr _ (by decide)) (outside r hr _ (by decide))
    have v11 : v.get 11 = p := (vregs 11 (by decide) (by decide) (by decide)).trans
      ((uregs 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h11)
    have v12 : v.get 12 = BitVec.ofNat 32 xs.length := (vregs 12 (by decide) (by decide) (by decide)).trans
      ((uregs 12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h12)
    have v13 : v.get 13 = p+BitVec.ofNat 32 xs.length := (vregs 13 (by decide) (by decide) (by decide)).trans u13
    have hspan : Bytes.Span B ram q ds := TrimLeft.span B ram p xs hs
    by_cases hempty : ds = []
    · have vpc' : v.pc = 0x80001fac#32 := by simpa only [ite_eq_left hempty] using vpc
      have hx := TrimFlow.leftEmpty_contract B v (p+BitVec.ofNat 32 xs.length) ram vpc' v13
      obtain ⟨dpc,d8,dregs,dcsr⟩ := TrimFlow.leftEmpty_fields v (p+BitVec.ofNat 32 xs.length)
      let d := TrimFlow.leftEmpty v (p+BitVec.ofNat 32 xs.length)
      have hd8 : d.get 8 = q := by simpa only [q,hempty,List.length_nil,Nat.sub_zero] using d8
      have hd9 : d.get 9 = BitVec.ofNat 32 (TrimMath.trim xs).length := by
        rw [dregs 9 (by decide),v9]
        change BitVec.ofNat 32 ds.length = BitVec.ofNat 32 ((ds.reverse.dropWhile TrimMath.white).reverse).length
        rw [hempty];rfl
      have fd : Frame v d := by intro r hr;exact dregs r (outside r hr _ (by decide))
      refine ⟨d,1+6+kl+2,by change _ ≤ 18*xs.length+25;omega,((DetSteps.single se).trans st).trans (hl.trans hx),dpc,hd8,hd9,?_,(fu.trans fv).trans fd,dcsr.trans (vcsr.trans ucsr)⟩
      rw [hd8]
      change Bytes.Span B ram q ((ds.reverse.dropWhile TrimMath.white).reverse)
      rw [hempty];exact Bytes.empty B ram q
    · have hn : 0 < ds.length := List.length_pos_iff.mpr hempty
      have vpc' : v.pc = 0x8000210e#32 := by simpa only [ite_eq_right hempty] using vpc
      have hx := TrimFlow.rightSetup_contract B v p (BitVec.ofNat 32 xs.length) ram vpc' v11 v12
      let w := TrimFlow.rightSetup v p (BitVec.ofNat 32 xs.length)
      obtain ⟨wpc,w11,w13,w12,wregs,wcsr⟩ := TrimFlow.rightSetup_fields v p (BitVec.ofNat 32 xs.length)
      have fw : Frame v w := by
        intro r hr;exact wregs r (outside r hr _ (by decide)) (outside r hr _ (by decide)) (outside r hr _ (by decide))
      have hptr : (p+BitVec.ofNat 32 xs.length)+0xffffffff#32 = q+BitVec.ofNat 32 (ds.length-1) :=
        TrimMath.end_pred p xs.length ds.length hn hbound
      obtain ⟨d,kr,hkr,hr,dpc,d9,dregs,dcsr⟩ := TrimRight.contract B w ram q ds hspan hn wpc (w11.trans hptr)
        ((wregs 9 (by decide) (by decide) (by decide)).trans v9) w12 w13
      have fd : Frame w d := by
        intro r hh;exact dregs r (outside r hh _ (by decide)) (outside r hh _ (by decide)) (outside r hh _ (by decide))
      have hd8 : d.get 8 = q := (dregs 8 (by decide) (by decide) (by decide)).trans
        ((wregs 8 (by decide) (by decide) (by decide)).trans v8)
      refine ⟨d,1+6+kl+5+kr,by change _ ≤ 18*xs.length+25;omega,((((DetSteps.single se).trans st).trans hl).trans hx).trans hr,dpc,hd8,?_,?_,((fu.trans fv).trans fw).trans fd,dcsr.trans (wcsr.trans (vcsr.trans ucsr))⟩
      · simpa only [TrimMath.trim,TrimMath.left,List.length_reverse,ds,xs] using d9
      · rw [hd8]
        exact TrimRight.span B ram q ds hspan

theorem closed_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (hs : Bytes.Span B ram p xs) (hp : c.pc = 0x80001f7e#32)
    (h11 : c.get 11 = p) (h12 : c.get 12 = BitVec.ofNat 32 xs.length) (hm : c.mie_ = false) :
    ∃ d k, k ≤ 18*xs.length+25 ∧ Trace.Closed B img k ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80001fb4#32 ∧
      d.get 8 = p+BitVec.ofNat 32 (xs.length-(TrimMath.left xs).length) ∧
      d.get 9 = BitVec.ofNat 32 (TrimMath.trim xs).length ∧
      Bytes.Span B ram (d.get 8) (TrimMath.trim xs) ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨d,k,hk,ht,hpc,h8,h9,hspan,hframe,hcsr⟩ := contract B c ram p xs hs hp h11 h12
  exact ⟨d,k,hk,Interrupt.close ht hm,hpc,h8,h9,hspan,hframe,hcsr⟩

end E5R.Thermostat.Trim
