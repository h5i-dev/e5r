import Projects.thermostat.Literal
import Projects.thermostat.Bytes
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.Literal
open E5R

/-- Every site is checked against instruction bytes. Prefix comparisons keep
    the base register live; a final comparison may use the generic compare
    theorem directly if the compiler reuses that register for its last byte. -/
inductive Chain (img : List Segment) (rd rc base : Reg) (finish reject : Word) :
    Nat → Word → List (BitVec 8) → Prop
  | nil (k : Nat) : Chain img rd rc base finish reject k finish []
  | cons {k expected tail} (site : Site img expected)
      (rd_eq : site.rd = rd) (rc_eq : site.rc = rc) (base_eq : site.base = base)
      (offset_eq : site.offset = BitVec.ofNat 32 k) (bad_eq : site.badPc = reject)
      (next : Chain img rd rc base finish reject (k+1) site.nextPc tail) :
      Chain img rd rc base finish reject k site.loadPc (expected::tail)

theorem Chain.contract {img rd rc base finish reject k pc expected}
    (code : Chain img rd rc base finish reject k pc expected)
    (B : Board) (ram : Word → BitVec 8) (p : Word) (actual : List (BitVec 8))
    (c : Core) (hs : Bytes.Span B ram (p+BitVec.ofNat 32 k) actual)
    (hlen : actual.length = expected.length) (hp : c.pc = pc) (hbase : c.get base = p)
    (hbr : base ≠ rd) (hbc : base ≠ rc) :
    ∃ d n, n ≤ 3*expected.length ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if actual = expected then finish else reject) ∧ d.get base = p ∧
      (∀ r : Reg, r ≠ rd → r ≠ rc → d.get r = c.get r) ∧ d.sameCsr c := by
  induction code generalizing actual c with
  | nil k =>
    have ha : actual = [] := List.eq_nil_of_length_eq_zero hlen
    subst actual
    exact ⟨c,0,by simp,.refl _,by simpa using hp,hbase,fun _ _ _ => rfl,Core.sameCsr_refl c⟩
  | @cons k b bs site er ec eb eo ef next ih =>
    cases actual with
    | nil => simp at hlen
    | cons a as =>
      obtain ⟨hb,hm⟩ := Bytes.head hs
      have haddr : c.get site.base+site.offset = p+BitVec.ofNat 32 k := by rw [eb,eo,hbase]
      obtain ⟨d,ht,hpc,_,_,hregs,hcsr⟩ := compare B img b a site c ram _ hp haddr hm hb
      have hr : ∀ r : Reg, r ≠ rd → r ≠ rc → d.get r = c.get r := by
        intro r h1 h2
        exact hregs r (by simpa only [er] using h1) (by simpa only [ec] using h2)
      have hdBase : d.get base = p := (hr base hbr hbc).trans hbase
      by_cases he : a = b
      · have hptr : (p+BitVec.ofNat 32 k)+1#32 = p+BitVec.ofNat 32 (k+1) := by
          rw [BitVec.add_assoc,←BitVec.ofNat_add]
        have hs' : Bytes.Span B ram (p+BitVec.ofNat 32 (k+1)) as := by
          simpa only [hptr] using Bytes.tail hs
        have hdp : d.pc = site.nextPc := by simpa only [ite_eq_left he] using hpc
        obtain ⟨e,n,hn,hsteps,epc,ebase,eregs,ecsr⟩ := ih as d hs' (by simpa using hlen) hdp hdBase
        refine ⟨e,3+n,by simp only [List.length_cons];omega,ht.trans hsteps,?_,ebase,?_,ecsr.trans hcsr⟩
        · have hh : a::as = b::bs ↔ as = bs := by simp only [List.cons.injEq,he,true_and]
          simpa only [hh] using epc
        · intro r h1 h2;exact (eregs r h1 h2).trans (hr r h1 h2)
      · have hh : ¬a::as = b::bs := by intro h;exact he (List.cons.inj h).1
        refine ⟨d,3,by simp only [List.length_cons];omega,ht,?_,hdBase,hr,hcsr⟩
        simpa only [ite_eq_right he,ite_eq_right hh,ef] using hpc
end E5R.Thermostat.Literal
