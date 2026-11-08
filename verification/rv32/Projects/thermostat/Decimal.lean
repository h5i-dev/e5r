import Projects.thermostat.DecimalValidate
import Projects.thermostat.DecimalAccumulate
import Projects.thermostat.DecimalSetup
import Projects.thermostat.DecimalReturn
import Projects.thermostat.Interrupt
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.Decimal
open E5R E5R.Thermostat

def Result (c : Core) : Option (BitVec 16) → Prop
  | none => c.get 10 = 0#32
  | some v => c.get 10 = 1#32 ∧ (c.get 11).setWidth 16 = v

def Frame (c d : Core) : Prop := ∀ r : Reg, r.val < 10 ∨ 16 < r.val → d.get r = c.get r

theorem Frame.trans {a b c : Core} (hab : Frame a b) (hbc : Frame b c) : Frame a c :=
  fun r hr => (hbc r hr).trans (hab r hr)

theorem outside (r : Reg) (hr : r.val < 10 ∨ 16 < r.val) (j : Reg)
    (hj : 10 ≤ j.val ∧ j.val ≤ 16) : r ≠ j := by
  intro he;rw [he] at hr;omega

theorem parse_cons (b : BitVec 8) (bs : List (BitVec 8)) :
    DecimalSpec.parse (b::bs) = DecimalSpec.finish (decide (b = 45#8)) (DecimalPrefix.digits b bs) := by
  by_cases he : b = 45#8 <;> simp [DecimalSpec.parse,DecimalPrefix.digits,he]

/-- A universal byte-level ELF contract. Input readability is checked RAM, not
    an assumed decoded command. All failures return the real Option tag zero.
    The inactive payload on failure is deliberately unconstrained. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (hs : Bytes.Span B ram p xs) (hp : c.pc = 0x80001dae#32)
    (h10 : c.get 10 = p) (h11 : c.get 11 = BitVec.ofNat 32 xs.length) :
    ∃ d k, k ≤ 102 ∧ DetSteps B img k ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = c.get 1 &&& ~~~1 ∧
      Result d (DecimalSpec.parse xs) ∧ Frame c d ∧ d.sameCsr c := by
  cases xs with
  | nil =>
    let a := c.goto 0x80001dc8#32
    have st : DetStep B img ⟨c,ram⟩ ⟨a,ram⟩ := by
      refine detStep_of (by rw [hp];decide) (by rw [hp];exact dc2147491246) fun o => ?_
      rw [exec_branch,h11,Core.get_zero]
      have ht : taken .eq (BitVec.ofNat 32 ([] : List (BitVec 8)).length) (0 : Word) = true := by decide +kernel
      rw [ht]
      simp only [ite_true]
      change interp B img o (jump c (c.pc+26#32)) ram 0 [] = _
      rw [hp,show 0x80001dae#32+26#32 = 0x80001dc8#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
    obtain ⟨d,ht,hpc,hresult,hregs,hcsr⟩ := DecimalReturn.none B a ram rfl
    refine ⟨d,3,by decide,(DetSteps.single st).trans ht,hpc,hresult,?_,hcsr⟩
    intro r hr;exact hregs r (outside r hr _ (by decide))
  | cons b bs =>
    let ds := DecimalPrefix.digits b bs
    have hspan := DecimalSetup.slice B ram p b bs hs
    obtain ⟨a,hpa,apc,a11,a12,a13,aregs,acsr⟩ := DecimalPrefix.contract B c ram p b bs hs hp h10 h11
    change a.pc = (if 1 ≤ ds.length ∧ ds.length ≤ 5 then 0x80001dcc#32 else 0x80001dc8#32) at apc
    have fa : Frame c a := by
      intro r hr;exact aregs r (outside r hr _ (by decide)) (outside r hr _ (by decide)) (outside r hr _ (by decide)) (outside r hr _ (by decide)) (outside r hr _ (by decide))
    have ha10 : a.get 10 = p := (aregs 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h10
    by_cases hlen : 1 ≤ ds.length ∧ ds.length ≤ 5
    · have apc' : a.pc = 0x80001dcc#32 := by simpa only [ite_eq_left hlen] using apc
      obtain ⟨a',hsetup,a'pc,a'10,a'13,a'15,a'14,a'regs,a'csr⟩ :=
        DecimalSetup.contract B a ram p (DecimalPrefix.sign b) ds.length (by omega) hspan.length apc' ha10 a11 a13
      have fa' : Frame a a' := by
        intro r hr;exact a'regs r (outside r hr _ (by decide)) (outside r hr _ (by decide)) (outside r hr _ (by decide)) (outside r hr _ (by decide))
      have a'11 : a'.get 11 = BitVec.ofNat 32 ds.length := (a'regs 11 (by decide) (by decide) (by decide) (by decide)).trans a11
      obtain ⟨v,kv,hkv,hvalid,vpc,vout,vregs,vcsr⟩ := DecimalValidate.loop B a' ram _ ds hspan (by omega) a'pc a'11 a'15 a'14
      have fv : Frame a' v := by
        intro r hr;exact vregs r (outside r hr _ (by decide)) (outside r hr _ (by decide)) (outside r hr _ (by decide))
      by_cases hd : ds.all DecimalSpec.digit = true
      · obtain ⟨vz,vend⟩ := vout hd
        have vpc' : v.pc = 0x80001dea#32 := by simpa only [hd,ite_true] using vpc
        have v13 : v.get 13 = p+DecimalPrefix.sign b := (vregs 13 (by decide) (by decide) (by decide)).trans a'13
        have v10 : v.get 10 = (p+DecimalPrefix.sign b)+BitVec.ofNat 32 ds.length :=
          (vregs 10 (by decide) (by decide) (by decide)).trans a'10
        obtain ⟨w,hacc,wpc,w11,w13,wregs,wcsr⟩ :=
          DecimalAccumulate.loop B v ram _ ds 0 hspan (by omega) hd vpc' v13 vz v10
        have fw : Frame v w := by
          intro r hr;exact wregs r (outside r hr _ (by decide)) (outside r hr _ (by decide)) (outside r hr _ (by decide)) (outside r hr _ (by decide))
        have w12 : w.get 12 = BitVec.ofNat 32 b.toNat :=
          (wregs 12 (by decide) (by decide) (by decide) (by decide)).trans
            ((vregs 12 (by decide) (by decide) (by decide)).trans
              ((a'regs 12 (by decide) (by decide) (by decide) (by decide)).trans a12))
        obtain ⟨d,kr,hkr,hreturn,dpc,dtag,dvalue,dregs,dcsr⟩ :=
          DecimalReturn.sign B w ram b (DecimalSpec.number ds 0) (DecimalSpec.short_bound ds hd hlen.2) wpc w12 w11
        have fd : Frame w d := by
          intro r hr;exact dregs r (outside r hr _ (by decide)) (outside r hr _ (by decide)) (outside r hr _ (by decide))
        have fbefore : Frame c w := ((fa.trans fa').trans fv).trans fw
        refine ⟨d,8+5+kv+10*ds.length+kr,by omega,?_,?_,?_,fbefore.trans fd,dcsr.trans (wcsr.trans (vcsr.trans (a'csr.trans acsr)))⟩
        · exact (((hpa.trans hsetup).trans hvalid).trans hacc).trans hreturn
        · rw [dpc,fbefore 1 (by decide)]
        · rw [parse_cons]
          change Result d (DecimalSpec.finish (decide (b = 45#8)) ds)
          have hg : 1 ≤ ds.length ∧ ds.length ≤ 5 ∧ ds.all DecimalSpec.digit = true := ⟨hlen.1,hlen.2,hd⟩
          simp only [DecimalSpec.finish,ite_eq_left hg]
          by_cases hrange : DecimalSpec.number ds 0 ≤ (if b = 45#8 then 32768 else 32767)
          · have htag : d.get 10 = 1#32 := by simpa only [ite_eq_left hrange] using dtag
            have hv : (d.get 11).setWidth 16 = BitVec.ofInt 16
                (if decide (b = 45#8) then -(Int.ofNat (DecimalSpec.number ds 0)) else Int.ofNat (DecimalSpec.number ds 0)) := by
              rw [dvalue,DecimalMath.signed_low]
            simpa only [decide_eq_true_eq,ite_eq_left hrange,Result] using And.intro htag hv
          · have htag : d.get 10 = 0#32 := by simpa only [ite_eq_right hrange] using dtag
            simpa only [decide_eq_true_eq,ite_eq_right hrange,Result] using htag
      · have hd' : ds.all DecimalSpec.digit = false := Bool.eq_false_iff.mpr hd
        have vpc' : v.pc = 0x80001dc8#32 := by simpa only [hd',Bool.false_eq_true,ite_false] using vpc
        obtain ⟨d,hreturn,dpc,dtag,dregs,dcsr⟩ := DecimalReturn.none B v ram vpc'
        have fbefore : Frame c v := (fa.trans fa').trans fv
        refine ⟨d,8+5+kv+2,by omega,((hpa.trans hsetup).trans hvalid).trans hreturn,?_,?_,?_,dcsr.trans (vcsr.trans (a'csr.trans acsr))⟩
        · rw [dpc,fbefore 1 (by decide)]
        · rw [parse_cons]
          have hg : ¬(1 ≤ ds.length ∧ ds.length ≤ 5 ∧ ds.all DecimalSpec.digit = true) := by intro h;exact hd h.2.2
          change Result d (DecimalSpec.finish (decide (b = 45#8)) ds)
          simpa only [DecimalSpec.finish,ite_eq_right hg,Result] using dtag
        · exact fbefore.trans (by intro r hr;exact dregs r (outside r hr _ (by decide)))
    · have apc' : a.pc = 0x80001dc8#32 := by simpa only [ite_eq_right hlen] using apc
      obtain ⟨d,hreturn,dpc,dtag,dregs,dcsr⟩ := DecimalReturn.none B a ram apc'
      refine ⟨d,10,by decide,hpa.trans hreturn,?_,?_,?_,dcsr.trans acsr⟩
      · rw [dpc,fa 1 (by decide)]
      · rw [parse_cons]
        have hg : ¬(1 ≤ ds.length ∧ ds.length ≤ 5 ∧ ds.all DecimalSpec.digit = true) := by intro h;exact hlen ⟨h.1,h.2.1⟩
        change Result d (DecimalSpec.finish (decide (b = 45#8)) ds)
        simpa only [DecimalSpec.finish,ite_eq_right hg,Result] using dtag
      · exact fa.trans (by intro r hr;exact dregs r (outside r hr _ (by decide)))

/-- With the proved global interrupt mask, the contract admits no interrupt or
    instruction fault escape within this leaf invocation. -/
theorem closed_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (hs : Bytes.Span B ram p xs) (hp : c.pc = 0x80001dae#32)
    (h10 : c.get 10 = p) (h11 : c.get 11 = BitVec.ofNat 32 xs.length) (hm : c.mie_ = false) :
    ∃ d k, k ≤ 102 ∧ Trace.Closed B img k ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = c.get 1 &&& ~~~1 ∧
      Result d (DecimalSpec.parse xs) ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨d,k,hk,ht,hpc,hresult,hframe,hcsr⟩ := contract B c ram p xs hs hp h10 h11
  exact ⟨d,k,hk,Interrupt.close ht hm,hpc,hresult,hframe,hcsr⟩

end E5R.Thermostat.Decimal
