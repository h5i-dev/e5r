-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.I16AfterFour
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.I16DigitStoreQuiet
import Projects.thermostat.I16LeadingPrepareQuiet
import Projects.thermostat.I16LeadingPresentQuiet
import Projects.thermostat.I16LeadingZeroQuiet
import Projects.thermostat.I16PadReadyQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.I16AfterFour
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp fmt : Word) (v : BitVec 16) (n : Nat)
    (hv : v.toInt.natAbs = n) (hn : 1000 ≤ n) (hb : n ≤ 32768)
    (hp : c.pc = 0x80004f3c#32) (hs : c.get 2 = sp) (h10 : c.get 10 = SignedMagnitude.input v)
    (h12 : c.get 12 = BitVec.ofNat 32 (n/10000)) (h13 : c.get 13 = fmt) (h14 : c.get 14 = 1#32)
    (hst : Memory.Block B sp 16)
    (hpair : Bytes.Span B ram (sp+4#32) (DecimalDigits.fourTail n))
    (hunit : ReadBytes.Byte B img ram ((0x80005e10#32+BitVec.ofNat 32 (2*(n/10000)))+1#32) (DecimalDigits.digit (n/10000))) :
    ∃ d k r, k ≤ 27 ∧ Quiet.Steps B img k ⟨c,ram⟩ ⟨d,r⟩ ∧
      I16Ready.Ready c d sp fmt v (if n < 10000 then 4 else 3) (if n < 10000 then 4 else 5) ∧
      ReadBytes.Span B img r (sp+BitVec.ofNat 32 (if n < 10000 then 4 else 3)) (ReplyJson.decimal n) ∧
      ViewFrame.Region ram r (sp+8#32) 8 ∧
      (∀ x, (∀ i : Fin 16, x ≠ sp+BitVec.ofNat 32 i.val) → r x = ram x) := by
  have hvn : v.toInt.natAbs ≠ 0 := by omega
  by_cases ht : n < 10000
  · have hq : n/10000 = 0 := by omega
    obtain ⟨a,ta,apc,a11,a12,a15,ar,ac⟩ := E5R.Thermostat.I16LeadingZero.contract_quiet B c ram v hvn h10 (by simpa only [hq] using h12) hp
    have asp : a.get 2 = sp := (ar 2 (by decide) (by decide) (by decide)).trans hs
    have a10 : a.get 10 = SignedMagnitude.input v := (ar 10 (by decide) (by decide) (by decide)).trans h10
    have a13 : a.get 13 = fmt := (ar 13 (by decide) (by decide) (by decide)).trans h13
    have a14 : a.get 14 = 1#32 := (ar 14 (by decide) (by decide) (by decide)).trans h14
    have af : I16Protected.Frame c a := by
      intro reg hr
      exact ar reg (I16Protected.ne reg 11 hr (by decide) (by decide))
        (I16Protected.ne reg 12 hr (by decide) (by decide)) (I16Protected.ne reg 15 hr (by decide) (by decide))
    obtain ⟨d,td,hd⟩ := E5R.Thermostat.I16PadReady.contract_quiet B c a ram sp fmt v 1 (by decide) asp a10 a13 a14 apc ac af
    refine ⟨d,17,ram,by decide,ta.trans td,?_,?_,fun _ => rfl,fun _ _ => rfl⟩
    · simpa only [ite_eq_left ht] using hd
    · rw [ite_eq_left ht,DecimalDigits.pair_four n hn ht]
      exact ReadBytes.of_ram hpair
  · have hq : 0 < n/10000 := by omega
    have hqb : n/10000 < 10 := by omega
    obtain ⟨a,ta,apc,a11,a12,a15,ar,ac⟩ := E5R.Thermostat.I16LeadingPresent.contract_quiet B c ram v (n/10000) hq hqb hvn h10 h12 hp
    have asp : a.get 2 = sp := (ar 2 (by decide) (by decide) (by decide)).trans hs
    have a14 : a.get 14 = 1#32 := (ar 14 (by decide) (by decide) (by decide)).trans h14
    obtain ⟨b,tb,bpc,b11,b12,b14,br,bc⟩ := E5R.Thermostat.I16LeadingPrepare.contract_quiet B a ram sp (n/10000) 1 hqb (by decide) (by decide) asp a11 a14 hunit apc
    have bsp : b.get 2 = sp := (br 2 (by decide) (by decide) (by decide)).trans asp
    let rr := ramPut ram (sp+3#32) (DecimalDigits.digit (n/10000))
    let z := b.goto 0x80004f6a#32
    have tz : Quiet.Step B img ⟨b,ram⟩ ⟨z,rr⟩ :=
      E5R.Thermostat.I16DigitStore.contract_quiet B b ram sp (n/10000) 1 bpc b11 b12 hqb (by decide) (by decide) hst
    have z10 : z.get 10 = SignedMagnitude.input v := (br 10 (by decide) (by decide) (by decide)).trans
      ((ar 10 (by decide) (by decide) (by decide)).trans h10)
    have z13 : z.get 13 = fmt := (br 13 (by decide) (by decide) (by decide)).trans
      ((ar 13 (by decide) (by decide) (by decide)).trans h13)
    have zf : I16Protected.Frame c z := by
      intro reg hr
      have ne (q : Reg) (hq : q.val < 18) (h9 : q ≠ 9) := I16Protected.ne reg q hr hq h9
      exact (br reg (ne 11 (by decide) (by decide)) (ne 12 (by decide) (by decide)) (ne 14 (by decide) (by decide))).trans
        (ar reg (ne 11 (by decide) (by decide)) (ne 12 (by decide) (by decide)) (ne 15 (by decide) (by decide)))
    obtain ⟨d,td,hd⟩ := E5R.Thermostat.I16PadReady.contract_quiet B c z rr sp fmt v 0 (by decide) bsp z10 z13 b14 rfl (bc.trans ac) zf
    have hpairs : Bytes.Span B rr (sp+4#32) (DecimalDigits.fourTail n) := by
      apply ViewFrame.span hpair
      intro i
      apply ramPut_ne
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using Bytes.offset_ne sp (4+i.val) 3
        (by have := i.isLt;change i.val < 4 at this;omega) (by decide) (by omega)
    have hbytes : Bytes.Span B rr (sp+3#32) (ReplyJson.decimal n) := by
      rw [DecimalDigits.pair_five n (by omega) (by omega)]
      exact Bytes.cons_of_block hst (by decide) (by change 3+1+4 ≤ 16;decide) (ramPut_eq _ _ _) hpairs
    refine ⟨d,27,rr,by decide,((ta.trans tb).trans (.single tz)).trans td,?_,?_,?_,?_⟩
    · simpa only [ite_eq_right ht] using hd
    · rw [ite_eq_right ht];exact ReadBytes.of_ram hbytes
    · intro i
      apply ramPut_ne
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using Bytes.offset_ne sp (8+i.val) 3
        (by have := i.isLt;omega) (by decide) (by omega)
    · intro x hx
      exact ramPut_ne _ (hx ⟨3,by decide⟩)

end E5R.Thermostat.I16AfterFour
