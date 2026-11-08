-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.I16Large
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.I16AfterFourQuiet
import Projects.thermostat.I16LargeEntryQuiet
import Projects.thermostat.I16LargePairQuiet
import Projects.thermostat.I16LargeQuotientQuiet
import Projects.thermostat.I16LargeRemainderQuiet
import Projects.thermostat.I16StartQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.I16Large
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp ptr fmt : Word) (v : BitVec 16)
    (hp : c.pc = 0x80004e5e#32) (hsp : c.get 2 = sp+16#32) (h10 : c.get 10 = ptr) (h11 : c.get 11 = fmt)
    (hst : Memory.Block B sp 16) (hsa : sp.toNat%4 = 0)
    (hm : Memory.Block B ptr 2) (ha : ptr.toNat%2 = 0)
    (hv : extend .h true (ramRead ram ptr .h) = SignedMagnitude.input v)
    (hsep : WordRegions.Disjoint ptr 2 sp 16) (hn : 1000 ≤ v.toInt.natAbs)
    (hrom : ∀ i : Fin 100, ∀ unit : Bool, B.inRam (DigitTable.address i unit) 1 = false) :
    ∃ d k r, k ≤ 77 ∧ Quiet.Steps B img k ⟨c,ram⟩ ⟨d,r⟩ ∧
      I16Ready.Ready c d sp fmt v (if v.toInt.natAbs < 10000 then 4 else 3) (if v.toInt.natAbs < 10000 then 4 else 5) ∧
      ReadBytes.Span B img r (sp+BitVec.ofNat 32 (if v.toInt.natAbs < 10000 then 4 else 3)) (ReplyJson.decimal v.toInt.natAbs) ∧
      ViewFrame.Region (I16Save.memory ram sp c) r (sp+8#32) 8 ∧
      (∀ x, (∀ i : Fin 16, x ≠ sp+BitVec.ofNat 32 i.val) → r x = ram x) := by
  let n := v.toInt.natAbs
  let r0 := I16Save.memory ram sp c
  have hb : n ≤ 32768 := ReplyJsonBounds.magnitude v
  obtain ⟨a,ta,ha⟩ := E5R.Thermostat.I16Start.contract_quiet B c ram sp ptr fmt v hp hsp h10 h11 hst hsa hm ha hv hsep
  obtain ⟨b,tb,bpc,br,bc⟩ := E5R.Thermostat.I16LargeEntry.contract_quiet B a r0 n hn hb ha.x14 ha.x16 ha.pc
  obtain ⟨u,tu,upc,u12,u14,u11,ur,uc⟩ := E5R.Thermostat.I16LargeQuotient.contract_quiet B b r0 n hb ((br 12).trans ha.x12) ((br 11).trans ha.x11) bpc
  have usp : u.get 2 = sp := (ur 2 (by decide) (by decide) (by decide)).trans ((br 2).trans ha.spReg)
  have u10 : u.get 10 = SignedMagnitude.input v := (ur 10 (by decide) (by decide) (by decide)).trans ((br 10).trans ha.x10)
  have u13 : u.get 13 = fmt := (ur 13 (by decide) (by decide) (by decide)).trans ((br 13).trans ha.x13)
  obtain ⟨z,tz,zpc,z14,z15,z16,z11,zr,zc⟩ := E5R.Thermostat.I16LargeRemainder.contract_quiet B u r0 (n%10000) (by omega) u11 upc
  have zsp : z.get 2 = sp := (zr 2 (by decide) (by decide) (by decide) (by decide)).trans usp
  have z10 : z.get 10 = SignedMagnitude.input v := (zr 10 (by decide) (by decide) (by decide) (by decide)).trans u10
  have z12 : z.get 12 = BitVec.ofNat 32 (n/10000) := (zr 12 (by decide) (by decide) (by decide) (by decide)).trans u12
  have z13 : z.get 13 = fmt := (zr 13 (by decide) (by decide) (by decide) (by decide)).trans u13
  let p0 := 0x80005e10#32+BitVec.ofNat 32 (2*((n%10000)/100))
  let p1 := 0x80005e10#32+BitVec.ofNat 32 (2*((n%10000)%100))
  let b0 := DecimalDigits.digit ((n%10000)/100/10)
  let b1 := DecimalDigits.digit ((n%10000)/100%10)
  let b2 := DecimalDigits.digit (((n%10000)%100)/10)
  let b3 := DecimalDigits.digit (((n%10000)%100)%10)
  have h0 : ReadBytes.Byte B img r0 p0 b0 := by
    have hh := DigitTable.byte B r0 ⟨(n%10000)/100,by omega⟩ false (hrom ⟨(n%10000)/100,by omega⟩ false)
    simpa only [DigitTable.address,Bool.false_eq_true,ite_false,Nat.add_zero,p0,b0,DecimalDigits.digit] using hh
  have h1 : ReadBytes.Byte B img r0 (p0+1#32) b1 := by
    have hh := DigitTable.byte B r0 ⟨(n%10000)/100,by omega⟩ true (hrom ⟨(n%10000)/100,by omega⟩ true)
    simpa only [DigitTable.address,ite_true,BitVec.ofNat_add,BitVec.add_assoc,p0,b1,DecimalDigits.digit] using hh
  have h2 : ReadBytes.Byte B img r0 p1 b2 := by
    have hh := DigitTable.byte B r0 ⟨(n%10000)%100,by omega⟩ false (hrom ⟨(n%10000)%100,by omega⟩ false)
    simpa only [DigitTable.address,Bool.false_eq_true,ite_false,Nat.add_zero,p1,b2,DecimalDigits.digit] using hh
  have h3 : ReadBytes.Byte B img r0 (p1+1#32) b3 := by
    have hh := DigitTable.byte B r0 ⟨(n%10000)%100,by omega⟩ true (hrom ⟨(n%10000)%100,by omega⟩ true)
    simpa only [DigitTable.address,ite_true,BitVec.ofNat_add,BitVec.add_assoc,p1,b3,DecimalDigits.digit] using hh
  let rp := I16LargePair.memory r0 sp b0 b1 b2 b3
  obtain ⟨w,tw,wpc,w14,wr,wc⟩ := E5R.Thermostat.I16LargePair.contract_quiet B z r0 sp p0 p1 b0 b1 b2 b3 zpc zsp z14 z11 h0 h1 h2 h3 hst
  have wsp : w.get 2 = sp := (wr 2 (by decide) (by decide) (by decide) (by decide)).trans zsp
  have w10 : w.get 10 = SignedMagnitude.input v := (wr 10 (by decide) (by decide) (by decide) (by decide)).trans z10
  have w12 : w.get 12 = BitVec.ofNat 32 (n/10000) := (wr 12 (by decide) (by decide) (by decide) (by decide)).trans z12
  have w13 : w.get 13 = fmt := (wr 13 (by decide) (by decide) (by decide) (by decide)).trans z13
  have hpair : Bytes.Span B rp (sp+4#32) (DecimalDigits.fourTail n) := I16LargePair.bytes B r0 sp b0 b1 b2 b3 hst
  have hunit : ReadBytes.Byte B img rp ((0x80005e10#32+BitVec.ofNat 32 (2*(n/10000)))+1#32) (DecimalDigits.digit (n/10000)) := by
    have hq : n/10000 < 10 := by omega
    have hh := DigitTable.byte B rp ⟨n/10000,by omega⟩ true (hrom ⟨n/10000,by omega⟩ true)
    simpa only [DigitTable.address,ite_true,Nat.mod_eq_of_lt hq,BitVec.ofNat_add,BitVec.add_assoc,DecimalDigits.digit] using hh
  obtain ⟨d,j,r,hj,td,hd,hbytes,hsaved,hframe⟩ := E5R.Thermostat.I16AfterFour.contract_quiet B w rp sp fmt v n rfl hn hb wpc wsp w10 w12 w13 w14 hst hpair hunit
  have wcsr : w.sameCsr c := (((wc.trans zc).trans uc).trans bc).trans ha.csr
  have wframe : I16Protected.Frame c w := by
    intro reg hr
    have ne (q : Reg) (hq : q.val < 18) (h9 : q ≠ 9) := I16Protected.ne reg q hr hq h9
    exact (wr reg (ne 15 (by decide) (by decide)) (ne 14 (by decide) (by decide)) (ne 16 (by decide) (by decide)) (ne 11 (by decide) (by decide))).trans
      ((zr reg (ne 14 (by decide) (by decide)) (ne 15 (by decide) (by decide)) (ne 16 (by decide) (by decide)) (ne 11 (by decide) (by decide))).trans
      ((ur reg (ne 12 (by decide) (by decide)) (ne 14 (by decide) (by decide)) (ne 11 (by decide) (by decide))).trans ((br reg).trans (ha.saved reg hr))))
  refine ⟨d,14+1+8+17+10+j,r,by omega,((((ta.trans tb).trans tu).trans tz).trans tw).trans td,?_,hbytes,?_,?_⟩
  · exact ⟨hd.pc,hd.spReg,hd.x1,hd.x10,hd.x11,hd.x12,hd.x13,hd.x14,hd.x15,hd.csr.trans wcsr,
      fun reg hr => (hd.saved reg hr).trans (wframe reg hr)⟩
  · intro i
    apply (hsaved i).trans
    apply I16LargePair.frame
    intro j
    have hi := i.isLt;have hj := j.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using Bytes.offset_ne sp (8+i.val) (4+j.val) (by omega) (by omega) (by omega)
  · intro x hx
    exact (hframe x hx).trans ((I16LargePair.frame r0 sp x b0 b1 b2 b3 (by
      intro i
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨4+i.val,by have := i.isLt;omega⟩)).trans (I16Save.frame ram sp c x hx))

end E5R.Thermostat.I16Large
