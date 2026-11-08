-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.I16Small
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.I16AfterPairQuiet
import Projects.thermostat.I16SmallArithmeticQuiet
import Projects.thermostat.I16SmallEntryQuiet
import Projects.thermostat.I16SmallIndexQuiet
import Projects.thermostat.I16SmallPairQuiet
import Projects.thermostat.I16StartQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.I16Small
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp ptr fmt : Word) (v : BitVec 16)
    (hp : c.pc = 0x80004e5e#32) (hsp : c.get 2 = sp+16#32) (h10 : c.get 10 = ptr) (h11 : c.get 11 = fmt)
    (hst : Memory.Block B sp 16) (hsa : sp.toNat%4 = 0)
    (hm : Memory.Block B ptr 2) (ha : ptr.toNat%2 = 0)
    (hv : extend .h true (ramRead ram ptr .h) = SignedMagnitude.input v)
    (hsep : WordRegions.Disjoint ptr 2 sp 16) (hn : 10 ≤ v.toInt.natAbs) (hb : v.toInt.natAbs < 1000)
    (hrom : ∀ i : Fin 100, ∀ unit : Bool, B.inRam (DigitTable.address i unit) 1 = false) :
    ∃ d k r, k ≤ 62 ∧ Quiet.Steps B img k ⟨c,ram⟩ ⟨d,r⟩ ∧
      I16Ready.Ready c d sp fmt v (if v.toInt.natAbs < 100 then 6 else 5) (if v.toInt.natAbs < 100 then 2 else 3) ∧
      ReadBytes.Span B img r (sp+BitVec.ofNat 32 (if v.toInt.natAbs < 100 then 6 else 5)) (ReplyJson.decimal v.toInt.natAbs) ∧
      ViewFrame.Region (I16Save.memory ram sp c) r (sp+8#32) 8 ∧
      (∀ x, (∀ i : Fin 16, x ≠ sp+BitVec.ofNat 32 i.val) → r x = ram x) := by
  let n := v.toInt.natAbs
  let r0 := I16Save.memory ram sp c
  obtain ⟨a,ta,ha⟩ := E5R.Thermostat.I16Start.contract_quiet B c ram sp ptr fmt v hp hsp h10 h11 hst hsa hm ha hv hsep
  obtain ⟨b,tb,bpc,b15,br,bc⟩ := E5R.Thermostat.I16SmallEntry.contract_quiet B a r0 n hn hb ha.x14 ha.x16 ha.pc
  have bsp : b.get 2 = sp := (br 2 (by decide)).trans ha.spReg
  have b10 : b.get 10 = SignedMagnitude.input v := (br 10 (by decide)).trans ha.x10
  have b11 : b.get 11 = BitVec.ofNat 32 n := (br 11 (by decide)).trans ha.x11
  have b12 : b.get 12 = (BitVec.ofNat 32 n) <<< 16 := (br 12 (by decide)).trans ha.x12
  have b13 : b.get 13 = fmt := (br 13 (by decide)).trans ha.x13
  obtain ⟨u,tu,upc,u14,u12,u11,ur,uc⟩ := E5R.Thermostat.I16SmallArithmetic.contract_quiet B b r0 n (by omega) b12 b11 bpc
  have usp : u.get 2 = sp := (ur 2 (by decide) (by decide) (by decide)).trans bsp
  have u10 : u.get 10 = SignedMagnitude.input v := (ur 10 (by decide) (by decide) (by decide)).trans b10
  have u13 : u.get 13 = fmt := (ur 13 (by decide) (by decide) (by decide)).trans b13
  let tens := DecimalDigits.digit ((n%100)/10)
  let units := DecimalDigits.digit ((n%100)%10)
  have ht : ReadBytes.Byte B img r0 (0x80005e10#32+BitVec.ofNat 32 (2*(n%100))) tens := by
    have hh := DigitTable.byte B r0 ⟨n%100,by omega⟩ false (hrom ⟨n%100,by omega⟩ false)
    simpa only [DigitTable.address,Bool.false_eq_true,ite_false,Nat.add_zero,tens,DecimalDigits.digit] using hh
  have hu : ReadBytes.Byte B img r0 ((0x80005e10#32+BitVec.ofNat 32 (2*(n%100)))+1#32) units := by
    have hh := DigitTable.byte B r0 ⟨n%100,by omega⟩ true (hrom ⟨n%100,by omega⟩ true)
    simpa only [DigitTable.address,ite_true,BitVec.ofNat_add,BitVec.add_assoc,units,DecimalDigits.digit] using hh
  let rp := I16SmallPair.memory r0 sp tens units
  obtain ⟨w,tw,wpc,w14,w11,wr,wc⟩ := E5R.Thermostat.I16SmallPair.contract_quiet B u r0 sp _ tens units upc usp u11 ht hu hst
  have wsp : w.get 2 = sp := (wr 2 (by decide) (by decide)).trans usp
  have w10 : w.get 10 = SignedMagnitude.input v := (wr 10 (by decide) (by decide)).trans u10
  have w12 : w.get 12 = BitVec.ofNat 32 (n/100) := (wr 12 (by decide) (by decide)).trans u12
  have w13 : w.get 13 = fmt := (wr 13 (by decide) (by decide)).trans u13
  obtain ⟨z,tz,zpc,z14,zr,zc⟩ := E5R.Thermostat.I16SmallIndex.contract_quiet B w rp wpc
  have zsp : z.get 2 = sp := (zr 2 (by decide)).trans wsp
  have z10 : z.get 10 = SignedMagnitude.input v := (zr 10 (by decide)).trans w10
  have z12 : z.get 12 = BitVec.ofNat 32 (n/100) := (zr 12 (by decide)).trans w12
  have z13 : z.get 13 = fmt := (zr 13 (by decide)).trans w13
  have hpair : Bytes.Span B rp (sp+6#32) [tens,units] := I16SmallPair.bytes B r0 sp tens units hst
  have hunit : ReadBytes.Byte B img rp ((0x80005e10#32+BitVec.ofNat 32 (2*(n/100)))+1#32) (DecimalDigits.digit (n/100)) := by
    have hq : n/100 < 10 := by omega
    have hh := DigitTable.byte B rp ⟨n/100,by omega⟩ true (hrom ⟨n/100,by omega⟩ true)
    simpa only [DigitTable.address,ite_true,Nat.mod_eq_of_lt hq,BitVec.ofNat_add,BitVec.add_assoc,DecimalDigits.digit] using hh
  obtain ⟨d,j,r,hj,td,hd,hbytes,hsaved,hframe⟩ := E5R.Thermostat.I16AfterPair.contract_quiet B z rp sp fmt v n rfl hn hb zpc zsp z10 z12 z13 z14 hst hpair hunit
  have zcsr : z.sameCsr c := (((zc.trans wc).trans uc).trans bc).trans ha.csr
  have zframe : I16Protected.Frame c z := by
    intro reg hr
    have ne (q : Reg) (hq : q.val < 18) (h9 : q ≠ 9) := I16Protected.ne reg q hr hq h9
    exact (zr reg (ne 14 (by decide) (by decide))).trans ((wr reg (ne 14 (by decide) (by decide)) (ne 11 (by decide) (by decide))).trans
      ((ur reg (ne 14 (by decide) (by decide)) (ne 12 (by decide) (by decide)) (ne 11 (by decide) (by decide))).trans
      ((br reg (ne 15 (by decide) (by decide))).trans (ha.saved reg hr))))
  refine ⟨d,14+3+13+4+1+j,r,by omega,((((ta.trans tb).trans tu).trans tw).trans tz).trans td,?_,hbytes,?_,?_⟩
  · exact ⟨hd.pc,hd.spReg,hd.x1,hd.x10,hd.x11,hd.x12,hd.x13,hd.x14,hd.x15,hd.csr.trans zcsr,
      fun reg hr => (hd.saved reg hr).trans (zframe reg hr)⟩
  · intro i
    apply (hsaved i).trans
    apply I16SmallPair.frame
    · simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using Bytes.offset_ne sp (8+i.val) 6 (by have := i.isLt;omega) (by decide) (by omega)
    · simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using Bytes.offset_ne sp (8+i.val) 7 (by have := i.isLt;omega) (by decide) (by omega)
  · intro x hx
    exact (hframe x hx).trans ((I16SmallPair.frame r0 sp x tens units (hx ⟨6,by decide⟩) (hx ⟨7,by decide⟩)).trans (I16Save.frame ram sp c x hx))

end E5R.Thermostat.I16Small
