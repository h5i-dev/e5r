-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.I16One
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.I16DigitStoreQuiet
import Projects.thermostat.I16LeadingPrepareQuiet
import Projects.thermostat.I16MagnitudeQuiet
import Projects.thermostat.I16OneEntryQuiet
import Projects.thermostat.I16OneLeadingQuiet
import Projects.thermostat.I16PadCallQuiet
import Projects.thermostat.I16SaveQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.I16One
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp ptr fmt : Word) (v : BitVec 16)
    (hp : c.pc = 0x80004e5e#32) (hsp : c.get 2 = sp+16#32)
    (h10 : c.get 10 = ptr) (h11 : c.get 11 = fmt)
    (hst : Memory.Block B sp 16) (hsa : sp.toNat%4 = 0)
    (hm : Memory.Block B ptr 2) (ha : ptr.toNat%2 = 0)
    (hv : extend .h true (ramRead ram ptr .h) = SignedMagnitude.input v)
    (hsep : WordRegions.Disjoint ptr 2 sp 16) (hn : v.toInt.natAbs < 10)
    (hrom : ∀ i : Fin 100, B.inRam (DigitTable.address i true) 1 = false) :
    ∃ d, Quiet.Steps B img 44 ⟨c,ram⟩ ⟨d,memory ram sp c v⟩ ∧ Ready c d sp fmt v ∧
      ReadBytes.Span B img (memory ram sp c v) (sp+7#32) (ReplyJson.decimal v.toInt.natAbs) ∧
      ViewFrame.Region (I16Save.memory ram sp c) (memory ram sp c v) (sp+8#32) 8 ∧
      (∀ x, (∀ i : Fin 16, x ≠ sp+BitVec.ofNat 32 i.val) → memory ram sp c v x = ram x) := by
  let r0 := I16Save.memory ram sp c
  let n := v.toInt.natAbs
  have hn0 : n < 10 := hn
  have ho : ViewFrame.Region ram r0 ptr 2 := fun i => I16Save.frame ram sp c _ (hsep i)
  have hv0 : extend .h true (ramRead r0 ptr .h) = SignedMagnitude.input v := by
    have hh := ViewFrame.half ho 0 (by decide)
    simp only [BitVec.add_zero] at hh
    rw [hh];exact hv
  obtain ⟨a,ta,apc,asp,ar,ac⟩ := E5R.Thermostat.I16Save.contract_quiet B c ram sp hp hsp hst hsa
  obtain ⟨b,tb,bpc,b8,b13,b10,b15,b11,b12,b14,b16,br,bc⟩ := E5R.Thermostat.I16Magnitude.contract_quiet B a r0 sp ptr fmt v asp
    ((ar 10 (by decide)).trans h10) ((ar 11 (by decide)).trans h11) hm ha hv0 apc
  have bsp : b.get 2 = sp := (br 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans asp
  obtain ⟨u,tu,upc,u15,ur,uc⟩ := E5R.Thermostat.I16OneEntry.contract_quiet B b r0 n hn b14 b16 bpc
  have usp : u.get 2 = sp := (ur 2 (by decide)).trans bsp
  have u10 : u.get 10 = SignedMagnitude.input v := (ur 10 (by decide)).trans b10
  have u11 : u.get 11 = BitVec.ofNat 32 n := (ur 11 (by decide)).trans b11
  obtain ⟨z,tz,zpc,z14,z12,z15,zr,zc⟩ := E5R.Thermostat.I16OneLeading.contract_quiet B u r0 v hn u10 u11 upc
  have zsp : z.get 2 = sp := (zr 2 (by decide) (by decide) (by decide)).trans usp
  have z11 : z.get 11 = BitVec.ofNat 32 n := (zr 11 (by decide) (by decide) (by decide)).trans u11
  have hb : ReadBytes.Byte B img r0 ((0x80005e10#32+BitVec.ofNat 32 (2*n))+1#32) (DecimalDigits.digit n) := by
    have ht := DigitTable.byte B r0 ⟨n,by omega⟩ true (hrom ⟨n,by omega⟩)
    simpa only [DigitTable.address,ite_true,Nat.mod_eq_of_lt hn0,DecimalDigits.digit,BitVec.ofNat_add,BitVec.add_assoc] using ht
  obtain ⟨w,tw,wpc,w11,w12,w14,wr,wc⟩ := E5R.Thermostat.I16LeadingPrepare.contract_quiet B z r0 sp n 5 hn (by decide) (by decide) zsp z11 z14 hb zpc
  have wsp : w.get 2 = sp := (wr 2 (by decide) (by decide) (by decide)).trans zsp
  let x := w.goto 0x80004f6a#32
  have tx : Quiet.Step B img ⟨w,r0⟩ ⟨x,memory ram sp c v⟩ :=
    E5R.Thermostat.I16DigitStore.contract_quiet B w r0 sp n 5 wpc w11 w12 hn (by decide) (by decide) hst
  have x10 : x.get 10 = SignedMagnitude.input v :=
    (wr 10 (by decide) (by decide) (by decide)).trans ((zr 10 (by decide) (by decide) (by decide)).trans u10)
  have x13 : x.get 13 = fmt := (wr 13 (by decide) (by decide) (by decide)).trans
    ((zr 13 (by decide) (by decide) (by decide)).trans ((ur 13 (by decide)).trans b13))
  obtain ⟨d,td,dpc,d10,d15,d12,d11,d14,d13,d1,dr,dc⟩ := E5R.Thermostat.I16PadCall.contract_quiet B x (memory ram sp c v) sp fmt v 4 (by decide) wsp x10 x13 w14 rfl
  refine ⟨d,(((((ta.trans tb).trans tu).trans tz).trans tw).trans (.single tx)).trans td,?_,?_,?_,?_⟩
  · refine ⟨dpc,?_,d1,d10,d11,d12,d13,?_,d15,?_,?_⟩
    · exact (dr 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans wsp
    · simpa only [BitVec.add_assoc,show 3#32+BitVec.ofNat 32 4 = 7#32 by decide +kernel] using d14
    · exact (((((dc.trans wc).trans zc).trans uc).trans bc).trans ac)
    · intro reg hr
      have hl (q : Reg) (hq : q.val < 18) (h9 : q ≠ 9) : reg ≠ q := by
        intro he
        have hv := congrArg Fin.val he
        rcases hr with hr | hr
        · exact h9 (he.symm.trans hr)
        · omega
      exact (dr reg (hl 10 (by decide) (by decide)) (hl 15 (by decide) (by decide)) (hl 12 (by decide) (by decide))
        (hl 11 (by decide) (by decide)) (hl 14 (by decide) (by decide)) (hl 13 (by decide) (by decide)) (hl 1 (by decide) (by decide))).trans
        ((wr reg (hl 11 (by decide) (by decide)) (hl 12 (by decide) (by decide)) (hl 14 (by decide) (by decide))).trans
        ((zr reg (hl 14 (by decide) (by decide)) (hl 12 (by decide) (by decide)) (hl 15 (by decide) (by decide))).trans
        ((ur reg (hl 15 (by decide) (by decide))).trans
        ((br reg (hl 8 (by decide) (by decide)) (hl 13 (by decide) (by decide)) (hl 10 (by decide) (by decide))
          (hl 15 (by decide) (by decide)) (hl 11 (by decide) (by decide)) (hl 12 (by decide) (by decide))
          (hl 14 (by decide) (by decide)) (hl 16 (by decide) (by decide))).trans (ar reg (hl 2 (by decide) (by decide)))))))
  · rw [DecimalDigits.one n hn]
    apply ReadBytes.of_ram
    apply Bytes.of_block
    · exact Memory.sub_block hst (off := 7) (m := 1) (by decide) (by decide)
    · change 1 < 2^32;decide
    · intro i
      have hi : i.val = 0 := by have := i.isLt;change i.val < 1 at this;omega
      change memory ram sp c v ((sp+7#32)+BitVec.ofNat 32 i.val) = [DecimalDigits.digit n][i.val]
      simp only [hi,List.getElem_cons_zero]
      change memory ram sp c v ((sp+7#32)+0#32) = _
      rw [BitVec.add_zero];exact ramPut_eq _ _ _
  · intro i
    apply ramPut_ne
    have hi := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using Bytes.offset_ne sp (8+i.val) 7 (by omega) (by decide) (by omega)
  · intro pos hpos
    exact (ramPut_ne _ (by simpa only [BitVec.add_zero] using hpos ⟨7,by decide⟩)).trans (I16Save.frame ram sp c pos hpos)

end E5R.Thermostat.I16One
