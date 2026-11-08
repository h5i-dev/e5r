-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ParamDigits
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.ParamLoopQuiet
import Projects.thermostat.ParamReturnQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.ParamDigits
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (hs : Bytes.Span B ram p xs) (hlen : 1 ≤ xs.length ∧ xs.length ≤ 10)
    (hp : c.pc = 0x800027d8#32) (h11 : c.get 11 = 0#32) (h13 : c.get 13 = 0#32)
    (h12 : c.get 12 = BitVec.ofNat 32 xs.length) (h14 : c.get 14 = p) (h10 : c.get 10 = 10#32) :
    ∃ d n, n ≤ 182 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = c.get 1 &&& ~~~1 ∧
      ParamReturn.Result d (WireSpec.parseU32 xs) ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,n,hn,ht,apc,aout,aregs,acsr⟩ := E5R.Thermostat.ParamLoop.contract_quiet B c ram p xs 0 0 hs hlen.1
    (by simpa using hlen.2) (by decide) hp h11 h13 h12 h14 h10
  have ara : a.get 1 = c.get 1 := aregs 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  by_cases hg : xs.all DecimalSpec.digit = true
  · have apc' : a.pc = 0x8000280e#32 := by simpa only [hg,ite_true] using apc
    obtain ⟨alow,ahigh,acount,aptr⟩ := aout hg
    have hnumber : DecimalSpec.number xs 0 < 10000000000 := by
      have hb := DecimalSpec.number_bound xs hg 0
      have hpw : 10^xs.length ≤ 10000000000 := Nat.pow_le_pow_right (by decide) hlen.2
      omega
    obtain ⟨d,hreturn,dpc,dtag,dregs,dcsr⟩ := E5R.Thermostat.ParamReturn.range_quiet B a ram (DecimalSpec.number xs 0) hnumber apc' ahigh
    refine ⟨d,n+2,by omega,ht.trans hreturn,?_,?_,?_,dcsr.trans acsr⟩
    · rw [dpc,ara]
    · have hguard : 1 ≤ xs.length ∧ xs.length ≤ 10 ∧ xs.all DecimalSpec.digit = true := ⟨hlen.1,hlen.2,hg⟩
      simp only [WireSpec.parseU32,ite_eq_left hguard]
      by_cases hfits : DecimalSpec.number xs 0 ≤ 4294967295
      · simp only [ite_eq_left hfits,ParamReturn.Result]
        exact ⟨by simpa only [ite_eq_left hfits] using dtag,(dregs 11 (by decide)).trans alow⟩
      · simp only [ite_eq_right hfits,ParamReturn.Result]
        simpa only [ite_eq_right hfits] using dtag
    · intro r h5 h10 h11 h12 h13 h14 h15 h16 h17
      exact (dregs r h10).trans (aregs r h5 h11 h12 h13 h14 h15 h16 h17)
  · have hg' : xs.all DecimalSpec.digit = false := Bool.eq_false_iff.mpr hg
    have apc' : a.pc = 0x800027be#32 := by simpa only [hg',Bool.false_eq_true,ite_false] using apc
    obtain ⟨d,hreturn,dpc,dnone,dregs,dcsr⟩ := E5R.Thermostat.ParamReturn.none_quiet B a ram apc'
    refine ⟨d,n+2,by omega,ht.trans hreturn,?_,?_,?_,dcsr.trans acsr⟩
    · rw [dpc,ara]
    · have hguard : ¬(1 ≤ xs.length ∧ xs.length ≤ 10 ∧ xs.all DecimalSpec.digit = true) := fun h => hg h.2.2
      simpa only [WireSpec.parseU32,ite_eq_right hguard] using dnone
    · intro r h5 h10 h11 h12 h13 h14 h15 h16 h17
      exact (dregs r h10).trans (aregs r h5 h11 h12 h13 h14 h15 h16 h17)

end E5R.Thermostat.ParamDigits
