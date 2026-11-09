import Projects.thermostat.MainRouterCode
import Projects.thermostat.QuietBranch
import Projects.thermostat.Memory
set_option autoImplicit false
namespace E5R.Thermostat.RouteSliceGuards
open E5R E5R.Thermostat

theorem lt_false (first last : Nat) (order : first≤last) (bound : last≤2048) :
    taken .ltu (BitVec.ofNat 32 last) (BitVec.ofNat 32 first)=false := by
  simp only [taken,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show last<2^32 by omega),
    Nat.mod_eq_of_lt (show first<2^32 by omega)]
  exact decide_eq_false (by omega)

/-- All four actual slice-panic branches fall through when scan-derived
    endpoints are ordered and inside their independently allocated slices. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (ps pe plen ss se slen : Nat)
    (pat : ps≤pe ∧ pe≤plen ∧ plen≤2048) (path : ss≤se ∧ se≤slen ∧ slen≤2048)
    (hp : c.pc=0x800028a8#32) (h22 : c.get 22=BitVec.ofNat 32 pe) (h11 : c.get 11=BitVec.ofNat 32 ps)
    (h18 : c.get 18=BitVec.ofNat 32 plen) (h23 : c.get 23=BitVec.ofNat 32 se)
    (h10 : c.get 10=BitVec.ofNat 32 ss) (h9 : c.get 9=BitVec.ofNat 32 slen) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800028b8#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,ta,pa,ar,ac⟩ := QuietBranch.contract B img c ram 0x800028a8#32 4#32 178#32 .ltu 22 11 false
    hp (by decide) (by decide) rt2147494056 (by rw [h22,h11];exact lt_false ps pe pat.1 (by omega))
  have ap : a.pc=0x800028ac#32 := by simpa only [Bool.false_eq_true,ite_false,show 0x800028a8#32+4#32=0x800028ac#32 by decide +kernel] using pa
  obtain ⟨b,tb,pb,br,bc⟩ := QuietBranch.contract B img a ram 0x800028ac#32 4#32 174#32 .ltu 18 22 false
    ap (by decide) (by decide) rt2147494060 (by rw [ar 18,ar 22,h18,h22];exact lt_false pe plen pat.2.1 pat.2.2)
  have bp : b.pc=0x800028b0#32 := by simpa only [Bool.false_eq_true,ite_false,show 0x800028ac#32+4#32=0x800028b0#32 by decide +kernel] using pb
  obtain ⟨d,td,pd,dr,dc⟩ := QuietBranch.contract B img b ram 0x800028b0#32 4#32 192#32 .ltu 23 10 false
    bp (by decide) (by decide) rt2147494064 (by rw [br 23,br 10,ar 23,ar 10,h23,h10];exact lt_false ss se path.1 (by omega))
  have dp : d.pc=0x800028b4#32 := by simpa only [Bool.false_eq_true,ite_false,show 0x800028b0#32+4#32=0x800028b4#32 by decide +kernel] using pd
  obtain ⟨e,te,pe,er,ec⟩ := QuietBranch.contract B img d ram 0x800028b4#32 4#32 188#32 .ltu 9 23 false
    dp (by decide) (by decide) rt2147494068 (by rw [dr 9,dr 23,br 9,br 23,ar 9,ar 23,h9,h23];exact lt_false se slen path.2.1 path.2.2)
  refine ⟨e,((ta.trans tb).trans td).trans te,?_,fun r => (er r).trans ((dr r).trans ((br r).trans (ar r))),ec.trans (dc.trans (bc.trans ac))⟩
  simpa only [Bool.false_eq_true,ite_false,show 0x800028b4#32+4#32=0x800028b8#32 by decide +kernel] using pe
end E5R.Thermostat.RouteSliceGuards
