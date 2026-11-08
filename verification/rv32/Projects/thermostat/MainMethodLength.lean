import Projects.thermostat.MainMethodDecodeCode
import Projects.thermostat.MainMethodSmallSetup
import Projects.thermostat.MainMethodLengthMath
import Projects.thermostat.QuietBranch
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainMethodLength
open E5R E5R.Thermostat

def destination (len : Nat) : Word :=
  if len=3 then 0x80000df6#32 else if len=4 then 0x80000d72#32
  else if len=5 then 0x80000e1a#32 else if len=6 then 0x80000db0#32 else 0x80001160#32

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (len : Nat) (bound : len≤2048)
    (hp : c.pc=0x80000d64#32) (h6 : c.get 6=4#32) (h16 : c.get 16=BitVec.ofNat 32 len)
    (h26 : c.get 26=3#32) (h17 : c.get 17=5#32) (h5 : c.get 5=6#32) :
    ∃ n d, n≤4 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=destination len ∧
      (∀ r : Reg, r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,t0,pa,ar,ac⟩ := QuietBranch.contract B img c ram 0x80000d64#32 4#32 0x44#32 .lt 6 16 (decide (4<len)) hp (by decide) (by decide) re2147487076
    (by rw [h6,h16];exact MainMethodLengthMath.ltTest 4 len (by decide) bound)
  have pa' : a.pc=(if 4<len then 0x80000da8#32 else 0x80000d68#32) := by
    simpa only [decide_eq_true_eq,show 0x80000d64#32+0x44#32=0x80000da8#32 by decide +kernel,show 0x80000d64#32+4#32=0x80000d68#32 by decide +kernel] using pa
  by_cases big : 4<len
  · have atBig : a.pc=0x80000da8#32 := by simpa only [big,ite_true] using pa'
    obtain ⟨b,t1,pb,br,bc⟩ := QuietBranch.contract B img a ram 0x80000da8#32 4#32 0x72#32 .eq 16 17 (decide (len=5)) atBig (by decide) (by decide) re2147487144
      (by rw [ar 16,ar 17,h16,h17];exact MainMethodLengthMath.eqTest len 5 bound (by decide))
    have pb' : b.pc=(if len=5 then 0x80000e1a#32 else 0x80000dac#32) := by
      simpa only [decide_eq_true_eq,show 0x80000da8#32+0x72#32=0x80000e1a#32 by decide +kernel,show 0x80000da8#32+4#32=0x80000dac#32 by decide +kernel] using pb
    by_cases five : len=5
    · refine ⟨2,b,by decide,t0.trans t1,?_,fun r _ => (br r).trans (ar r),bc.trans ac⟩
      simpa [destination,five] using pb'
    · have atSix : b.pc=0x80000dac#32 := by simpa only [five,ite_false] using pb'
      obtain ⟨d,t2,pd,dr,dc⟩ := QuietBranch.contract B img b ram 0x80000dac#32 4#32 0x3b4#32 .ne 16 5 (decide (len≠6)) atSix (by decide) (by decide) re2147487148
        (by rw [br 16,br 5,ar 16,ar 5,h16,h5];exact MainMethodLengthMath.neTest len 6 bound (by decide))
      have pd' : d.pc=(if len≠6 then 0x80001160#32 else 0x80000db0#32) := by
        simpa only [decide_eq_true_eq,show 0x80000dac#32+0x3b4#32=0x80001160#32 by decide +kernel,show 0x80000dac#32+4#32=0x80000db0#32 by decide +kernel] using pd
      refine ⟨3,d,by decide,(t0.trans t1).trans t2,?_,fun r _ => (dr r).trans ((br r).trans (ar r)),dc.trans (bc.trans ac)⟩
      by_cases six : len=6
      · simpa [destination,six] using pd'
      · have ne3 : len≠3 := by omega
        have ne4 : len≠4 := by omega
        simpa [destination,ne3,ne4,five,six] using pd'
  · have atSmall : a.pc=0x80000d68#32 := by simpa only [big,ite_false] using pa'
    obtain ⟨b,t1,pb,br,bc⟩ := QuietBranch.contract B img a ram 0x80000d68#32 4#32 0x8e#32 .eq 16 26 (decide (len=3)) atSmall (by decide) (by decide) re2147487080
      (by rw [ar 16,ar 26,h16,h26];exact MainMethodLengthMath.eqTest len 3 bound (by decide))
    have pb' : b.pc=(if len=3 then 0x80000df6#32 else 0x80000d6c#32) := by
      simpa only [decide_eq_true_eq,show 0x80000d68#32+0x8e#32=0x80000df6#32 by decide +kernel,show 0x80000d68#32+4#32=0x80000d6c#32 by decide +kernel] using pb
    by_cases three : len=3
    · refine ⟨2,b,by decide,t0.trans t1,?_,fun r _ => (br r).trans (ar r),bc.trans ac⟩
      simpa [destination,three] using pb'
    · have atFour : b.pc=0x80000d6c#32 := by simpa only [three,ite_false] using pb'
      obtain ⟨e,t2,pe,e17,er,ec⟩ := MainMethodSmallSetup.contract B b ram atFour
      obtain ⟨d,t3,pd,dr,dc⟩ := QuietBranch.contract B img e ram 0x80000d6e#32 4#32 0x3f2#32 .ne 16 17 (decide (len≠4)) pe (by decide) (by decide) re2147487086
        (by rw [er 16 (by decide),br 16,ar 16,h16,e17];exact MainMethodLengthMath.neTest len 4 bound (by decide))
      have pd' : d.pc=(if len≠4 then 0x80001160#32 else 0x80000d72#32) := by
        simpa only [decide_eq_true_eq,show 0x80000d6e#32+0x3f2#32=0x80001160#32 by decide +kernel,show 0x80000d6e#32+4#32=0x80000d72#32 by decide +kernel] using pd
      refine ⟨4,d,by decide,((t0.trans t1).trans t2).trans t3,?_,fun r h => (dr r).trans ((er r h).trans ((br r).trans (ar r))),dc.trans (ec.trans (bc.trans ac))⟩
      by_cases four : len=4
      · simpa [destination,four] using pd'
      · have ne5 : len≠5 := by omega
        have ne6 : len≠6 := by omega
        simpa [destination,three,four,ne5,ne6] using pd'
end E5R.Thermostat.MainMethodLength
