import Projects.thermostat.MainNextArrayView
set_option autoImplicit false
namespace E5R.Thermostat.MainRequestHeadAssemble
open E5R E5R.Thermostat HttpRequestSpec

theorem contract (ram : Word → BitVec 8) (dst : Word) (head : Head) (amount : Nat)
    (kind : head.framing=.length amount) (bound : amount≤1024)
    (tag : ramRead ram dst .w=1#32) (pad : ramRead ram (dst+4#32) .w=0#32)
    (low : ramRead ram (dst+8#32) .w=BitVec.ofNat 32 amount) (high : ramRead ram (dst+12#32) .w=0#32)
    (ms : ramRead ram (dst+16#32) .w=BitVec.ofNat 32 head.method.1)
    (me : ramRead ram (dst+20#32) .w=BitVec.ofNat 32 head.method.2)
    (ts : ramRead ram (dst+24#32) .w=BitVec.ofNat 32 head.target.1)
    (te : ramRead ram (dst+28#32) .w=BitVec.ofNat 32 head.target.2)
    (array : MainNextArrayView.At ram (dst+32#32) head)
    (minor : ram (dst+296#32)=BitVec.ofNat 8 head.minor) : HeadCompletedView.At ram dst head := by
  have offset (a b : Nat) : (dst+BitVec.ofNat 32 a)+BitVec.ofNat 32 b=dst+BitVec.ofNat 32 (a+b) := by rw [BitVec.add_assoc,←BitVec.ofNat_add]
  refine ⟨?_,pad,?_,ms,me,ts,te,array.bound,?_,?_,?_,minor⟩
  · simpa only [kind,HeadCompletedView.framingTag] using tag
  · intro n selected
    have eq : n=amount := by rw [kind] at selected;cases selected;rfl
    subst n
    refine ⟨low,?_⟩
    have zero : amount/4294967296=0 := by omega
    simpa only [zero] using high
  · simpa only [offset] using array.count
  · intro i
    have source := array.headers i
    simpa only [offset] using source
  · simpa only [offset] using array.length
end E5R.Thermostat.MainRequestHeadAssemble
