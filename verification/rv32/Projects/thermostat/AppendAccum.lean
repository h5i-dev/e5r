import Projects.thermostat.BytesAppend
import Projects.thermostat.AppendPost
namespace E5R.Thermostat.AppendPost
open E5R E5R.Thermostat

/-- A checked append cannot alter an earlier output prefix. This is a proved
    frame consequence, not an assumed summary of the formatting callbacks. -/
theorem accumulates {B c d before after sp obj dst scratch cap xs ys}
    (h : Post B c d before after sp obj dst scratch cap xs.length ys)
    (hm : Memory.Block B dst cap) (hc : cap < 2^32) (hf : xs.length+ys.length ≤ cap)
    (hs : WordRegions.Disjoint dst cap sp scratch) (ho : WordRegions.Disjoint obj 12 dst cap)
    (hx : Bytes.Span B before dst xs) : Bytes.Span B after dst (xs++ys) := by
  apply Bytes.append_of_block hm hc hf _ (h.written hf)
  apply ViewFrame.span hx
  intro i
  have hi := i.isLt
  apply h.frame _ (hs ⟨i.val,by omega⟩)
  · intro j
    have hj := j.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using Bytes.offset_ne dst i.val (xs.length+j.val) (by omega) (by omega) (by omega)
  · intro j
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using Ne.symm (ho ⟨8+j.val,by have := j.isLt;omega⟩ ⟨i.val,by omega⟩)
end E5R.Thermostat.AppendPost
