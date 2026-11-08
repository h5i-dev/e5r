import Projects.thermostat.HeadCompletedView
namespace E5R.Thermostat.MainCopyView
open E5R E5R.Thermostat HttpRequestSpec

/-- Byte-for-byte relocation between two concrete object bases. -/
def At (before after : Word → BitVec 8) (src dst : Word) (n : Nat) : Prop :=
  ∀ i : Fin n, after (dst+BitVec.ofNat 32 i.val)=before (src+BitVec.ofNat 32 i.val)

theorem word {before after src dst n} (h : At before after src dst n) (off : Nat) (bound : off+4≤n) :
    ramRead after (dst+BitVec.ofNat 32 off) .w=ramRead before (src+BitVec.ofNat 32 off) .w := by
  have byte (k : Nat) (small : k<4) : after ((dst+BitVec.ofNat 32 off)+BitVec.ofNat 32 k)=before ((src+BitVec.ofNat 32 off)+BitVec.ofNat 32 k) := by
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using h ⟨off+k,by omega⟩
  have b0 := byte 0 (by decide)
  have b1 := byte 1 (by decide)
  have b2 := byte 2 (by decide)
  have b3 := byte 3 (by decide)
  simp only [BitVec.add_zero] at b0
  simp only [ramRead,show (1 : Word)=1#32 by decide +kernel,show (2 : Word)=2#32 by decide +kernel,show (3 : Word)=3#32 by decide +kernel,b0,b1,b2,b3]

/-- Transport every successful parser field across the real304-byte main copy.
    This includes each of the sixteen possible four-word header descriptors. -/
theorem head {before after src dst} (h : At before after src dst 304) (value : Head)
    (view : HeadCompletedView.At before src value) : HeadCompletedView.At after dst value := by
  have slot (off : Nat) (bound : off+4≤304) := word h off bound
  refine ⟨?_,(slot 4 (by decide)).trans view.padding,?_,(slot 16 (by decide)).trans view.methodStart,
    (slot 20 (by decide)).trans view.methodEnd,(slot 24 (by decide)).trans view.targetStart,(slot 28 (by decide)).trans view.targetEnd,
    view.count_bound,(slot 288 (by decide)).trans view.count,?_,(slot 292 (by decide)).trans view.length,h ⟨296,by decide⟩ |>.trans view.version⟩
  · simpa only [BitVec.add_zero] using (slot 0 (by decide)).trans (by simpa only [BitVec.add_zero] using view.tag)
  · intro n selected
    exact ⟨(slot 8 (by decide)).trans (view.framing n selected).1,(slot 12 (by decide)).trans (view.framing n selected).2⟩
  · intro i
    have bound : i.val<16 := Nat.lt_of_lt_of_le i.isLt view.count_bound
    have offset (p : Word) (k : Nat) : (p+BitVec.ofNat 32 k)+BitVec.ofNat 32 (16*i.val)=p+BitVec.ofNat 32 (k+16*i.val) := by rw [BitVec.add_assoc,←BitVec.ofNat_add]
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [offset] using (slot (32+16*i.val) (by omega)).trans (by simpa only [offset] using (view.headers i).1)
    · simpa only [offset] using (slot (36+16*i.val) (by omega)).trans (by simpa only [offset] using (view.headers i).2.1)
    · simpa only [offset] using (slot (40+16*i.val) (by omega)).trans (by simpa only [offset] using (view.headers i).2.2.1)
    · simpa only [offset] using (slot (44+16*i.val) (by omega)).trans (by simpa only [offset] using (view.headers i).2.2.2)
end E5R.Thermostat.MainCopyView
