import Projects.thermostat.RuntimeRouteInputs
import Projects.thermostat.StackBoard
import Projects.thermostat.StackRuntimeApiWriteCaller
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.StackRuntimeRouteInputs
open E5R E5R.Thermostat HttpRequestSpec RuntimeRouteInputs
abbrev B := StackBoard.board
theorem object {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat} {lowValue : Word} {close : Bool}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close) (n : Nat) (positive : 0<n) (bound : n≤376) : Memory.Block B req n := by
  have block := Memory.sub_block StackBoard.available (off := 63616) (m := n) positive (by omega)
  simpa only [show 0x80ff0000#32+63616#32=req by decide +kernel] using block

theorem raw_length {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat} {lowValue : Word} {close : Bool}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close) : (RuntimeRequestSpans.raw input rawUsed).length=rawUsed := by
  simp only [RuntimeRequestSpans.raw,List.length_take,Nat.min_eq_left h.stored.usedBound.2]

theorem whole {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat} {lowValue : Word} {close : Bool}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close) : Bytes.Span B ram rx input := by
  have block : Memory.Block B rx input.length := by
    have region := Memory.sub_block StackBoard.available (off := 60436) (m := input.length) (by have := (Nat.le_trans h.stored.usedBound.1 h.stored.usedBound.2);have := h.stored.bounds.length.1;omega) (by have := h.stable.bound;omega)
    simpa only [show 0x80ff0000#32+60436#32=rx by decide +kernel] using region
  exact Bytes.of_block B ram rx input block (by have := h.stable.bound;omega) h.stable.bytes

theorem raw_span {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat} {lowValue : Word} {close : Bool}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close) : Bytes.Span B ram rx (RuntimeRequestSpans.raw input rawUsed) := Bytes.take_span (whole h) _

theorem table {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat} {lowValue : Word} {close : Bool}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close) :
    HeaderInput.Table B ram (req+32#32) (RuntimeRequestSpans.raw input rawUsed).length (entries head) := by
  refine ⟨?_,?_⟩
  · simpa only [entries,MainRequestInputs.entries,List.length_map] using h.stored.headView.count_bound
  · intro i
    have hi : i.val<head.headers.length := by simpa only [entries,MainRequestInputs.entries,List.length_map] using i.isLt
    let j : Fin head.headers.length := ⟨i.val,hi⟩
    have stored := h.stored.headView.headers j
    have e : (entries head)[i]=entry head.headers[j] := by
      have hm : i.val<(head.headers.map entry).length := by simpa only [List.length_map] using hi
      change ((head.headers.map entry)[i.val]'(hm))=entry (head.headers[i.val]'(hi))
      rw [List.getElem_map]
    let cell := (req+32#32)+BitVec.ofNat 32 (16*i.val)
    have small : i.val<16 := Nat.lt_of_lt_of_le hi h.stored.headView.count_bound
    have cellEq : cell=req+BitVec.ofNat 32 (32+16*i.val) := by
      simp only [cell,BitVec.add_assoc,←BitVec.ofNat_add]
    have cellOffset (n : Nat) : cell+BitVec.ofNat 32 n=(req+BitVec.ofNat 32 (32+n))+BitVec.ofNat 32 (16*i.val) := by
      rw [cellEq]
      simp only [req,BitVec.add_assoc,←BitVec.ofNat_add]
      apply congrArg (BitVec.ofNat 32)
      omega
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · have block := Memory.sub_block (object h 336 (by decide) (by decide)) (off := 32+16*i.val) (m := 16) (by omega) (by omega)
      change Memory.Block B cell 16
      rw [cellEq]
      exact block
    · change cell.toNat%4=0
      rw [cellEq]
      have address : 4*(8+4*i.val)=32+16*i.val := by omega
      rw [←address]
      exact Memory.word_aligned req (8+4*i.val) (by decide +kernel)
    · simp only [e,entry]
      exact stored.1
    · simp only [e,entry]
      change ramRead ram (cell+4#32) .w=BitVec.ofNat 32 head.headers[j].ne
      rw [cellOffset 4]
      exact stored.2.1
    · simp only [e,entry]
      change ramRead ram (cell+8#32) .w=BitVec.ofNat 32 head.headers[j].vs
      rw [cellOffset 8]
      exact stored.2.2.1
    · simp only [e,entry]
      change ramRead ram (cell+12#32) .w=BitVec.ofNat 32 head.headers[j].ve
      rw [cellOffset 12]
      exact stored.2.2.2
    · rw [e]
      have field := h.stored.contained.2 head.headers[j] (List.getElem_mem hi)
      rcases field with ⟨a,b,d,f⟩
      rw [raw_length h]
      change head.headers[j].ns≤head.headers[j].ne ∧ head.headers[j].ne≤rawUsed ∧
        head.headers[j].vs≤head.headers[j].ve ∧ head.headers[j].ve≤rawUsed
      have used := h.stored.usedBound.1
      exact ⟨by omega,by omega,d,by omega⟩

theorem headers {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat} {lowValue : Word} {close : Bool}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close) :
    Header.Pre B ram req rx (RuntimeRequestSpans.raw input rawUsed) (entries head) := by
  refine ⟨object h 336 (by decide) (by decide),by decide +kernel,?_,?_,?_,raw_span h,by decide +kernel,?_,table h⟩
  · simpa only [entries,MainRequestInputs.entries,List.length_map] using h.stored.headView.count
  · change ramRead ram ((sp+3312#32)+328#32) .w=_
    rw [BitVec.add_assoc,show 3312#32+328#32=3640#32 by decide +kernel]
    exact h.stored.request.raw
  · change ramRead ram ((sp+3312#32)+332#32) .w=_
    rw [BitVec.add_assoc,show 3312#32+332#32=3644#32 by decide +kernel,raw_length h]
    exact h.stored.request.rawLength
  · rw [raw_length h]
    have bound := h.stored.bounds.length.2
    have amountBound := h.stored.usedBound.2
    have inputBound := h.stable.bound
    change 2164255764+rawUsed<4294967296
    omega
end E5R.Thermostat.StackRuntimeRouteInputs
