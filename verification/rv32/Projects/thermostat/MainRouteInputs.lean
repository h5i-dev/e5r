import Projects.thermostat.MainRouteEnvelope
import Projects.thermostat.MainRequestInputs
import Projects.thermostat.HeaderFrame
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.MainRouteInputs
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := MainRouteEnvelope.B
abbrev sp := MainRouteEnvelope.sp
abbrev rx := MainRouteEnvelope.rx
abbrev req := sp+3312#32
abbrev entry := MainRequestInputs.entry
abbrev entries := MainRequestInputs.entries

theorem object {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainRouteEnvelope.At c ram input s head amount served close) (n : Nat) (positive : 0<n) (bound : n≤376) : Memory.Block B req n := by
  have block := Memory.sub_block (MainTransactionStable.request h.stable) (off := 0) (m := n) positive (by omega)
  simpa only [BitVec.add_zero] using block

theorem raw_length {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainRouteEnvelope.At c ram input s head amount served close) : (MainRequestSpans.raw input head amount).length=head.len+amount := by
  simp only [MainRequestSpans.raw,List.length_take,Nat.min_eq_left h.stored.available]

theorem whole {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainRouteEnvelope.At c ram input s head amount served close) : Bytes.Span B ram rx input := by
  have block : Memory.Block B rx input.length := by
    have region := Memory.sub_block h.stable.stack (off := 60436) (m := input.length) (by have := h.stored.available;have := h.stored.bounds.length.1;omega) (by have := h.stable.bound;omega)
    simpa only [show 0x80ff0000#32+60436#32=rx by decide +kernel] using region
  exact Bytes.of_block B ram rx input block (by have := h.stable.bound;omega) h.stable.bytes

theorem raw_span {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainRouteEnvelope.At c ram input s head amount served close) : Bytes.Span B ram rx (MainRequestSpans.raw input head amount) := Bytes.take_span (whole h) _

theorem table {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainRouteEnvelope.At c ram input s head amount served close) :
    HeaderInput.Table B ram (req+32#32) (MainRequestSpans.raw input head amount).length (entries head) := by
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
      change head.headers[j].ns≤head.headers[j].ne ∧ head.headers[j].ne≤head.len+amount ∧
        head.headers[j].vs≤head.headers[j].ve ∧ head.headers[j].ve≤head.len+amount
      exact ⟨by omega,by omega,d,by omega⟩

theorem headers {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainRouteEnvelope.At c ram input s head amount served close) :
    Header.Pre B ram req rx (MainRequestSpans.raw input head amount) (entries head) := by
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
    have amountBound := h.stored.bounds.content amount h.stored.kind
    change 2164255764+(head.len+amount)<4294967296
    omega
end E5R.Thermostat.MainRouteInputs

namespace E5R.Thermostat.HeaderFrame
open E5R E5R.Thermostat
/-- Header lookup reads only these336bytes; params/count may be reinitialized. -/
theorem header_fields {B before after req p raw entries} (h : Header.Pre B before req p raw entries)
    (ho : ViewFrame.Region before after req 336) (hb : ViewFrame.Region before after p raw.length) :
    Header.Pre B after req p raw entries := by
  refine ⟨h.object,h.aligned,(ViewFrame.word ho 288 (by decide)).trans h.count,
    (ViewFrame.word ho 328 (by decide)).trans h.pointer,(ViewFrame.word ho 332 (by decide)).trans h.length,
    ViewFrame.span h.bytes hb,h.positive,h.nowrap,⟨h.table.bounded,?_⟩⟩
  intro i
  apply cell (h.table.cells i)
  intro j
  have hi := i.isLt
  have hj := j.isLt
  have hn := h.table.bounded
  have hk : 32+16*i.val+j.val < 336 := by omega
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using ho ⟨32+16*i.val+j.val,hk⟩
end E5R.Thermostat.HeaderFrame
