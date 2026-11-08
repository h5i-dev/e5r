import Projects.thermostat.MainRequestSpans
import Projects.thermostat.Header
import Projects.thermostat.PathDispatch
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.MainRequestInputs
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := MainRequestBuild.B
abbrev sp := MainRequestBuild.sp
abbrev rx := MainRequestBuild.rx
abbrev req := sp+3312#32

def entry (field : Field) : HeaderSpec.Entry := ⟨field.ns,field.ne,field.vs,field.ve⟩
def entries (head : Head) := head.headers.map entry

theorem object {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat}
    (h : MainRequestBuild.Ready c ram input s head amount served) (n : Nat) (positive : 0<n) (bound : n≤376) : Memory.Block B req n := by
  have block := Memory.sub_block (MainTransactionStable.request h.stable) (off := 0) (m := n) positive (by omega)
  simpa only [BitVec.add_zero] using block

theorem path {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat}
    (h : MainRequestBuild.Ready c ram input s head amount served) :
    PathDispatch.PathAt B ram req (rx+BitVec.ofNat 32 head.target.1) (MainRequestSpans.path input head) := by
  refine ⟨object h 312 (by decide) (by decide),by decide +kernel,?_,?_,MainRequestSpans.path_span h⟩
  · change ramRead ram ((sp+3312#32)+304#32) .w=_
    rw [BitVec.add_assoc,show 3312#32+304#32=3616#32 by decide +kernel]
    exact h.request.path
  · change ramRead ram ((sp+3312#32)+308#32) .w=_
    rw [BitVec.add_assoc,show 3312#32+308#32=3620#32 by decide +kernel,MainRequestSpans.path_length h]
    exact h.request.pathLength

theorem table {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat}
    (h : MainRequestBuild.Ready c ram input s head amount served) :
    HeaderInput.Table B ram (req+32#32) (MainRequestSpans.raw input head amount).length (entries head) := by
  refine ⟨?_,?_⟩
  · simpa only [entries,List.length_map] using h.headView.count_bound
  · intro i
    have hi : i.val<head.headers.length := by simpa only [entries,List.length_map] using i.isLt
    let j : Fin head.headers.length := ⟨i.val,hi⟩
    have stored := h.headView.headers j
    have e : (entries head)[i]=entry head.headers[j] := by
      have hm : i.val<(head.headers.map entry).length := by simpa only [List.length_map] using hi
      change ((head.headers.map entry)[i.val]'(hm))=entry (head.headers[i.val]'(hi))
      rw [List.getElem_map]
    let cell := (req+32#32)+BitVec.ofNat 32 (16*i.val)
    have small : i.val<16 := Nat.lt_of_lt_of_le hi h.headView.count_bound
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
      have field := h.contained.2 head.headers[j] (List.getElem_mem hi)
      rcases field with ⟨a,b,d,f⟩
      rw [MainRequestSpans.raw_length h]
      change head.headers[j].ns≤head.headers[j].ne ∧ head.headers[j].ne≤head.len+amount ∧
        head.headers[j].vs≤head.headers[j].ve ∧ head.headers[j].ve≤head.len+amount
      exact ⟨by omega,by omega,d,by omega⟩

theorem headers {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat}
    (h : MainRequestBuild.Ready c ram input s head amount served) :
    Header.Pre B ram req rx (MainRequestSpans.raw input head amount) (entries head) := by
  refine ⟨object h 336 (by decide) (by decide),by decide +kernel,?_,?_,?_,MainRequestSpans.raw_span h,by decide +kernel,?_,table h⟩
  · simpa only [entries,List.length_map] using h.headView.count
  · change ramRead ram ((sp+3312#32)+328#32) .w=_
    rw [BitVec.add_assoc,show 3312#32+328#32=3640#32 by decide +kernel]
    exact h.request.raw
  · change ramRead ram ((sp+3312#32)+332#32) .w=_
    rw [BitVec.add_assoc,show 3312#32+332#32=3644#32 by decide +kernel,MainRequestSpans.raw_length h]
    exact h.request.rawLength
  · rw [MainRequestSpans.raw_length h]
    have bound := h.bounds.length.2
    have amountBound := h.bounds.content amount h.kind
    change 2164255764+(head.len+amount)<4294967296
    omega
end E5R.Thermostat.MainRequestInputs
