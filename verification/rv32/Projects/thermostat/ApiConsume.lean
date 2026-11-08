import Projects.thermostat.ApiHeadPrefix
import Projects.thermostat.MainHeaderStreamSpec
set_option autoImplicit false
namespace E5R.Thermostat.ApiConsume
open E5R E5R.Thermostat HttpRequestSpec ApiRequestSpec MainHeaderStreamSpec

theorem arrivals_piece (wire : Nat → BitVec 8) (input : ApiRequestSpec.Bytes) (first count : Nat)
    (inside : first+count≤input.length)
    (agree : ∀ k (hk : k<input.length), wire k=input[k]'hk) :
    arrivals wire first count=(input.drop first).take count := by
  apply List.ext_getElem
  · simp only [arrivals,List.length_map,List.length_range,List.length_take,List.length_drop]
    exact (Nat.min_eq_left (by omega)).symm
  · intro i hi hj
    have index : first+i<input.length := by
      simp only [arrivals,List.length_map,List.length_range] at hi
      omega
    simp only [arrivals,List.getElem_map,List.getElem_range,List.getElem_take,List.getElem_drop]
    exact agree (first+i) index

theorem head_agree (r : Fixed11) (wire : Nat → BitVec 8)
    (agree : ∀ k (hk : k<r.bytes.length), wire k=r.bytes[k]'hk) :
    ∀ k (hk : k<r.headBytes.length), wire k=r.headBytes[k]'hk := by
  intro k hk
  have index : k<(r.headBytes++r.body).length := by
    rw [List.length_append]; omega
  have input : wire k=(r.headBytes++r.body)[k]'index := agree k index
  exact input.trans (List.getElem_append_left hk)


/-- Reuse the existing receive-consumer progress/extent proofs: grammar
    excludes every earlier parser result, so exactly the head is consumed. -/
theorem exact_head (r : Fixed11) (wire : Nat → BitVec 8)
    (agree : ∀ k (hk : k<r.bytes.length), wire k=r.bytes[k]'hk) :
    consume wire r.headBytes.length [] = ⟨r.headBytes.length,r.headBytes,.done r.head⟩ := by
  have header := head_agree r wire agree
  have allBytes := arrivals_piece wire r.headBytes 0 r.headBytes.length (by omega) header
  simp only [List.drop_zero,List.take_length] at allBytes
  have empty : HttpRequestBytes.parse [] 1024 1024=.incomplete := by decide +kernel
  have progress := complete_progress wire r.headBytes.length [] empty (by
    rw [List.length_nil,allBytes,List.nil_append,ApiFixedHead.accepted]
    intro impossible; cases impossible)
  have bounded := received_le wire r.headBytes.length []
  have bytes := input_bytes wire r.headBytes.length []
  simp only [List.length_nil,List.nil_append] at bytes
  have parsed := exact_result wire r.headBytes.length [] empty
  have count : (consume wire r.headBytes.length []).received=r.headBytes.length := by
    by_cases same : (consume wire r.headBytes.length []).received=r.headBytes.length
    · exact same
    apply False.elim
    have proper : (consume wire r.headBytes.length []).received<r.headBytes.length := by omega
    have piece := arrivals_piece wire r.headBytes 0 (consume wire r.headBytes.length []).received (by omega) header
    simp only [List.drop_zero] at piece
    rw [bytes,piece,ApiHeadPrefix.incomplete r _ proper] at parsed
    exact progress parsed
  rw [count,allBytes] at bytes
  rw [bytes,ApiFixedHead.accepted] at parsed
  cases run : consume wire r.headBytes.length [] with
  | mk received input result =>
    rw [run] at count bytes parsed
    dsimp only at count bytes parsed
    rw [count,bytes,parsed]

theorem delivered (r : Fixed11) (wire : Nat → BitVec 8)
    (agree : ∀ k (hk : k<r.bytes.length), wire k=r.bytes[k]'hk) :
    (consume wire r.headBytes.length []).input ++
      arrivals wire (consume wire r.headBytes.length []).input.length
        (r.head.len+r.body.length-(consume wire r.headBytes.length []).input.length) = r.bytes := by
  rw [exact_head r wire agree]
  change r.headBytes ++ arrivals wire r.headBytes.length
    (r.headBytes.length+r.body.length-r.headBytes.length) = r.headBytes++r.body
  rw [Nat.add_sub_cancel_left]
  have body := arrivals_piece wire r.bytes r.headBytes.length r.body.length
    (by simp only [Fixed11.bytes,List.length_append]; omega) agree
  simp only [Fixed11.bytes,List.drop_left,List.take_length] at body
  rw [body]

end E5R.Thermostat.ApiConsume
