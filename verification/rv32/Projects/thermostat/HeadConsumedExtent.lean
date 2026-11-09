import Projects.thermostat.HeadFieldsCongr
import Projects.thermostat.HeadRequestCongr
import Projects.thermostat.MainHeadAcceptedBounds
import Projects.thermostat.MainHeaderStreamSpec
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HeadConsumedExtent
open E5R E5R.Thermostat HttpRequestSpec

/-- A successful field scan consumes an empty CRLF after its starting index. -/
theorem fields_lower (g : Nat → Nat) (cap minor max i len : Nat) (f result : Fields)
    (done : fields g cap minor max i f=.done result len) : i+2≤len := by
  rw [fields] at done
  split at done
  · dsimp only at done
    split at done
    · cases done
    · split at done
      · cases done
      · split at done
        · cases done
          have := scan_ge notEol g i cap
          change i+2≤lineEnd g i cap+2
          omega
        · cases hp : headerLine g i (lineEnd g i cap) with
          | bad status => simp only [hp] at done;cases done
          | ok ne vs ve =>
            simp only [hp] at done
            cases ha : addHeader g f i ne vs ve (lineEnd g i cap) minor max with
            | bad status => simp only [ha] at done;cases done
            | ok next =>
              simp only [ha] at done
              have lower := fields_lower g cap minor max (lineEnd g i cap+2) len next result done
              have := scan_ge notEol g i cap
              change i≤lineEnd g i cap at this
              omega
  · cases done
termination_by cap-i
decreasing_by have := scan_ge notEol g i cap;unfold lineEnd at *;omega

/-- A scan that already stopped before the smaller limit reads no removed
    bytes. The byte functions need agree only below that smaller limit. -/
theorem scan_prefix (p : Nat → Bool) (g h : Nat → Nat) (i cap small : Nat)
    (limits : small≤cap) (stopped : scan p g i cap<small)
    (agree : ∀ k, k<small → g k=h k) : scan p h i small=scan p g i cap := by
  have lower := scan_ge p g i cap
  have inside : i<small := by omega
  conv => lhs;rw [scan]
  conv => rhs;rw [scan]
  simp only [inside,show i<cap by omega,ite_true,←agree i inside]
  cases hp : p (g i) with
  | false => simp only [Bool.false_eq_true,ite_false]
  | true =>
    simp only [ite_true]
    have next : scan p g (i+1) cap<small := by
      rw [scan,ite_eq_left (by omega),ite_eq_left hp] at stopped
      exact stopped
    exact scan_prefix p g h (i+1) cap small limits next agree
termination_by cap-i

/-- Resizing after a complete CRLF preserves line-termination classification. -/
theorem term_prefix (g h : Nat → Nat) (j cap small : Nat) (limits : small≤cap)
    (enough : j+2≤small) (agree : ∀ k, k<small → g k=h k) :
    lineTerm h j small=lineTerm g j cap := by
  simp only [lineTerm,show ¬small≤j by omega,show ¬cap≤j by omega,ite_false,
    ←agree j (by omega),←agree (j+1) (by omega),show ¬small≤j+1 by omega,show ¬cap≤j+1 by omega]
/-- The first successful field line ends before the complete head ends. -/
theorem fields_line (g : Nat → Nat) (cap minor max i len : Nat) (f result : Fields)
    (done : fields g cap minor max i f=.done result len) : lineEnd g i cap+2≤len := by
  rw [fields] at done
  split at done
  · dsimp only at done
    split at done
    · cases done
    · split at done
      · cases done
      · split at done
        · cases done;exact Nat.le_refl _
        · cases hp : headerLine g i (lineEnd g i cap) with
          | bad status => simp only [hp] at done;cases done
          | ok ne vs ve =>
            simp only [hp] at done
            cases ha : addHeader g f i ne vs ve (lineEnd g i cap) minor max with
            | bad status => simp only [ha] at done;cases done
            | ok next =>
              simp only [ha] at done
              have lower := fields_lower g cap minor max (lineEnd g i cap+2) len next result done
              omega
  · cases done

/-- Completed fields are unchanged when removing only bytes past their end. -/
theorem fields_prefix (g h : Nat → Nat) (cap small minor max i len : Nat) (f result : Fields)
    (done : fields g cap minor max i f=.done result len)
    (limits : len≤small ∧ small≤cap) (agree : ∀ k, k<small → g k=h k) :
    fields h small minor max i f=.done result len := by
  have first := fields_line g cap minor max i len f result done
  have lower := fields_lower g cap minor max i len f result done
  have line : lineEnd h i small=lineEnd g i cap := scan_prefix notEol g h i cap small limits.2 (by change lineEnd g i cap<small;omega) agree
  have term := term_prefix g h (lineEnd g i cap) cap small limits.2 (by omega) agree
  rw [fields,ite_eq_left (by omega : i<small)]
  dsimp only
  rw [line,term]
  rw [fields,ite_eq_left (by omega : i<cap)] at done
  dsimp only at done
  split at done
  · cases done
  · rename_i notMore
    rw [ite_eq_right notMore]
    split at done
    · cases done
    · rename_i notBad
      rw [ite_eq_right notBad]
      split at done
      · rename_i empty
        rw [ite_eq_left empty]
        exact done
      · rename_i nonempty
        rw [ite_eq_right nonempty]
        rw [←HeadFieldCongr.header_congr g h i (lineEnd g i cap) (fun k hk => agree k (by omega))]
        cases hp : headerLine g i (lineEnd g i cap) with
        | bad status => simp only [hp] at done;cases done
        | ok ne vs ve =>
          simp only [hp] at done ⊢
          have shape := HeadFieldsInputCongr.header_bounds g i (lineEnd g i cap) ne vs ve hp
          have action := HeadActionCongr.action_congr g h f i ne vs ve (lineEnd g i cap) minor max small (by omega) (by omega) agree
          have added : addHeader h f i ne vs ve (lineEnd g i cap) minor max=addHeader g f i ne vs ve (lineEnd g i cap) minor max := by
            simp only [HeadActionSpec.factor,←action]
          rw [added]
          cases ha : addHeader g f i ne vs ve (lineEnd g i cap) minor max with
          | bad status => simp only [ha] at done;cases done
          | ok next =>
            simp only [ha] at done ⊢
            exact fields_prefix g h cap small minor max (lineEnd g i cap+2) len next result done limits agree
termination_by cap-i
decreasing_by have := scan_ge notEol g i cap;unfold lineEnd at *;omega
/-- The parser's successful head already parses at its exact consumed end;
    later bytes are not needed to establish that same result. -/
theorem parse_prefix (L : List Nat) (maxHead maxBody : Nat) (head : Head)
    (done : parseHead L maxHead maxBody=.done head) :
    parseHead (L.take head.len) maxHead maxBody=.done head := by
  have bounds := MainHeadAcceptedBounds.accepted L maxHead maxBody head done
  have limits := MainHeadAcceptedBounds.limit L.length maxHead
  let cap := readLimit L.length maxHead
  let g := window L cap
  let j := lineEnd g 0 cap
  let short := window (L.take head.len) head.len
  have truncatedCap : readLimit (L.take head.len).length maxHead=head.len := by
    have hl : head.len≤L.length := Nat.le_trans bounds.length.2 limits.1
    have hm : head.len≤maxHead := Nat.le_trans bounds.length.2 limits.2
    rw [List.length_take,Nat.min_eq_left hl]
    unfold readLimit
    split <;> omega
  have agree : ∀ k, k<head.len → g k=short k := by
    intro k hk
    have kc : k<cap := Nat.lt_of_lt_of_le hk bounds.length.2
    simp only [g,short,window,kc,hk,ite_true,List.getD,List.getElem?_take_of_lt hk]
  unfold parseHead at done
  dsimp only at done
  split at done
  · split at done <;> cases done
  · rename_i notMore
    split at done
    · cases done
    · rename_i notBad
      cases req : requestLine g 0 j with
      | bad status => rw [req] at done;cases done
      | ok ms me ts te minor =>
        rw [req] at done
        dsimp only at done
        cases found : fields g cap minor maxBody (j+2) Fields.empty with
        | more => rw [found] at done;dsimp only at done;split at done <;> cases done
        | bad status => rw [found] at done;cases done
        | done f len =>
          rw [found] at done
          dsimp only at done
          split at done
          · cases done
          · rename_i host
            cases done
            have first := fields_lower g cap minor maxBody (j+2) len Fields.empty f found
            have line : lineEnd short 0 len=j := scan_prefix notEol g short 0 cap len bounds.length.2 (by change j<len;omega) agree
            have term := term_prefix g short j cap len bounds.length.2 (by omega) agree
            have request := HeadRequestCongr.requestLine g short j (fun k hk => agree k (by change k<len;omega))
            have headers := fields_prefix g short cap len minor maxBody (j+2) len Fields.empty f found ⟨Nat.le_refl _,bounds.length.2⟩ agree
            unfold parseHead
            dsimp only
            rw [truncatedCap]
            change (if lineTerm short (lineEnd short 0 len) len=1 then _ else if lineTerm short (lineEnd short 0 len) len=2 then _ else _)=_
            rw [line,term]
            change (if lineTerm g j cap=1 then _ else if lineTerm g j cap=2 then _ else _)=_
            rw [ite_eq_right notMore,ite_eq_right notBad,←request,req]
            dsimp only
            rw [headers]
            dsimp only
            exact ite_eq_right host
theorem bytes_prefix (input : List (BitVec 8)) (head : Head)
    (done : HttpRequestBytes.parse input 1024 1024=.done head) :
    HttpRequestBytes.parse (input.take head.len) 1024 1024=.done head := by
  simpa only [HttpRequestBytes.parse,HttpRequestBytes.bytes,List.map_take] using
    parse_prefix (HttpRequestBytes.bytes input) 1024 1024 head done

theorem arrivals_take (wire : Nat → BitVec 8) (first count small : Nat) (bound : small≤count) :
    (MainHeaderStreamSpec.arrivals wire first count).take small=MainHeaderStreamSpec.arrivals wire first small := by
  apply List.ext_getElem
  · simp only [MainHeaderStreamSpec.arrivals,List.length_take,List.length_map,List.length_range,Nat.min_eq_left bound]
  · intro i hi hj
    simp only [MainHeaderStreamSpec.arrivals,List.getElem_take,List.getElem_map,List.getElem_range]

/-- Before the consumer's first terminal result, each earlier receive budget
    ends at its incomplete boundary. No wire grammar or fixture is assumed. -/
theorem prior (wire : Nat → BitVec 8) (fuel k : Nat) (input : List (BitVec 8))
    (inside : k<(MainHeaderStreamSpec.consume wire fuel input).received) :
    (MainHeaderStreamSpec.consume wire k input).result=.incomplete := by
  induction fuel generalizing input k with
  | zero => simp only [MainHeaderStreamSpec.consume] at inside;omega
  | succ fuel ih =>
    cases k with
    | zero => rfl
    | succ k =>
      rw [MainHeaderStreamSpec.consume] at inside ⊢
      dsimp only at inside ⊢
      cases parsed : HttpRequestBytes.parse (input++[wire input.length]) 1024 1024 with
      | incomplete =>
        rw [parsed] at inside
        dsimp only at inside ⊢
        exact ih k _ (by omega)
      | reject status => rw [parsed] at inside;dsimp only at inside;omega
      | done head => rw [parsed] at inside;dsimp only at inside;omega

/-- One-byte UART reception stops exactly at the consumed successful head
    extent, for every accepted head and every wire. This discharges the generic
    empty/chunked entry's zero buffered-body premise from the upstream parser. -/
theorem receive_exact (wire : Nat → BitVec 8) (fuel : Nat) (head : Head)
    (accepted : (MainHeaderStreamSpec.consume wire fuel []).result=.done head) :
    (MainHeaderStreamSpec.consume wire fuel []).input.length=head.len := by
  have empty : HttpRequestBytes.parse [] 1024 1024=.incomplete := by decide +kernel
  have parsed := MainHeaderStreamSpec.exact_result wire fuel [] empty
  rw [accepted] at parsed
  have bounds := MainHeadAcceptedBounds.bytes _ head parsed.symm
  have size := MainHeaderStreamSpec.input_length wire fuel []
  simp only [List.length_nil,Nat.zero_add] at size
  by_cases different : (MainHeaderStreamSpec.consume wire fuel []).input.length=head.len
  · exact different
  apply False.elim
  have shorter : head.len<(MainHeaderStreamSpec.consume wire fuel []).received := by
    have := bounds.length.2
    have := Nat.min_le_left (MainHeaderStreamSpec.consume wire fuel []).input.length 1024
    omega
  have waiting := prior wire fuel head.len [] shorter
  have smallCount := MainHeaderStreamSpec.exhausted wire head.len [] waiting
  have smallInput := MainHeaderStreamSpec.input_bytes wire head.len []
  rw [smallCount] at smallInput
  simp only [List.length_nil,List.nil_append] at smallInput
  have smallParsed := MainHeaderStreamSpec.exact_result wire head.len [] empty
  rw [waiting,smallInput] at smallParsed
  have truncated := bytes_prefix _ head parsed.symm
  have largeInput := MainHeaderStreamSpec.input_bytes wire fuel []
  simp only [List.length_nil,List.nil_append] at largeInput
  rw [largeInput,arrivals_take wire 0 _ head.len (by omega)] at truncated
  rw [truncated] at smallParsed
  cases smallParsed
end E5R.Thermostat.HeadConsumedExtent
