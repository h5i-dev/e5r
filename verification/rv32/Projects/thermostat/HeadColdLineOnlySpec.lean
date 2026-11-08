import Projects.thermostat.HeadRequestInputStorage
import Projects.thermostat.HeadFieldsMore
namespace E5R.Thermostat.HeadColdLineOnlySpec
open E5R E5R.Thermostat HttpRequestSpec

def result (input : List (BitVec 8)) : HeadR :=
  match HeadRequestInputStorage.request input with
  | .bad status => .reject status
  | .ok _ _ _ _ _ => HeadFieldsMore.out input.length

/-- With a complete first line and no available header line, the independent
    full parser either rejects that first line or needs more headers/returns431. -/
theorem parsed (input : List (BitVec 8)) (complete : HeadByteInput.term input=0)
    (noHeader : min input.length 1024≤HeadRequestInputStorage.line input+2) :
    HttpRequestBytes.parse input 1024 1024=result input := by
  let n := min input.length 1024
  let g := window (HttpRequestBytes.bytes input) n
  let j := HeadRequestInputStorage.line input
  have noFields (minor : Nat) : fields g n minor 1024 (j+2) Fields.empty=.more := by
    rw [fields]
    simp only [show ¬j+2<n by omega,ite_false]
  unfold HttpRequestBytes.parse HttpRequestSpec.parseHead
  rw [HeadByteInput.read_limit]
  change (if HeadByteInput.term input=1 then _ else if HeadByteInput.term input=2 then _ else _) = _
  rw [complete]
  simp only [show ¬(0=1) by decide,show ¬(0=2) by decide,ite_false]
  change (match HeadRequestInputStorage.request input with
    | .bad status => HeadR.reject status
    | .ok _ _ _ _ minor => match fields g n minor 1024 (j+2) Fields.empty with
      | .more => if decide (1024≤(HttpRequestBytes.bytes input).length) then HeadR.reject 431 else HeadR.incomplete
      | .bad status => HeadR.reject status
      | .done f len => _) = _
  cases request : HeadRequestInputStorage.request input with
  | bad status => simp only [result,request]
  | ok ms me ts te minor =>
    dsimp only
    rw [noFields minor]
    simp only [result,request,HttpRequestBytes.bytes,List.length_map,decide_eq_true_eq,HeadFieldsMore.out]
end E5R.Thermostat.HeadColdLineOnlySpec
