import Projects.thermostat.HeadFieldsWhole
import Projects.thermostat.HeadFieldsCongr
import Projects.thermostat.HeadRequestSuccess
import Projects.thermostat.HeadRequestInputStorage
namespace E5R.Thermostat.HeadColdSpec
open E5R E5R.Thermostat HttpRequestSpec

def inputBytes (input : List (BitVec 8)) := window (HttpRequestBytes.bytes input) (min input.length 1024)

theorem bad (input : List (BitVec 8)) (status : Nat) (complete : HeadByteInput.term input=0)
    (request : HeadRequestInputStorage.request input=.bad status) : HttpRequestBytes.parse input 1024 1024=.reject status := by
  unfold HttpRequestBytes.parse parseHead
  rw [HeadByteInput.read_limit]
  change (if HeadByteInput.term input=1 then _ else if HeadByteInput.term input=2 then _ else _)=_
  rw [complete]
  simp only [show ¬(0=1) by decide,show ¬(0=2) by decide,ite_false]
  change (match HeadRequestInputStorage.request input with | .bad s => HeadR.reject s | .ok _ _ _ _ _ => _)=_
  rw [request]

theorem good (input : List (BitVec 8)) (ms me ts te minor : Nat) (complete : HeadByteInput.term input=0)
    (request : HeadRequestInputStorage.request input=.ok ms me ts te minor) :
    HttpRequestBytes.parse input 1024 1024=HeadFieldsFinish.result input.length me (me+1) te minor
      (fields (inputBytes input) (min input.length 1024) minor 1024 (HeadRequestInputStorage.line input+2) Fields.empty) := by
  have shape := HeadRequestSuccess.shape (inputBytes input) (HeadRequestInputStorage.line input) ms me ts te minor request
  obtain ⟨rfl,rfl,version⟩ := shape
  unfold HttpRequestBytes.parse parseHead
  rw [HeadByteInput.read_limit]
  change (if HeadByteInput.term input=1 then _ else if HeadByteInput.term input=2 then _ else _)=_
  rw [complete]
  simp only [show ¬(0=1) by decide,show ¬(0=2) by decide,ite_false]
  change (match HeadRequestInputStorage.request input with | .bad s => HeadR.reject s | .ok _ _ _ _ _ => _)=_
  rw [request]
  dsimp only
  change (match fields (inputBytes input) (min input.length 1024) minor 1024 (HeadRequestInputStorage.line input+2) Fields.empty with
    | .more => _ | .bad status => _ | .done f len => _)=_
  cases parsed : fields (inputBytes input) (min input.length 1024) minor 1024 (HeadRequestInputStorage.line input+2) Fields.empty with
  | more =>
    simp only [HeadFieldsFinish.result,HeadFieldsMore.out,HttpRequestBytes.bytes,List.length_map,decide_eq_true_eq]
  | bad status => rfl
  | done f len =>
    change (if minor=1 ∧ (!f.host)=true then HeadR.reject 400 else _) = HeadFinalResult.result me (me+1) te len minor f
    cases host : f.host <;> simp only [host,Bool.not_true,Bool.not_false,Bool.false_eq_true,Bool.true_eq_false,and_true,and_false,ite_false,HeadFinalResult.result,HeadCompletedView.head]
end E5R.Thermostat.HeadColdSpec
