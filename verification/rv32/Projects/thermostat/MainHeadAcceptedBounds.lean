import Projects.thermostat.MainHeadBounds
namespace E5R.Thermostat.MainHeadAcceptedBounds
open E5R E5R.Thermostat HttpRequestSpec

structure At (cap maxBody : Nat) (head : Head) : Prop where
  method : head.method.1=0 ∧ 0<head.method.2
  target : head.method.2<head.target.1 ∧ head.target.1<head.target.2 ∧ head.target.2<cap
  version : head.minor≤1
  fields : ∀ entry∈head.headers, MainHeadBounds.FieldAt cap entry
  length : 2≤head.len ∧ head.len≤cap
  content : ∀ n, head.framing=.length n → n≤maxBody

theorem limit (len maxHead : Nat) : readLimit len maxHead≤len ∧ readLimit len maxHead≤maxHead := by
  unfold readLimit
  split <;> omega

/-- Slice and body limits follow from acceptance by the independent byte
    parser. No typed command, authentication result or request span is assumed. -/
theorem accepted (input : List Nat) (maxHead maxBody : Nat) (head : Head)
    (parsed : parseHead input maxHead maxBody=.done head) : At (readLimit input.length maxHead) maxBody head := by
  let cap := readLimit input.length maxHead
  let g := window input cap
  let j := lineEnd g 0 cap
  unfold parseHead at parsed
  dsimp only at parsed
  split at parsed
  next more => split at parsed <;> cases parsed
  next notMore =>
    split at parsed
    next bad => cases parsed
    next notBad =>
      cases req : requestLine g 0 j with
      | bad status => rw [req] at parsed;cases parsed
      | ok ms me ts te minor =>
        rw [req] at parsed
        dsimp only at parsed
        have request := MainHeadBounds.request g j ms me ts te minor req
        have jBound : j≤cap := scan_le notEol g 0 cap (by omega)
        cases found : HttpRequestSpec.fields g cap minor maxBody (j+2) Fields.empty with
        | more => rw [found] at parsed;dsimp only at parsed;split at parsed <;> cases parsed
        | bad status => rw [found] at parsed;cases parsed
        | done f len =>
          rw [found] at parsed
          dsimp only at parsed
          split at parsed
          next missing => cases parsed
          next host =>
            cases parsed
            have fields := MainHeadBounds.fields g cap minor maxBody (j+2) Fields.empty f len (by intro entry impossible;cases impossible) found
            have length := HeadFieldsResultSpec.fields g cap minor maxBody (j+2) Fields.empty
            rw [found] at length
            have cl := HeadFieldsClBound.fields g cap minor maxBody (j+2) Fields.empty f len (by change 0≤maxBody;omega) found
            refine ⟨⟨request.1,request.2.1⟩,⟨request.2.2.1,request.2.2.2.1,by have := request.2.2.2.2.1;change te<cap;omega⟩,request.2.2.2.2.2,fields.2,⟨length.1,fields.1⟩,?_⟩
            intro n selected
            change (if f.te then Framing.chunked else if f.hasCl then Framing.length f.cl else Framing.empty)=.length n at selected
            cases teFlag : f.te <;> cases clFlag : f.hasCl <;> simp only [teFlag,clFlag,Bool.false_eq_true,ite_false,ite_true] at selected
            · cases selected
            · cases selected;exact cl
            · cases selected
            · cases selected

theorem bytes (input : List (BitVec 8)) (head : Head) (parsed : HttpRequestBytes.parse input 1024 1024=.done head) :
    At (min input.length 1024) 1024 head := by
  have bounds := accepted (HttpRequestBytes.bytes input) 1024 1024 head parsed
  have eq : readLimit (HttpRequestBytes.bytes input).length 1024=min input.length 1024 := by
    simp only [HttpRequestBytes.bytes,List.length_map,readLimit]
    split <;> omega
  simpa only [eq] using bounds

theorem body_total {input : List (BitVec 8)} {head : Head} (parsed : HttpRequestBytes.parse input 1024 1024=.done head)
    (n : Nat) (kind : head.framing=.length n) : head.len+n≤2048 := by
  have bounds := bytes input head parsed
  have len := bounds.length.2
  have content := bounds.content n kind
  have cap : min input.length 1024≤1024 := Nat.min_le_right _ _
  omega
end E5R.Thermostat.MainHeadAcceptedBounds
