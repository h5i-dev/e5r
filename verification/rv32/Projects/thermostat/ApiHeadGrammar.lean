import Projects.thermostat.ApiHeaderGrammar
set_option autoImplicit false
namespace E5R.Thermostat.ApiHeadGrammar
open E5R E5R.Thermostat HttpRequestSpec ApiRequestSpec ApiRequestGrammar ApiHeaderGrammar

def count (kind : Nat) (hs : List Header) : Nat :=
  (hs.filter (fun h => decide (h.kind=kind))).length
def flag (b : Bool) : Nat := if b then 1 else 0

theorem count_cons (kind : Nat) (h : Header) (hs : List Header) :
    count kind (h::hs) = count kind hs + if h.kind=kind then 1 else 0 := by
  by_cases hit : h.kind=kind <;> simp [count,hit]

structure Remaining (f : Fields) (hs : List Header) (amount : Nat) : Prop where
  host : count 1 hs + flag f.host = 1
  length : count 2 hs + flag f.hasCl = 1
  cl : f.hasCl=true → f.cl=amount
  te : f.te=false
  space : f.headers.length+hs.length≤16

theorem no_duplicate (kind : Nat) (h : Header) (hs : List Header) (b : Bool)
    (unique : count kind (h::hs)+flag b=1) (hit : h.kind=kind) : b=false := by
  rw [count_cons,ite_eq_left hit] at unique
  cases b <;> simp only [flag,Bool.false_eq_true,ite_false,ite_true] at unique ⊢ <;> omega

theorem remaining_step (f : Fields) (h : Header) (hs : List Header) (start amount : Nat)
    (r : Remaining f (h::hs) amount) : Remaining (recorded f h start amount) hs amount := by
  constructor
  · have unique := r.host
    rw [count_cons] at unique
    by_cases hit : h.kind=1 <;> cases hb : f.host <;>
      simp only [recorded,flag,hit,decide_true,decide_false,Bool.or_true,Bool.or_false,hb,ite_true,ite_false] at unique ⊢ <;> omega
  · have unique := r.length
    rw [count_cons] at unique
    by_cases hit : h.kind=2 <;> cases hb : f.hasCl <;>
      simp only [recorded,flag,hit,decide_true,decide_false,Bool.or_true,Bool.or_false,hb,ite_true,ite_false] at unique ⊢ <;> omega
  · intro cl
    by_cases hit : h.kind=2
    · simp only [recorded,hit,ite_true]
    · have previous : f.hasCl=true := by simpa only [recorded,hit,decide_false,Bool.or_false] using cl
      simpa only [recorded,hit,ite_false] using r.cl previous
  · exact r.te
  · have space := r.space
    simp only [recorded,List.length_append,List.length_cons,List.length_nil] at space ⊢
    omega

/-- Complete syntactic header lists produce exactly their computed field
    offsets, unique Host, and the declared fixed body length. -/
theorem fields_complete (g : Nat → Nat) (start cap max amount : Nat)
    (hs : List Header) (f : Fields)
    (span : Span g start (hs.flatMap Header.bytes++[13#8,10#8]))
    (valid : ∀ h∈hs, h.Valid) (noTransfer : ∀ h∈hs, h.kind≠3)
    (numeric : ∀ h∈hs, h.kind=2 → h.LengthValue amount)
    (remaining : Remaining f hs amount) (bound : amount≤max)
    (enough : start+(hs.flatMap Header.bytes).length+2≤cap) :
    fields g cap 1 max start f = .done
      ⟨f.headers++fieldsAt hs start,true,true,amount,false⟩
      (start+(hs.flatMap Header.bytes).length+2) := by
  induction hs generalizing start f with
  | nil =>
    have ending := line_complete g start cap [] span (by simp) (by simpa using enough)
    simp only [List.length_nil,Nat.add_zero] at ending
    have state : f = ⟨f.headers,true,true,amount,false⟩ := by
      have host := remaining.host
      have length := remaining.length
      have te := remaining.te
      have cl := remaining.cl
      simp only [count,List.filter_nil,List.length_nil,Nat.zero_add,flag] at host length
      cases f with
      | mk headers hb cb cv tb =>
        cases hb <;> cases cb <;> simp_all
    rw [fields]
    simp only [List.flatMap_nil,List.length_nil,Nat.add_zero] at enough ⊢
    simp only [show start<cap by omega,ite_true,ending.1,ending.2,
      show ¬(0=1) by decide,show ¬(0=2) by decide,ite_false,
      fieldsAt,List.append_nil]
    rw [state]
  | cons h hs ih =>
    have pieces : Span g start (h.bytes++(hs.flatMap Header.bytes++[13#8,10#8])) := by
      simpa only [List.flatMap_cons,List.append_assoc] using span
    have firstSpan := span_left pieces
    have restSpan := span_right pieces
    have firstValid := valid h (by simp)
    have lineSpan : Span g start (ApiHeaderGrammar.Header.line h++[13#8,10#8]) := by
      rw [←header_line_bytes]; exact firstSpan
    have firstEnough : start+(ApiHeaderGrammar.Header.line h).length+2≤cap := by
      rw [List.flatMap_cons,List.length_append] at enough
      have size : h.bytes.length=(ApiHeaderGrammar.Header.line h).length+2 := by
        rw [header_line_bytes,List.length_append]; rfl
      omega
    have ending := line_complete g start cap (ApiHeaderGrammar.Header.line h) lineSpan
      (header_line_chars h firstValid) firstEnough
    have endpoint : start+(ApiHeaderGrammar.Header.line h).length = start+h.bytes.length-2 := by
      rw [header_line_bytes,List.length_append]
      simp only [List.length_cons,List.length_nil]; omega
    have nonempty : start ≠ start+(ApiHeaderGrammar.Header.line h).length := by
      have positive := List.length_pos_iff.mpr firstValid.1
      simp only [ApiHeaderGrammar.Header.line,List.length_append,List.length_cons,List.length_nil]
      omega
    have parseLine := header_line g start h firstValid firstSpan
    rw [←endpoint] at parseLine
    have action := add_header g start h f amount max firstSpan
      (by have := remaining.space; simp only [List.length_cons,maxHeaders] at *; omega)
      (no_duplicate 1 h hs f.host remaining.host)
      (no_duplicate 2 h hs f.hasCl remaining.length)
      (noTransfer h (by simp)) remaining.te (numeric h (by simp)) bound
    rw [←endpoint] at action
    have next := ih (start+h.bytes.length) (recorded f h start amount) restSpan
      (fun x hx => valid x (by simp [hx])) (fun x hx => noTransfer x (by simp [hx]))
      (fun x hx => numeric x (by simp [hx])) (remaining_step f h hs start amount remaining)
      (by rw [List.flatMap_cons,List.length_append] at enough; omega)
    rw [fields]
    simp only [show start<cap by omega,ite_true,ending.1,ending.2,
      show ¬(0=1) by decide,show ¬(0=2) by decide,ite_false,Ne.symm nonempty,parseLine,action]
    have advance : start+(ApiHeaderGrammar.Header.line h).length+2 = start+h.bytes.length := by
      rw [header_line_bytes,List.length_append]; rfl
    rw [advance,next]
    simp only [recorded,fieldsAt,List.flatMap_cons,List.length_append,List.append_assoc,List.singleton_append,Nat.add_assoc]

end E5R.Thermostat.ApiHeadGrammar
