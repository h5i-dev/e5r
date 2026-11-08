import Projects.thermostat.ApiRequestGrammar
set_option autoImplicit false
namespace E5R.Thermostat.ApiHeaderGrammar
open E5R E5R.Thermostat HttpRequestSpec ApiRequestSpec ApiRequestGrammar

theorem eq_from_iff (g : Nat → Nat) (start : Nat) (lit : List Nat) (q : Nat) :
    eqFrom g start lit q = true ↔
      ∀ i, q ≤ i → i < lit.length → lower (g (start+i)) = lit.getD i 0 := by
  rw [eqFrom]
  by_cases inside : q < lit.length
  · rw [ite_eq_left inside]
    by_cases equal : lower (g (start+q)) = lit.getD q 0
    · rw [ite_eq_right ((fun ne => ne equal)),eq_from_iff g start lit (q+1)]
      constructor
      · intro tail i lo hi
        by_cases first : i=q
        · simpa only [first] using equal
        · exact tail i (by omega) hi
      · intro all i lo hi
        exact all i (by omega) hi
    · rw [ite_eq_left equal]
      constructor
      · intro impossible; cases impossible
      · intro all; exact False.elim (equal (all q (by omega) inside))
  · rw [ite_eq_right inside]
    constructor
    · intro _ i lo hi; omega
    · intro _; rfl
termination_by lit.length-q

theorem eq_ci (g : Nat → Nat) (start : Nat) (xs : ApiRequestSpec.Bytes)
    (span : Span g start xs) (lit : List Nat) :
    eqCi g start (start+xs.length) lit =
      decide (xs.map (fun b => lower b.toNat) = lit) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  unfold eqCi
  have offset : start+xs.length-start = xs.length := by omega
  rw [offset]
  by_cases width : xs.length = lit.length
  · have range : ¬(start+xs.length < start ∨ xs.length ≠ lit.length) := by omega
    rw [ite_eq_right range,eq_from_iff]
    constructor
    · intro same
      apply List.ext_getElem (by simpa only [List.length_map] using width)
      intro i hleft hright
      have hi : i < xs.length := by simpa only [List.length_map] using hleft
      have byte := span i hi
      have value := same i (by omega) hright
      rw [byte] at value
      simpa only [List.getElem_map,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hright,Option.getD_some] using value
    · intro same i lo hi
      have index : i < xs.length := by omega
      rw [span i index]
      have values := congrArg (fun ys : List Nat => ys.getD i 0) same
      simpa only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem index,
        List.getElem?_eq_getElem hi,Option.map_some,Option.getD_some] using values
  · rw [ite_eq_left (Or.inr width)]
    constructor
    · intro impossible; cases impossible
    · intro same
      have lengths := congrArg List.length same
      simp only [List.length_map] at lengths
      exact False.elim (width lengths)

theorem classify_header (g : Nat → Nat) (start : Nat) (h : Header)
    (span : Span g start h.name) : classify g start (start+h.name.length) = h.kind := by
  simp only [classify,eq_ci g start h.name span,Header.kind,decide_eq_true_eq]

def digitsValue (acc : Nat) (xs : ApiRequestSpec.Bytes) : Nat :=
  xs.foldl (fun a b => 10*a+(b.toNat-48)) acc

theorem digits_ge (acc : Nat) (xs : ApiRequestSpec.Bytes) : acc ≤ digitsValue acc xs := by
  induction xs generalizing acc with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    change acc ≤ digitsValue (10*acc+(x.toNat-48)) xs
    have tail := ih (10*acc+(x.toNat-48))
    omega

/-- Every intermediate Content-Length accumulator is bounded by its final
    structural decimal value; this includes arbitrary leading zeroes. -/
theorem content_loop (g : Nat → Nat) (start max acc : Nat) (xs : ApiRequestSpec.Bytes)
    (span : Span g start xs)
    (digits : ∀ b ∈ xs, 48 ≤ b.toNat ∧ b.toNat ≤ 57)
    (bound : digitsValue acc xs ≤ max) :
    clLoop g (start+xs.length) max acc start = .ok (digitsValue acc xs) := by
  induction xs generalizing start acc with
  | nil => rw [clLoop]; simp only [List.length_nil,Nat.add_zero,Nat.lt_irrefl,ite_false]; rfl
  | cons x xs ih =>
    have first := digits x (by simp)
    have byte := span_head span
    have nextBound := digits_ge (10*acc+(x.toNat-48)) xs
    have noOverflow : ¬ max < acc*10+(g start-48) := by
      rw [byte]
      change digitsValue (10*acc+(x.toNat-48)) xs ≤ max at bound
      omega
    rw [clLoop,ite_eq_left (by simp only [List.length_cons]; omega)]
    rw [ite_eq_right (by rw [byte]; omega),ite_eq_right noOverflow]
    have tail := ih (start+1) (10*acc+(x.toNat-48)) (span_tail span)
      (fun b hb => digits b (by simp [hb])) bound
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1 xs.length,byte,Nat.mul_comm acc 10,digitsValue,List.foldl_cons] using tail

theorem content_length (g : Nat → Nat) (start : Nat) (h : Header) (amount max : Nat)
    (span : Span g start h.value) (value : h.LengthValue amount) (bound : amount ≤ max) :
    contentLength g start (start+h.value.length) max = .ok amount := by
  have positive : 0 < h.value.length := List.length_pos_iff.mpr value.2.1
  rw [contentLength,ite_eq_right (by omega)]
  have numeric : digitsValue 0 h.value = amount := value.2.2.2
  rw [←numeric]
  exact content_loop g start max 0 h.value span value.2.2.1 (by rw [numeric]; exact bound)

def recorded (f : Fields) (h : Header) (start amount : Nat) : Fields :=
  ⟨f.headers++[h.field start], f.host || decide (h.kind=1),
    f.hasCl || decide (h.kind=2), if h.kind=2 then amount else f.cl, f.te⟩

/-- The actual pure-parser header action follows from structural uniqueness
    and digits, rather than being a condition in the outer request domain. -/
theorem add_header (g : Nat → Nat) (start : Nat) (h : Header) (f : Fields) (amount max : Nat)
    (span : Span g start h.bytes) (space : f.headers.length < maxHeaders)
    (noHost : h.kind=1 → f.host=false) (noLength : h.kind=2 → f.hasCl=false)
    (noTransfer : h.kind≠3) (te : f.te=false)
    (numeric : h.kind=2 → h.LengthValue amount) (bound : amount≤max) :
    addHeader g f start (start+h.name.length)
      (start+h.name.length+1+h.before.length)
      (start+h.name.length+1+h.before.length+h.value.length)
      (start+h.bytes.length-2) 1 max = .ok (recorded f h start amount) := by
  have pieces : Span g start (h.name ++ (58#8 :: ((h.before++h.value++h.after)++[13#8,10#8]))) := by
    simpa only [Header.bytes,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using span
  have nameSpan := span_left pieces
  have valueSpan := span_left (span_right (show Span g (start+h.name.length+1) (h.before++(h.value++h.after)) by
    simpa only [List.append_assoc] using span_left (span_tail (span_right pieces))))
  have fieldEq : (⟨start,start+h.name.length,
      start+h.name.length+1+h.before.length,
      start+h.name.length+1+h.before.length+h.value.length⟩ : Field) = h.field start := rfl
  unfold addHeader
  rw [ite_eq_right (by omega),classify_header g start h nameSpan]
  dsimp only
  by_cases host : h.kind=1
  · simp [host,noHost host,recorded,fieldEq]
  · rw [ite_eq_right host]
    by_cases lengthCase : h.kind=2
    · rw [ite_eq_left lengthCase]
      have noAfter := (numeric lengthCase).1
      have lineEnd : start+h.bytes.length-2 = start+h.name.length+1+h.before.length+h.value.length := by
        simp only [Header.bytes,List.length_append,List.length_cons,List.length_nil,noAfter]
        omega
      rw [lineEnd]
      simp only [noLength lengthCase,te,Bool.false_eq_true,ne_eq,not_true_eq_false,or_self,ite_false]
      rw [content_length g _ h amount max valueSpan (numeric lengthCase) bound]
      simp [recorded,lengthCase,te,fieldEq]
    · simp only [lengthCase,ite_false,noTransfer,recorded,host,decide_false,Bool.or_false,fieldEq]

theorem tchar_not_eol (b : BitVec 8) (h : isTchar b.toNat=true) : notEol b.toNat=true := by
  by_cases cr : b.toNat=13
  · rw [cr] at h; cases h
  · by_cases lf : b.toNat=10
    · rw [lf] at h; cases h
    · simp [notEol,cr,lf]

theorem field_not_eol (b : BitVec 8) (h : isFieldByte b.toNat=true) : notEol b.toNat=true := by
  by_cases cr : b.toNat=13
  · rw [cr] at h; cases h
  · by_cases lf : b.toNat=10
    · rw [lf] at h; cases h
    · simp [notEol,cr,lf]

def Header.line (h : Header) : ApiRequestSpec.Bytes :=
  h.name++[58#8]++h.before++h.value++h.after

theorem header_line_bytes (h : Header) : h.bytes = Header.line h ++ [13#8,10#8] := rfl

theorem header_line_chars (h : Header) (good : h.Valid) :
    ∀ b∈Header.line h, notEol b.toNat=true := by
  intro b hb
  simp only [Header.line,List.mem_append,List.mem_singleton] at hb
  rcases hb with (((name|colon)|before)|value)|after
  · exact tchar_not_eol b (good.2.1 b name)
  · subst b; decide +kernel
  · exact field_not_eol b (ows_field b (good.2.2.1 b before))
  · exact field_not_eol b (good.2.2.2.1 b value)
  · exact field_not_eol b (ows_field b (good.2.2.2.2.1 b after))

theorem line_complete (g : Nat → Nat) (start cap : Nat) (line : ApiRequestSpec.Bytes)
    (span : Span g start (line++[13#8,10#8]))
    (chars : ∀ b∈line, notEol b.toNat=true) (enough : start+line.length+2≤cap) :
    lineEnd g start cap = start+line.length ∧ lineTerm g (start+line.length) cap=0 := by
  have cr := span_head (span_right span)
  have lf := span_head (span_tail (span_right span))
  constructor
  · apply scan_piece notEol g start cap line (span_left span) chars (by omega)
    rw [cr]; decide +kernel
  · have first : ¬cap≤start+line.length := by omega
    have second : ¬cap≤start+line.length+1 := by omega
    simp only [lineTerm,first,ite_false,cr,show (13#8).toNat≠10 by decide +kernel,
      second,lf,show ¬(10#8).toNat≠10 by decide +kernel]

end E5R.Thermostat.ApiHeaderGrammar
