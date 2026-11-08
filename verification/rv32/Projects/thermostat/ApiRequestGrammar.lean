import Projects.thermostat.ApiRequestSpec
import Projects.thermostat.HeadLineScanSpec
import Projects.thermostat.HeadVersionSpec
set_option autoImplicit false
namespace E5R.Thermostat.ApiRequestGrammar
open E5R E5R.Thermostat HttpRequestSpec ApiRequestSpec

/-- A pure byte span, used to connect syntactic pieces with parser indices. -/
def Span (g : Nat → Nat) (start : Nat) (xs : ApiRequestSpec.Bytes) : Prop :=
  ∀ i (hi : i < xs.length), g (start+i) = (xs[i]'hi).toNat

theorem span_left {g : Nat → Nat} {start : Nat} {xs ys : ApiRequestSpec.Bytes}
    (h : Span g start (xs++ys)) : Span g start xs := by
  intro i hi
  have v := h i (by simp only [List.length_append]; omega)
  rw [List.getElem_append_left hi] at v
  exact v

theorem span_right {g : Nat → Nat} {start : Nat} {xs ys : ApiRequestSpec.Bytes}
    (h : Span g start (xs++ys)) : Span g (start+xs.length) ys := by
  intro i hi
  have v := h (xs.length+i) (by simp only [List.length_append]; omega)
  simpa only [List.getElem_append_right (by omega : xs.length ≤ xs.length+i),
    Nat.add_sub_cancel_left,Nat.add_assoc] using v

theorem span_tail {g : Nat → Nat} {start : Nat} {x : BitVec 8} {xs : ApiRequestSpec.Bytes}
    (h : Span g start (x::xs)) : Span g (start+1) xs := by
  intro i hi
  have v := h (i+1) (by simp only [List.length_cons]; omega)
  simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm 1 i] using v

theorem span_head {g : Nat → Nat} {start : Nat} {x : BitVec 8} {xs : ApiRequestSpec.Bytes}
    (h : Span g start (x::xs)) : g start = x.toNat := by
  have v := h 0 (by simp)
  change g (start+0) = x.toNat at v
  simpa only [Nat.add_zero] using v

/-- Scans stop at the syntactic delimiter, for arbitrary token lengths. -/
theorem scan_piece (p : Nat → Bool) (g : Nat → Nat) (start cap : Nat)
    (xs : ApiRequestSpec.Bytes) (span : Span g start xs)
    (good : ∀ b ∈ xs, p b.toNat = true)
    (inside : start+xs.length < cap) (stop : p (g (start+xs.length)) = false) :
    scan p g start cap = start+xs.length := by
  induction xs generalizing start with
  | nil => simpa only [List.length_nil,Nat.add_zero] using scan_stop inside stop
  | cons x xs ih =>
    have first : p (g start) = true := by rw [span_head span]; exact good x (by simp)
    rw [scan_cont (by simp only [List.length_cons] at inside; omega) first]
    have tail := ih (start+1) (span_tail span) (fun b hb => good b (by simp [hb]))
      (by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1 xs.length] using inside)
      (by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1 xs.length] using stop)
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1 xs.length] using tail

theorem all_piece (p : Nat → Bool) (g : Nat → Nat) (start : Nat)
    (xs : ApiRequestSpec.Bytes) (span : Span g start xs)
    (good : ∀ b ∈ xs, p b.toNat = true) :
    allIn p g start (start+xs.length) = true := by
  induction xs generalizing start with
  | nil => exact allIn_end (by simp)
  | cons x xs ih =>
    have first : p (g start) = true := by rw [span_head span]; exact good x (by simp)
    rw [allIn_cont (by simp only [List.length_cons]; omega) first]
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1 xs.length] using
      ih (start+1) (span_tail span) (fun b hb => good b (by simp [hb]))

theorem scan_to_limit (p : Nat → Bool) (g : Nat → Nat) (start cap : Nat)
    (xs : ApiRequestSpec.Bytes) (span : Span g start xs)
    (good : ∀ b ∈ xs, p b.toNat = true) (lo : start ≤ cap) (hi : cap ≤ start+xs.length) :
    scan p g start cap = cap := by
  apply HeadLineScanSpec.scan_all p g start cap lo
  intro k lower upper
  have index : k-start < xs.length := by omega
  have byte := span (k-start) index
  rw [Nat.add_sub_of_le lower] at byte
  rw [byte]
  exact good _ (List.getElem_mem index)

theorem window_span (before xs after : ApiRequestSpec.Bytes) (cap : Nat)
    (enough : before.length+xs.length ≤ cap) :
    Span (window (HttpRequestBytes.bytes (before++xs++after)) cap) before.length xs := by
  intro i hi
  have index : before.length+i < cap := by omega
  simp only [window,index,ite_true,HttpRequestBytes.bytes,List.map_append,
    List.getD_eq_getElem?_getD,List.getElem?_append,List.length_map]
  simp only [show ¬before.length+i < before.length by omega,ite_false,
    Nat.add_sub_cancel_left]
  simp [hi]

theorem method_chars (route : Route) : route.method ≠ [] ∧
    ∀ b ∈ route.method, isTchar b.toNat = true := by
  cases route <;> simp only [Route.method] <;> decide +kernel

theorem target_chars (route : Route) (query : Option ApiRequestSpec.Bytes)
    (routeGood : route.Valid)
    (queryGood : ∀ q, query = some q → ∀ b ∈ q, isTargetByte b.toNat = true) :
    target route query ≠ [] ∧ ∀ b ∈ target route query, isTargetByte b.toNat = true := by
  have pathGood : route.path ≠ [] ∧ ∀ b ∈ route.path, isTargetByte b.toNat = true := by
    cases route with
    | state => decide +kernel
    | setpoint => decide +kernel
    | temp => decide +kernel
    | mode => decide +kernel
    | relay segment =>
      constructor
      · simp [Route.path,WireSpec.ascii]
      · intro b hb
        rcases List.mem_append.mp hb with hb|hb
        · have fixed : ∀ b ∈ WireSpec.ascii "/relay/", isTargetByte b.toNat = true := by decide +kernel
          exact fixed b hb
        · exact (routeGood.2 b hb).1
  constructor
  · intro empty
    have := congrArg List.length empty
    have positive : 0 < route.path.length := List.length_pos_iff.mpr pathGood.1
    simp only [target,List.length_append,List.length_nil] at this
    omega
  · intro b hb
    rcases List.mem_append.mp hb with hb|hb
    · exact pathGood.2 b hb
    · cases query with
      | none => cases hb
      | some q =>
        rcases List.mem_cons.mp hb with eq|mem
        · subst b; decide +kernel
        · exact queryGood q rfl b mem

/-- The structural request line establishes all parser token/version tests. -/
theorem request_line (g : Nat → Nat) (route : Route) (query : Option ApiRequestSpec.Bytes)
    (routeGood : route.Valid)
    (queryGood : ∀ q, query = some q → ∀ b ∈ q, isTargetByte b.toNat = true)
    (span : Span g 0 (ApiRequestSpec.requestLine route query)) :
    HttpRequestSpec.requestLine g 0 ((ApiRequestSpec.requestLine route query).length-2) =
      .ok 0 route.method.length (route.method.length+1)
        (route.method.length+1+(target route query).length) 1 := by
  let m := route.method.length
  let t := (target route query).length
  have methodGood := method_chars route
  have targetGood := target_chars route query routeGood queryGood
  have bytesEq : ApiRequestSpec.requestLine route query =
      route.method ++ (32#8 :: (target route query ++ (32#8 :: WireSpec.ascii "HTTP/1.1\r\n"))) := by
    simp only [ApiRequestSpec.requestLine,List.append_assoc,List.singleton_append]
    rfl
  rw [bytesEq] at span
  have methodSpan := span_left span
  have firstSpace := span_head (span_right span)
  have targetSpan := span_left (span_tail (span_right span))
  have lastSpace := span_head (span_right (span_tail (span_right span)))
  have versionSpan := span_tail (span_right (span_tail (span_right span)))
  have lengthEq : (ApiRequestSpec.requestLine route query).length-2 = m+1+t+9 := by
    rw [bytesEq]
    simp only [List.length_append,List.length_cons]
    change m+(t+(10+1)+1)-2 = m+1+t+9
    omega
  have mPos : 0 < m := List.length_pos_iff.mpr methodGood.1
  have tPos : 0 < t := List.length_pos_iff.mpr targetGood.1
  have ms : g m = 32 := by simpa only [Nat.zero_add,m,show (32#8).toNat=32 by decide +kernel] using firstSpace
  have ts : g (m+1+t) = 32 := by simpa only [Nat.zero_add,m,t,show (32#8).toNat=32 by decide +kernel] using lastSpace
  have methodScan : scan isTchar g 0 (m+1+t+9) = m := by
    simpa only [Nat.zero_add] using scan_piece isTchar g 0 (m+1+t+9) route.method methodSpan methodGood.2
      (by dsimp [m]; omega) (by simpa only [Nat.zero_add] using (show isTchar (g m) = false by rw [ms]; decide +kernel))
  have targetScan : scan isTargetByte g (m+1) (m+1+t+9) = m+1+t :=
    scan_piece isTargetByte g (m+1) (m+1+t+9) (target route query) (by simpa only [Nat.zero_add,m] using targetSpan) targetGood.2
      (by dsimp [t]; omega) (by change isTargetByte (g (m+1+t))=false; rw [ts]; decide +kernel)
  have startsSlash : g (m+1) = 47 := by
    have pathFirst : ∀ r : Route, ∃ rest, r.path = 47#8::rest := by
      intro r; cases r <;> exact ⟨_,rfl⟩
    obtain ⟨rest,eq⟩ := pathFirst route
    have piece := targetSpan
    simp only [target,eq,List.cons_append] at piece
    simpa only [Nat.zero_add,m,show (47#8).toNat=47 by decide +kernel] using span_head piece
  have ver : HttpRequestSpec.version g (m+1+t+1) (m+1+t+9) = 1 := by
    have v (i : Nat) (hi : i<10) := versionSpan i (by exact hi)
    have byteAt (i : Nat) (hi : i<10) : g (m+1+t+1+i) =
        ((WireSpec.ascii "HTTP/1.1\r\n")[i]'hi).toNat := by
      simpa only [Nat.zero_add] using v i hi
    have httpPrefix : HeadVersionSpec.Prefix g (m+1+t+1) :=
      ⟨byteAt 0 (by decide),byteAt 1 (by decide),byteAt 2 (by decide),byteAt 3 (by decide),byteAt 4 (by decide)⟩
    rw [show m+1+t+9 = (m+1+t+1)+8 by omega,HeadVersionSpec.version]
    simp only [httpPrefix,ite_true]
    rw [byteAt 5 (by decide),byteAt 6 (by decide),byteAt 7 (by decide)]
    decide +kernel
  rw [lengthEq]
  unfold HttpRequestSpec.requestLine
  rw [methodScan]
  simp only [show ¬(m=0 ∨ m+1+t+9≤m) by omega,ite_false,ms,ne_eq,not_true_eq_false]
  rw [targetScan]
  simp only [show ¬(m+1+t=m+1 ∨ m+1+t+9≤m+1+t) by omega,ite_false,
    startsSlash,ts,not_true_eq_false,or_self]
  rw [ver]
  rfl

theorem trim_suffix (g : Nat → Nat) (start middle finish : Nat)
    (ordered : start ≤ middle) (inside : middle ≤ finish)
    (ows : ∀ k, middle ≤ k → k < finish → isOws (g k) = true)
    (last : middle = start ∨ (start < middle ∧ isOws (g (middle-1)) = false)) :
    trimEnd g start finish = middle := by
  by_cases eq : finish = middle
  · subst finish
    rcases last with eq|last
    · subst middle; rw [trimEnd]; simp
    · rw [trimEnd,ite_eq_left last.1,ite_eq_right (by simp only [last.2,Bool.false_eq_true,not_false_eq_true])]
  · have positive : start < finish := by omega
    have trailing : isOws (g (finish-1)) = true := ows (finish-1) (by omega) (by omega)
    rw [trimEnd,ite_eq_left positive,ite_eq_left trailing]
    exact trim_suffix g start middle (finish-1) ordered (by omega)
      (fun k lower upper => ows k lower (by omega)) last
termination_by finish

theorem ows_field (b : BitVec 8) (h : isOws b.toNat = true) : isFieldByte b.toNat = true := by
  have choice : b.toNat = 32 ∨ b.toNat = 9 := by simpa only [isOws,Bool.or_eq_true,beq_iff_eq] using h
  rcases choice with eq|eq <;> rw [eq] <;> decide +kernel

/-- Field-value lexical acceptance is derived even with arbitrary internal OWS. -/
theorem header_line (g : Nat → Nat) (start : Nat) (h : Header)
    (good : h.Valid) (span : Span g start h.bytes) :
    HttpRequestSpec.headerLine g start (start+h.bytes.length-2) =
      .ok (start+h.name.length) (start+h.name.length+1+h.before.length)
        (start+h.name.length+1+h.before.length+h.value.length) := by
  let colon := start+h.name.length
  let valueStart := colon+1+h.before.length
  let valueEnd := valueStart+h.value.length
  let finish := valueEnd+h.after.length
  have parts : Span g start (h.name ++ (58#8 :: ((h.before++h.value++h.after)++[13#8,10#8]))) := by
    simpa only [Header.bytes,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using span
  have nameSpan := span_left parts
  have colonByte : g colon = 58 := by
    simpa only [colon,show (58#8).toNat=58 by decide +kernel] using span_head (span_right parts)
  have values : Span g (colon+1) (h.before++h.value++h.after) := by
    exact span_left (span_tail (span_right parts))
  have beforeSpan := span_left (show Span g (colon+1) (h.before++(h.value++h.after)) by
    simpa only [List.append_assoc] using values)
  have valueAndAfter := span_right (show Span g (colon+1) (h.before++(h.value++h.after)) by
    simpa only [List.append_assoc] using values)
  have valueSpan : Span g valueStart h.value := span_left valueAndAfter
  have afterSpan : Span g valueEnd h.after := span_right valueAndAfter
  have namePositive : 0 < h.name.length := List.length_pos_iff.mpr good.1
  have finishEq : start+h.bytes.length-2 = finish := by
    simp only [Header.bytes,List.length_append,List.length_cons,List.length_nil]
    dsimp [finish,valueEnd,valueStart,colon]
    omega
  have nameScan : scan isTchar g start finish = colon := by
    apply scan_piece isTchar g start finish h.name nameSpan good.2.1
    · dsimp [finish,valueEnd,valueStart,colon]; omega
    · change isTchar (g colon) = false; rw [colonByte]; decide +kernel
  have fieldChars : ∀ b ∈ h.before++h.value++h.after, isFieldByte b.toNat = true := by
    intro b hb
    rcases List.mem_append.mp hb with hb|hb
    · rcases List.mem_append.mp hb with hb|hb
      · exact ows_field b (good.2.2.1 b hb)
      · exact good.2.2.2.1 b hb
    · exact ows_field b (good.2.2.2.2.1 b hb)
  have allFields : allIn isFieldByte g (colon+1) finish = true := by
    have checked := all_piece isFieldByte g (colon+1) (h.before++h.value++h.after) values fieldChars
    simpa only [List.length_append,finish,valueEnd,valueStart,Nat.add_assoc] using checked
  have valueScan : scan isOws g (colon+1) finish = valueStart := by
    by_cases empty : h.value = []
    · have noAfter := good.2.2.2.2.2.1 empty
      have endEq : finish = valueStart := by simp [finish,valueEnd,empty,noAfter]
      rw [endEq]
      exact scan_to_limit isOws g (colon+1) valueStart h.before beforeSpan good.2.2.1 (by dsimp [valueStart]; omega) (Nat.le_refl _)
    · have nonempty : 0 < h.value.length := List.length_pos_iff.mpr empty
      have first : g valueStart = (h.value.headD 0#8).toNat := by
        cases valuesEq : h.value with
        | nil => exact False.elim (empty valuesEq)
        | cons x xs =>
          rw [valuesEq] at valueSpan
          simpa only [valuesEq,List.headD_cons] using span_head valueSpan
      exact scan_piece isOws g (colon+1) finish h.before beforeSpan good.2.2.1
        (by dsimp [finish,valueEnd,valueStart]; omega)
        (by change isOws (g valueStart)=false; rw [first]; exact (good.2.2.2.2.2.2 empty).1)
  have trim : trimEnd g valueStart finish = valueEnd := by
    apply trim_suffix g valueStart valueEnd finish (by dsimp [valueEnd]; omega) (by dsimp [finish]; omega)
    · intro k lower upper
      have index : k-valueEnd < h.after.length := by dsimp [finish] at upper; omega
      have byte := afterSpan (k-valueEnd) index
      rw [Nat.add_sub_of_le lower] at byte
      rw [byte]
      exact good.2.2.2.2.1 _ (List.getElem_mem index)
    · by_cases empty : h.value = []
      · exact Or.inl (by simp [valueEnd,empty])
      · have positive : 0 < h.value.length := List.length_pos_iff.mpr empty
        refine Or.inr ⟨by dsimp [valueEnd]; omega,?_⟩
        have lastByte := valueSpan (h.value.length-1) (by omega)
        have address : valueStart+(h.value.length-1) = valueEnd-1 := by dsimp [valueEnd]; omega
        rw [address] at lastByte
        rw [lastByte]
        have lastEq : h.value[h.value.length-1] = h.value.getLastD 0#8 := by
          simp only [List.getLastD_eq_getLast?,List.getLast?_eq_some_getLast empty,Option.getD_some,List.getLast_eq_getElem]
        rw [lastEq]
        exact (good.2.2.2.2.2.2 empty).2
  rw [finishEq]
  unfold HttpRequestSpec.headerLine
  rw [nameScan]
  simp only [show ¬(colon=start ∨ finish≤colon) by dsimp [colon,finish,valueEnd,valueStart]; omega,
    ite_false,colonByte,ne_eq,not_true_eq_false,allFields,Bool.not_true,Bool.false_eq_true,valueScan,trim]
  rfl

end E5R.Thermostat.ApiRequestGrammar
