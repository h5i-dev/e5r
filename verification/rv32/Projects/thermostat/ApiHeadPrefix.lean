import Projects.thermostat.ApiFixedHead
import Projects.thermostat.HeadFieldsCongr
import Projects.thermostat.HeadRequestCongr
set_option autoImplicit false
namespace E5R.Thermostat.ApiHeadPrefix
open E5R E5R.Thermostat HttpRequestSpec ApiRequestSpec ApiRequestGrammar ApiHeaderGrammar ApiHeadGrammar

theorem line_incomplete (g : Nat → Nat) (start cap : Nat) (line : ApiRequestSpec.Bytes)
    (span : Span g start (line++[13#8,10#8]))
    (chars : ∀ b∈line, notEol b.toNat=true) (unfinished : cap<start+line.length+2) :
    lineTerm g (lineEnd g start cap) cap=1 := by
  by_cases before : cap≤start
  · have scan : lineEnd g start cap=start := scan_end before
    rw [scan]
    simp only [lineTerm,before,ite_true]
  · by_cases inside : cap≤start+line.length
    · have scan : lineEnd g start cap=cap :=
        scan_to_limit notEol g start cap line (span_left span) chars (by omega) inside
      rw [scan]
      simp only [lineTerm,Nat.le_refl,ite_true]
    · have cr := span_head (span_right span)
      have scan : lineEnd g start cap=start+line.length :=
        scan_piece notEol g start cap line (span_left span) chars (by omega) (by rw [cr]; decide +kernel)
      rw [scan]
      simp only [lineTerm,show ¬cap≤start+line.length by omega,ite_false,cr,
        show (13#8).toNat≠10 by decide +kernel,show cap≤start+line.length+1 by omega,ite_true]

theorem header_advance (g : Nat → Nat) (start cap amount : Nat)
    (h : Header) (hs : List Header) (f : Fields)
    (span : Span g start h.bytes) (valid : h.Valid) (noTransfer : h.kind≠3)
    (numeric : h.kind=2 → h.LengthValue amount) (remaining : Remaining f (h::hs) amount)
    (bound : amount≤1024) (enough : start+h.bytes.length≤cap) :
    fields g cap 1 1024 start f = fields g cap 1 1024 (start+h.bytes.length) (recorded f h start amount) := by
  have lineSpan : Span g start (ApiHeaderGrammar.Header.line h++[13#8,10#8]) := by
    rw [←header_line_bytes]; exact span
  have size : h.bytes.length=(ApiHeaderGrammar.Header.line h).length+2 := by
    rw [header_line_bytes,List.length_append]; rfl
  have ending := line_complete g start cap (ApiHeaderGrammar.Header.line h) lineSpan
    (header_line_chars h valid) (by omega)
  have endpoint : start+(ApiHeaderGrammar.Header.line h).length=start+h.bytes.length-2 := by omega
  have positive : 0<(ApiHeaderGrammar.Header.line h).length := by
    simp only [ApiHeaderGrammar.Header.line,List.length_append,List.length_cons,List.length_nil]
    omega
  have parsed := header_line g start h valid span
  rw [←endpoint] at parsed
  have action := add_header g start h f amount 1024 span
    (by have := remaining.space; simp only [List.length_cons,maxHeaders] at *; omega)
    (no_duplicate 1 h hs f.host remaining.host) (no_duplicate 2 h hs f.hasCl remaining.length)
    noTransfer remaining.te numeric bound
  rw [←endpoint] at action
  rw [fields]
  simp only [show start<cap by omega,ite_true,ending.1,ending.2,
    show ¬(0=1) by decide,show ¬(0=2) by decide,ite_false,
    show start+(ApiHeaderGrammar.Header.line h).length≠start by omega,parsed,action]
  rw [show start+(ApiHeaderGrammar.Header.line h).length+2=start+h.bytes.length by omega]

theorem fields_incomplete (g : Nat → Nat) (start cap amount : Nat)
    (hs : List Header) (f : Fields)
    (span : Span g start (hs.flatMap Header.bytes++[13#8,10#8]))
    (valid : ∀ h∈hs,h.Valid) (noTransfer : ∀ h∈hs,h.kind≠3)
    (numeric : ∀ h∈hs,h.kind=2 → h.LengthValue amount)
    (remaining : Remaining f hs amount) (bound : amount≤1024)
    (unfinished : cap<start+(hs.flatMap Header.bytes).length+2) :
    fields g cap 1 1024 start f=.more := by
  induction hs generalizing start f with
  | nil =>
    by_cases before : cap≤start
    · rw [fields,ite_eq_right (by omega)]
    · have ending := line_incomplete g start cap [] span (by simp) (by simpa using unfinished)
      rw [fields,ite_eq_left (by omega),ite_eq_left ending]
  | cons h hs ih =>
    have pieces : Span g start (h.bytes++(hs.flatMap Header.bytes++[13#8,10#8])) := by
      simpa only [List.flatMap_cons,List.append_assoc] using span
    have firstSpan := span_left pieces
    have restSpan := span_right pieces
    by_cases done : start+h.bytes.length≤cap
    · rw [header_advance g start cap amount h hs f firstSpan (valid h (by simp))
        (noTransfer h (by simp)) (numeric h (by simp)) remaining bound done]
      apply ih (start+h.bytes.length) (recorded f h start amount) restSpan
        (fun x hx => valid x (by simp [hx])) (fun x hx => noTransfer x (by simp [hx]))
        (fun x hx => numeric x (by simp [hx])) (remaining_step f h hs start amount remaining)
      simp only [List.flatMap_cons,List.length_append] at unfinished
      omega
    · by_cases before : cap≤start
      · rw [fields,ite_eq_right (by omega)]
      · have lineSpan : Span g start (ApiHeaderGrammar.Header.line h++[13#8,10#8]) := by
          rw [←header_line_bytes]; exact firstSpan
        have size : h.bytes.length=(ApiHeaderGrammar.Header.line h).length+2 := by
          rw [header_line_bytes,List.length_append]; rfl
        have ending := line_incomplete g start cap (ApiHeaderGrammar.Header.line h) lineSpan
          (header_line_chars h (valid h (by simp))) (by omega)
        rw [fields,ite_eq_left (by omega),ite_eq_left ending]

/-- Every proper byte prefix is incomplete, including zero bytes, a partial
    request line, a lone CR, and prefixes after complete ordinary headers. -/
theorem incomplete (r : Fixed11) (n : Nat) (proper : n<r.headBytes.length) :
    HttpRequestBytes.parse (r.headBytes.take n) 1024 1024=.incomplete := by
  let cap := r.headBytes.length
  let line := ApiRequestSpec.requestLine r.route r.query
  let tail := r.headers.flatMap Header.bytes++[13#8,10#8]
  let g := window (HttpRequestBytes.bytes r.headBytes) cap
  let view := window (HttpRequestBytes.bytes (r.headBytes.take n)) n
  have bytesEq : r.headBytes=line++tail := by
    simp only [Fixed11.headBytes,headBytes,line,tail,List.append_assoc]
  have capEq : cap=line.length+(r.headers.flatMap Header.bytes).length+2 := by
    simp only [cap,bytesEq,List.length_append,List.length_cons,List.length_nil,tail]
    omega
  have lineSpan : Span g 0 line := by
    have piece := window_span [] line tail cap (by simp only [List.length_nil,Nat.zero_add]; omega)
    simpa only [List.nil_append,List.length_nil,←bytesEq,Nat.zero_add,g] using piece
  have tailSpan : Span g line.length tail := by
    have piece := window_span line tail [] cap (by simp only [List.length_append,List.length_cons,List.length_nil,tail]; omega)
    simpa only [List.append_nil,←bytesEq,g] using piece
  have lineContent : Span g 0 (ApiFixedHead.content r.route r.query++[13#8,10#8]) := by
    rw [←ApiFixedHead.line_bytes]; exact lineSpan
  have lineSize : line.length=(ApiFixedHead.content r.route r.query).length+2 := by
    dsimp only [line]
    rw [ApiFixedHead.line_bytes,List.length_append]; rfl
  have agree (k : Nat) (hk : k<n) : view k=g k := by
    have bound : k<cap := by dsimp only [cap]; omega
    simp [view,g,window,hk,bound,HttpRequestBytes.bytes,List.getD_eq_getElem?_getD]
  have lineEq : lineEnd view 0 n=lineEnd g 0 n := HeadLineScanSpec.line_congr view g 0 n agree
  have termEq : lineTerm view (lineEnd g 0 n) n=lineTerm g (lineEnd g 0 n) n :=
    HeadLineScanSpec.term_congr view g (lineEnd g 0 n) n agree
  have lengthEq : (HttpRequestBytes.bytes (r.headBytes.take n)).length=n := by
    simp only [HttpRequestBytes.bytes,List.length_map,List.length_take,Nat.min_eq_left (Nat.le_of_lt proper)]
  have headBound := r.headBound
  have notFull : ¬1024≤n := by dsimp only [Fixed11.headBytes] at proper; omega
  have limit : readLimit (HttpRequestBytes.bytes (r.headBytes.take n)).length 1024=n := by
    rw [lengthEq]; simp only [readLimit,notFull,ite_false]
  unfold HttpRequestBytes.parse parseHead
  rw [limit]
  change (if lineTerm view (lineEnd view 0 n) n=1 then _ else _) = _
  rw [lineEq,termEq]
  by_cases partialLine : n<line.length
  · have ending := line_incomplete g 0 n (ApiFixedHead.content r.route r.query) lineContent
      (ApiFixedHead.content_chars r) (by omega)
    rw [ite_eq_left ending]
    simp only [lengthEq,notFull,decide_false,Bool.false_eq_true,ite_false]
  · have ending := line_complete g 0 n (ApiFixedHead.content r.route r.query) lineContent
      (ApiFixedHead.content_chars r) (by omega)
    have lineEnd : HttpRequestSpec.lineEnd g 0 n=line.length-2 := by
      simpa only [Nat.zero_add,show line.length-2=(ApiFixedHead.content r.route r.query).length by omega] using ending.1
    have term : lineTerm g (line.length-2) n=0 := by
      simpa only [Nat.zero_add,show line.length-2=(ApiFixedHead.content r.route r.query).length by omega] using ending.2
    rw [lineEnd,term]
    simp only [show ¬(0=1) by decide,show ¬(0=2) by decide,ite_false]
    have req := request_line g r.route r.query r.routeValid r.queryValid lineSpan
    have reqEq := HeadRequestCongr.requestLine view g (line.length-2) (fun k hk => agree k (by omega))
    rw [reqEq,req]
    dsimp only
    have remaining : Remaining Fields.empty r.headers r.body.length := by
      constructor
      · simpa only [count,Fields.empty,flag,Bool.false_eq_true,ite_false,Nat.add_zero] using r.hostCount
      · simpa only [count,Fields.empty,flag,Bool.false_eq_true,ite_false,Nat.add_zero] using r.lengthCount
      · intro impossible; cases impossible
      · rfl
      · simpa only [Fields.empty,List.length_nil,Nat.zero_add] using r.headerCount
    have more := fields_incomplete g line.length n r.body.length r.headers Fields.empty tailSpan
      r.headersValid r.noTransfer r.lengthValue remaining r.bodyBound (by dsimp only [cap] at capEq; omega)
    have fieldsEq := HeadFieldsCongr.fields view g n 1 line.length Fields.empty agree
    rw [show line.length-2+2=line.length by omega,fieldsEq,more]
    simp only [lengthEq,notFull,decide_false,Bool.false_eq_true,ite_false]

end E5R.Thermostat.ApiHeadPrefix
