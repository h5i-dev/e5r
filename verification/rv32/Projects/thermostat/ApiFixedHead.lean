import Projects.thermostat.ApiHeadGrammar
set_option autoImplicit false
namespace E5R.Thermostat.ApiFixedHead
open E5R E5R.Thermostat HttpRequestSpec ApiRequestSpec ApiRequestGrammar ApiHeaderGrammar ApiHeadGrammar

def content (route : Route) (query : Option ApiRequestSpec.Bytes) : ApiRequestSpec.Bytes :=
  route.method++[32#8]++target route query++WireSpec.ascii " HTTP/1.1"

theorem line_bytes (route : Route) (query : Option ApiRequestSpec.Bytes) :
    ApiRequestSpec.requestLine route query = content route query++[13#8,10#8] := by
  simp only [ApiRequestSpec.requestLine,content,List.append_assoc]
  rfl

theorem target_not_eol (b : BitVec 8) (h : isTargetByte b.toNat=true) : notEol b.toNat=true := by
  by_cases cr : b.toNat=13
  · rw [cr] at h; cases h
  · by_cases lf : b.toNat=10
    · rw [lf] at h; cases h
    · simp [notEol,cr,lf]

theorem content_chars (r : Fixed11) : ∀ b∈content r.route r.query, notEol b.toNat=true := by
  intro b hb
  simp only [content,List.mem_append,List.mem_singleton] at hb
  rcases hb with ((method|space)|path)|version
  · exact tchar_not_eol b ((method_chars r.route).2 b method)
  · subst b; decide +kernel
  · exact target_not_eol b ((target_chars r.route r.query r.routeValid r.queryValid).2 b path)
  · have fixed : ∀ b∈WireSpec.ascii " HTTP/1.1", notEol b.toNat=true := by decide +kernel
    exact fixed b version

/-- The broad structural domain derives a complete parser result, with exact
    field offsets and Content-Length; acceptance is not an input assumption. -/
theorem accepted (r : Fixed11) : HttpRequestBytes.parse r.headBytes 1024 1024 = .done r.head := by
  let cap := r.headBytes.length
  let line := ApiRequestSpec.requestLine r.route r.query
  let tail := r.headers.flatMap Header.bytes++[13#8,10#8]
  let g := window (HttpRequestBytes.bytes r.headBytes) cap
  have bytesEq : r.headBytes = line++tail := by
    simp only [Fixed11.headBytes,headBytes,line,tail,List.append_assoc]
  have capEq : cap = line.length+(r.headers.flatMap Header.bytes).length+2 := by
    simp only [cap,bytesEq,List.length_append,List.length_cons,List.length_nil,tail]
    omega
  have lineSpan : Span g 0 line := by
    have piece := window_span [] line tail cap (by simp only [List.length_nil,Nat.zero_add]; omega)
    simpa only [List.nil_append,List.length_nil,←bytesEq,Nat.zero_add,g] using piece
  have tailSpan : Span g line.length tail := by
    have piece := window_span line tail [] cap (by simp only [List.length_append,List.length_cons,List.length_nil,tail]; omega)
    simpa only [List.append_nil,←bytesEq,g] using piece
  have lineContent : Span g 0 (content r.route r.query++[13#8,10#8]) := by
    rw [←line_bytes]; exact lineSpan
  have lineSize : line.length = (content r.route r.query).length+2 := by
    dsimp only [line]
    rw [line_bytes,List.length_append]
    rfl
  have ending := line_complete g 0 cap (content r.route r.query) lineContent (content_chars r)
    (by omega)
  have lineEnd : HttpRequestSpec.lineEnd g 0 cap = line.length-2 := by
    simpa only [Nat.zero_add,show line.length-2=(content r.route r.query).length by omega] using ending.1
  have term : lineTerm g (line.length-2) cap = 0 := by
    simpa only [Nat.zero_add,show line.length-2=(content r.route r.query).length by omega] using ending.2
  have request := request_line g r.route r.query r.routeValid r.queryValid lineSpan
  have remaining : Remaining Fields.empty r.headers r.body.length := by
    constructor
    · simpa only [count,Fields.empty,flag,Bool.false_eq_true,ite_false,Nat.add_zero] using r.hostCount
    · simpa only [count,Fields.empty,flag,Bool.false_eq_true,ite_false,Nat.add_zero] using r.lengthCount
    · intro impossible; cases impossible
    · rfl
    · simpa only [Fields.empty,List.length_nil,Nat.zero_add] using r.headerCount
  have fields := fields_complete g line.length cap 1024 r.body.length r.headers Fields.empty
    tailSpan r.headersValid r.noTransfer r.lengthValue remaining r.bodyBound (by omega)
  have limit : readLimit (HttpRequestBytes.bytes r.headBytes).length 1024 = cap := by
    have bound := r.headBound
    simp only [HttpRequestBytes.bytes,List.length_map]
    unfold readLimit
    split <;> dsimp only [cap,Fixed11.headBytes] at * <;> omega
  unfold HttpRequestBytes.parse parseHead
  rw [limit]
  change (if lineTerm g (HttpRequestSpec.lineEnd g 0 cap) cap=1 then _ else _) = _
  rw [lineEnd,term]
  simp only [show ¬(0=1) by decide,show ¬(0=2) by decide,ite_false]
  rw [request]
  dsimp only
  have advance : line.length-2+2=line.length := by omega
  rw [advance,fields]
  simp only [Fields.empty,List.nil_append,Bool.not_true,Bool.false_eq_true,and_false,ite_false,
    ite_true]
  congr 1
  unfold Fixed11.head
  rw [←capEq]

end E5R.Thermostat.ApiFixedHead
