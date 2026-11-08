import Projects.thermostat.ApiConsume
import Projects.thermostat.MainRequestInputs
import Projects.thermostat.MainMethodBytes
set_option autoImplicit false
namespace E5R.Thermostat.ApiRouting
open E5R E5R.Thermostat HttpRequestSpec ApiRequestSpec ApiRequestGrammar

def method : Route → MainMethodSpec.Method
  | .state => .get
  | .temp => .post
  | _ => .put

theorem raw (r : Fixed11) : MainRequestSpans.raw r.bytes r.head r.body.length=r.bytes := by
  change r.bytes.take (r.headBytes.length+r.body.length)=r.bytes
  have size : r.headBytes.length+r.body.length=r.bytes.length := List.length_append.symm
  rw [size,List.take_length]

theorem body (r : Fixed11) : MainRequestSpans.body r.bytes r.head r.body.length=r.body := by
  change ((r.headBytes++r.body).drop r.headBytes.length).take r.body.length=r.body
  rw [List.drop_left,List.take_length]

theorem entries (r : Fixed11) : MainRequestInputs.entries r.head=r.head.headers.map HttpRequestBytes.entry := rfl

theorem method_token (r : Fixed11) :
    MainMethodBytes.token r.bytes r.head.method.2=r.route.method.map BitVec.toNat := by
  have parts : r.bytes=r.route.method++
      ([32#8]++target r.route r.query++WireSpec.ascii " HTTP/1.1\r\n"++
        r.headers.flatMap Header.bytes++[13#8,10#8]++r.body) := by
    simp only [Fixed11.bytes,Fixed11.headBytes,headBytes,ApiRequestSpec.requestLine,List.append_assoc]
  change (r.bytes.take r.route.method.length).map BitVec.toNat=_
  rw [parts,List.take_left]

theorem method_case (r : Fixed11) :
    MainMethodSpec.decode (MainMethodBytes.token r.bytes r.head.method.2)=method r.route := by
  rw [method_token]
  cases r.route <;> simp only [Route.method,method] <;> decide +kernel

theorem path_no_question (route : Route) (valid : route.Valid) :
    ∀ b∈route.path, MainQuerySpec.notQuestion b.toNat=true := by
  cases route with
  | state => decide +kernel
  | setpoint => decide +kernel
  | temp => decide +kernel
  | mode => decide +kernel
  | relay segment =>
    intro b hb
    rcases List.mem_append.mp hb with hb|hb
    · have fixed : ∀ b∈WireSpec.ascii "/relay/", MainQuerySpec.notQuestion b.toNat=true := by decide +kernel
      exact fixed b hb
    · have neq := (valid.2 b hb).2.2
      have natNe : b.toNat≠63 := by
        intro eq
        apply neq
        apply BitVec.eq_of_toNat_eq
        exact eq
      simp [MainQuerySpec.notQuestion,natNe]

theorem bytes_span (front xs back : ApiRequestSpec.Bytes) :
    Span (MainQuerySpec.bytes (front++xs++back)) front.length xs := by
  intro i hi
  simp only [MainQuerySpec.bytes,List.getElem?_append,List.length_append]
  simp only [show front.length+i<front.length+xs.length by omega,ite_true,
    show ¬front.length+i<front.length by omega,ite_false,Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem hi,Option.getD_some]

/-- Query splitting is derived from the first actual question mark. Relay
    segments may be arbitrary visible bytes except slash/question mark. -/
theorem path (r : Fixed11) : MainRequestSpans.path r.bytes r.head=r.route.path := by
  let front := r.route.method++[32#8]
  let suffix := match r.query with | none => [] | some q => 63#8::q
  let back := suffix++WireSpec.ascii " HTTP/1.1\r\n"++r.headers.flatMap Header.bytes++[13#8,10#8]++r.body
  have parts : r.bytes=front++r.route.path++back := by
    simp only [Fixed11.bytes,Fixed11.headBytes,headBytes,ApiRequestSpec.requestLine,target,
      front,back,suffix,List.append_assoc]
    rfl
  have start : r.head.target.1=front.length := by
    change r.route.method.length+1=(r.route.method++[32#8]).length
    rw [List.length_append]; rfl
  have finish : r.head.target.2=front.length+r.route.path.length+suffix.length := by
    change r.route.method.length+1+(target r.route r.query).length=_
    simp only [target,List.length_append]
    have frontLength : front.length=r.route.method.length+1 := by
      rw [List.length_append]; rfl
    rw [frontLength]
    exact (Nat.add_assoc _ _ _).symm
  have span : Span (MainQuerySpec.bytes r.bytes) front.length r.route.path := by
    rw [parts]; exact bytes_span front r.route.path back
  have splitPoint : MainQuerySpec.position (MainQuerySpec.bytes r.bytes) r.head.target.1 r.head.target.2 = front.length+r.route.path.length := by
    rw [start,finish]
    unfold MainQuerySpec.position
    cases queryEq : r.query with
    | none =>
      have suffixLength : suffix.length=0 := by simp [suffix,queryEq]
      rw [suffixLength,Nat.add_zero]
      exact scan_to_limit MainQuerySpec.notQuestion _ front.length _ r.route.path span
        (path_no_question r.route r.routeValid) (by omega) (Nat.le_refl _)
    | some q =>
      have mark : MainQuerySpec.bytes r.bytes (front.length+r.route.path.length)=63 := by
        have full : Span (MainQuerySpec.bytes r.bytes) front.length (r.route.path++back) := by
          rw [parts,List.append_assoc]
          simpa only [List.append_nil] using bytes_span front (r.route.path++back) []
        have afterPath := span_right full
        simp only [back,suffix,queryEq,List.cons_append] at afterPath
        simpa only [show (63#8).toNat=63 by decide +kernel] using span_head afterPath
      apply scan_piece MainQuerySpec.notQuestion _ front.length _ r.route.path span
        (path_no_question r.route r.routeValid)
      · simp only [suffix,queryEq,List.length_cons]; omega
      · rw [mark]; decide +kernel
  change (r.bytes.drop r.head.target.1).take
    (MainQuerySpec.position (MainQuerySpec.bytes r.bytes) r.head.target.1 r.head.target.2-r.head.target.1)=_
  rw [splitPoint,start,parts,Nat.add_sub_cancel_left]
  rw [List.append_assoc,List.drop_left,List.take_left]

end E5R.Thermostat.ApiRouting
