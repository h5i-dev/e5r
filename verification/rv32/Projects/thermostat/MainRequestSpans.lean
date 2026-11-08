import Projects.thermostat.MainRequestBuild
import Projects.thermostat.Subspan
set_option autoImplicit false
namespace E5R.Thermostat.MainRequestSpans
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := MainRequestBuild.B
abbrev rx := MainRequestBuild.rx

def raw (input : List (BitVec 8)) (head : Head) (amount : Nat) := input.take (head.len+amount)
def path (input : List (BitVec 8)) (head : Head) := MainQuerySpec.path input head.target.1 head.target.2
def query (input : List (BitVec 8)) (head : Head) := MainQuerySpec.query input head.target.1 head.target.2
def body (input : List (BitVec 8)) (head : Head) (amount : Nat) := (input.drop head.len).take amount

theorem whole {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat}
    (h : MainRequestBuild.Ready c ram input s head amount served) : Bytes.Span B ram rx input := by
  have block : Memory.Block B rx input.length := by
    have region := Memory.sub_block h.stable.stack (off := 60436) (m := input.length) (by have := h.available;have := h.bounds.length.1;omega) (by have := h.stable.bound;omega)
    simpa only [show 0x80ff0000#32+60436#32=rx by decide +kernel] using region
  exact Bytes.of_block B ram rx input block (by have := h.stable.bound;omega) h.stable.bytes

theorem raw_length {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat}
    (h : MainRequestBuild.Ready c ram input s head amount served) : (raw input head amount).length=head.len+amount := by
  simp only [raw,List.length_take,Nat.min_eq_left h.available]

theorem raw_span {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat}
    (h : MainRequestBuild.Ready c ram input s head amount served) : Bytes.Span B ram rx (raw input head amount) := Bytes.take_span (whole h) _

theorem target_bounds {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat}
    (h : MainRequestBuild.Ready c ram input s head amount served) :
    head.target.1≤MainQuerySpec.position (MainQuerySpec.bytes input) head.target.1 head.target.2 ∧
      MainQuerySpec.position (MainQuerySpec.bytes input) head.target.1 head.target.2≤input.length := by
  have bound := MainQuerySpec.bounds (MainQuerySpec.bytes input) head.target.1 head.target.2 (by have := h.bounds.target.2.1;omega)
  have inside := h.contained.1
  have available := h.available
  exact ⟨bound.1,by omega⟩

theorem path_length {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat}
    (h : MainRequestBuild.Ready c ram input s head amount served) :
    (path input head).length=MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2 := by
  exact Bytes.subspan_length input _ _ (target_bounds h)

theorem path_span {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat}
    (h : MainRequestBuild.Ready c ram input s head amount served) :
    Bytes.Span B ram (rx+BitVec.ofNat 32 head.target.1) (path input head) := Bytes.subspan (whole h) _ _ (target_bounds h)

theorem body_length {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat}
    (h : MainRequestBuild.Ready c ram input s head amount served) : (body input head amount).length=amount := by
  simp only [body,List.length_take,List.length_drop]
  exact Nat.min_eq_left (by have := h.available;omega)

theorem body_span {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat}
    (h : MainRequestBuild.Ready c ram input s head amount served) :
    Bytes.Span B ram (rx+BitVec.ofNat 32 head.len) (body input head amount) := by
  have span := Bytes.subspan (whole h) head.len (head.len+amount) ⟨by omega,h.available⟩
  change Bytes.Span B ram (rx+BitVec.ofNat 32 head.len) ((input.drop head.len).take amount)
  simpa only [show head.len+amount-head.len=amount by omega] using span

theorem query_length {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat}
    (h : MainRequestBuild.Ready c ram input s head amount served) :
    (query input head).length=MainQuerySpec.queryLength (MainQuerySpec.bytes input) head.target.1 head.target.2 := by
  have spans := MainQuerySpec.spans (MainQuerySpec.bytes input) head.target.1 head.target.2 (by have := h.bounds.target.2.1;omega)
  have inside := h.contained.1
  have available := h.available
  simp only [query,MainQuerySpec.query,List.length_take,List.length_drop]
  exact Nat.min_eq_left (by omega)

theorem query_span {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat}
    (h : MainRequestBuild.Ready c ram input s head amount served) : Bytes.Span B ram (MainRequestBuild.queryPtr input head) (query input head) := by
  let start := MainQuerySpec.queryStart (MainQuerySpec.bytes input) head.target.1 head.target.2
  let len := MainQuerySpec.queryLength (MainQuerySpec.bytes input) head.target.1 head.target.2
  have spans := MainQuerySpec.spans (MainQuerySpec.bytes input) head.target.1 head.target.2 (by have := h.bounds.target.2.1;omega)
  have inside := h.contained.1
  have available := h.available
  have ordered : start≤start+len ∧ start+len≤input.length := ⟨by omega,by omega⟩
  have span := Bytes.subspan (whole h) start (start+len) ordered
  change Bytes.Span B ram (rx+BitVec.ofNat 32 start) ((input.drop start).take len)
  simpa only [show start+len-start=len by omega] using span
end E5R.Thermostat.MainRequestSpans
