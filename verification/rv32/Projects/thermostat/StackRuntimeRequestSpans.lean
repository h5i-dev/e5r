import Projects.thermostat.RuntimeRequestSpans
import Projects.thermostat.StackBoard
set_option autoImplicit false
namespace E5R.Thermostat.StackRuntimeRequestSpans
open E5R E5R.Thermostat HttpRequestSpec RuntimeRequestSpans
abbrev B := StackBoard.board
theorem whole {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat}
    (h : RuntimeRequest.Ready c ram input s head amount rawUsed served) : Bytes.Span B ram rx input := by
  have block : Memory.Block B rx input.length := by
    have region := Memory.sub_block StackBoard.available (off := 60436) (m := input.length) (by have := h.available;have := h.bounds.length.1;omega) (by have := h.stable.bound;omega)
    simpa only [show 0x80ff0000#32+60436#32=rx by decide +kernel] using region
  exact Bytes.of_block B ram rx input block (by have := h.stable.bound;omega) h.stable.bytes


theorem raw_span {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat}
    (h : RuntimeRequest.Ready c ram input s head amount rawUsed served) : Bytes.Span B ram rx (raw input rawUsed) := Bytes.take_span (whole h) _


theorem path_span {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat}
    (h : RuntimeRequest.Ready c ram input s head amount rawUsed served) :
    Bytes.Span B ram (rx+BitVec.ofNat 32 head.target.1) (path input head) := Bytes.subspan (whole h) _ _ (target_bounds h)


theorem body_span {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat}
    (h : RuntimeRequest.Ready c ram input s head amount rawUsed served) :
    Bytes.Span B ram (rx+BitVec.ofNat 32 head.len) (body input head amount) := by
  have span := Bytes.subspan (whole h) head.len (head.len+amount) ⟨by omega,h.available⟩
  change Bytes.Span B ram (rx+BitVec.ofNat 32 head.len) ((input.drop head.len).take amount)
  simpa only [show head.len+amount-head.len=amount by omega] using span


theorem query_span {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat}
    (h : RuntimeRequest.Ready c ram input s head amount rawUsed served) : Bytes.Span B ram (MainRequestBuild.queryPtr input head) (query input head) := by
  let start := MainQuerySpec.queryStart (MainQuerySpec.bytes input) head.target.1 head.target.2
  let len := MainQuerySpec.queryLength (MainQuerySpec.bytes input) head.target.1 head.target.2
  have spans := MainQuerySpec.spans (MainQuerySpec.bytes input) head.target.1 head.target.2 (by have := h.bounds.target.2.1;omega)
  have inside := h.contained.1
  have available := h.available
  have ordered : start≤start+len ∧ start+len≤input.length := ⟨by omega,by omega⟩
  have span := Bytes.subspan (whole h) start (start+len) ordered
  change Bytes.Span B ram (rx+BitVec.ofNat 32 start) ((input.drop start).take len)
  simpa only [show start+len-start=len by omega] using span
end E5R.Thermostat.StackRuntimeRequestSpans
