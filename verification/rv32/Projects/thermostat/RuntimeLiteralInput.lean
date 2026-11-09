import Projects.thermostat.RuntimeRouteEnvelope
import Projects.thermostat.MainRouteLiteralView
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeLiteralInput
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := RuntimeRouteEnvelope.B
abbrev sp := RuntimeRouteEnvelope.sp
abbrev fp := RuntimeRouteEnvelope.fp
abbrev rx := RuntimeRouteEnvelope.rx

/-- Actual arguments at any fixed literal pattern call. The live Request
    layout and protocol bytes remain independent of the selected pattern. -/
structure At (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) (head : Head)
    (amount rawUsed served : Nat) (lowValue : Word) (close : Bool) (pattern patternLength ret : Word) : Prop where
  live : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close
  pc : c.pc=0x8000283a#32
  ret : c.get 1=ret
  pattern : c.get 10=pattern
  patternLength : c.get 11=patternLength
  path : c.get 12=rx+BitVec.ofNat 32 head.target.1
  pathLength : c.get 13=MainRequestBuild.pathLength input head
  params : c.get 14=0x80fff9d0#32

/-- Named G3 obligation for remaining API routes: obtain a literal byte span,
    length and matcher-stack separation from the real stored Request. -/
theorem literal_view {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat} {lowValue : Word} {close : Bool}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close) (literal : List (BitVec 8))
    (route : RuntimeRequestSpans.path input head=literal) :
    Bytes.Span B ram (rx+BitVec.ofNat 32 head.target.1) literal ∧
    MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2=literal.length ∧
    WordRegions.Disjoint (rx+BitVec.ofNat 32 head.target.1) literal.length 0x80ffeb30#32 96 := by
  have whole : Bytes.Span B ram rx input := by
    have block := Memory.sub_block h.stable.stack (off := 60436) (m := input.length)
      (by have available := Nat.le_trans h.stored.usedBound.1 h.stored.usedBound.2;have := h.stored.bounds.length.1;omega) (by have := h.stable.bound;omega)
    have rxblock : Memory.Block B rx input.length := by
      simpa only [show 0x80ff0000#32+60436#32=rx by decide +kernel] using block
    exact Bytes.of_block B ram rx input rxblock (by have := h.stable.bound;omega) h.stable.bytes
  have limits : head.target.1≤MainQuerySpec.position (MainQuerySpec.bytes input) head.target.1 head.target.2 ∧
      MainQuerySpec.position (MainQuerySpec.bytes input) head.target.1 head.target.2≤input.length := by
    have bounds := MainQuerySpec.bounds (MainQuerySpec.bytes input) head.target.1 head.target.2 (by have := h.stored.bounds.target.2.1;omega)
    have := h.stored.contained.1
    have available := Nat.le_trans h.stored.usedBound.1 h.stored.usedBound.2
    omega
  have pathBytes : Bytes.Span B ram (rx+BitVec.ofNat 32 head.target.1) literal := by
    have span := Bytes.subspan whole _ _ limits
    change Bytes.Span B ram (rx+BitVec.ofNat 32 head.target.1) (RuntimeRequestSpans.path input head) at span
    rw [route] at span
    exact span
  have length : MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2=literal.length := by
    have size := Bytes.subspan_length input _ _ limits
    change (RuntimeRequestSpans.path input head).length=MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2 at size
    rw [route] at size
    exact size.symm
  refine ⟨pathBytes,length,?_⟩
  intro i j
  have start : head.target.1+literal.length≤input.length := by
    have := limits.2
    change MainQuerySpec.position (MainQuerySpec.bytes input) head.target.1 head.target.2-head.target.1=literal.length at length
    omega
  have separated := WordZero.separated 0x80ffeb30#32 rx 96 2048 (by decide +kernel) (by decide +kernel) j
    ⟨head.target.1+i.val,by have := i.isLt;have := h.stable.bound;omega⟩
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  exact Ne.symm separated
end E5R.Thermostat.RuntimeLiteralInput
