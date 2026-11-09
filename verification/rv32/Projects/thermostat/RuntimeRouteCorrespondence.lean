import Projects.thermostat.RuntimeRouteTransaction
import Projects.thermostat.RuntimeHeaderLookup
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeRouteCorrespondence
open E5R E5R.Thermostat HttpRequestSpec

theorem reply_raw_prefix {raw original : List (BitVec 8)} {cut : Nat} (same : raw.take cut=original)
    (s : Spec.Snapshot) (method : MainMethodSpec.Method) (path body : List (BitVec 8))
    (entries : List HeaderSpec.Entry) (inside : ∀ e∈entries,HeaderSpec.Bounds cut e) :
    RouteSpec.reply s method path raw body entries=RouteSpec.reply s method path original body entries := by
  unfold RouteSpec.reply
  cases selected : RouteSpec.select path with
  | none => rfl
  | some route =>
    dsimp only
    split
    · cases route with
      | state => rfl
      | setpoint | temp | mode | relay segment => exact RuntimeHeaderLookup.write same s path body _ entries inside
    · rfl

theorem header_bounds {c ram input s head amount rawUsed served lowValue close}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close) :
    ∀ e∈RuntimeRequestInputs.entries head,HeaderSpec.Bounds head.len e := by
  intro e member
  obtain ⟨field,inside,rfl⟩ := List.mem_map.mp member
  obtain ⟨a,b,c,d⟩ := h.stored.contained.2 field inside
  change field.ns≤field.ne ∧ field.ne≤head.len ∧ field.vs≤field.ve ∧ field.ve≤head.len
  exact ⟨by omega,by omega,c,d⟩

theorem raw_prefix {c ram input s head amount rawUsed served lowValue close}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    {original : List (BitVec 8)} (same : input.take head.len=original) :
    (RuntimeRequestSpans.raw input rawUsed).take head.len=original := by
  unfold RuntimeRequestSpans.raw
  rw [List.take_take,Nat.min_eq_left (by have := h.stored.usedBound.1;omega)]
  exact same

theorem method {c ram input s head amount rawUsed served lowValue close}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    {original : List (BitVec 8)} (same : input.take head.len=original) :
    MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=MainMethodSpec.decode (MainMethodBytes.token original head.method.2) := by
  rw [RuntimeHeaderPrefix.method same (by have := h.stored.bounds.target;have := h.stored.contained.1;omega)]

theorem isHead {c ram input s head amount rawUsed served lowValue close}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    {original : List (BitVec 8)} (same : input.take head.len=original) :
    RuntimeRouteTransaction.isHead input head=RuntimeRouteTransaction.isHead original head := by
  unfold RuntimeRouteTransaction.isHead;rw [method h same]

theorem path {c ram input s head amount rawUsed served lowValue close}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    {original : List (BitVec 8)} (same : input.take head.len=original) : RuntimeRequestSpans.path input head=RuntimeRequestSpans.path original head := by
  apply RuntimeHeaderPrefix.path same
  have := h.stored.bounds.target.2.1;have := h.stored.contained.1;omega

theorem reply {c ram input s head amount rawUsed served lowValue close}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    {original body : List (BitVec 8)} (same : input.take head.len=original) (payload : RuntimeRequestSpans.body input head amount=body) :
    RuntimeRouteTransaction.reply s input head amount rawUsed=
      RouteSpec.reply s (MainMethodSpec.decode (MainMethodBytes.token original head.method.2)) (RuntimeRequestSpans.path original head) original body (RuntimeRequestInputs.entries head) := by
  unfold RuntimeRouteTransaction.reply
  rw [method h same,path h same,payload]
  exact reply_raw_prefix (raw_prefix h same) s _ _ body _ (header_bounds h)

theorem close {c ram input s head amount rawUsed served lowValue close}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    {original : List (BitVec 8)} (same : input.take head.len=original) :
    close=MainCloseSpec.mustClose head.minor served original (RuntimeRequestInputs.entries head) :=
  h.closeSpec.trans (RuntimeHeaderLookup.close (raw_prefix h same) _ _ _ (header_bounds h))
end E5R.Thermostat.RuntimeRouteCorrespondence
