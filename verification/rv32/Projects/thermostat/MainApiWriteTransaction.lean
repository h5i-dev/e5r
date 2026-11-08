import Projects.thermostat.ApiWriteHttpSpec
import Projects.thermostat.MainApiWriteCallerSuccess
import Projects.thermostat.MainApiWriteCallerError
import Projects.thermostat.MainApiWriteCallerRefusal
set_option autoImplicit false
namespace E5R.Thermostat.MainApiWriteCaller
open E5R E5R.Thermostat HttpRequestSpec

/-- Named G3/G4/G5 join for all real write callers: authentication, decoding
    and kernel outcomes are derived by splitting the independent pure evaluator. -/
theorem transaction {kind : Fin 4} {future : Word} {path : List (BitVec 8)} {first : Option (List (BitVec 8))}
    {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot}
    {head : Head} {amount served : Nat} {close : Bool}
    (h : Ready kind future path first c ram input s head amount served close)
    (hs bs : List UartTxLoop.Slot)
    (hhs : hs.length=(ResponseHeadSpec.bytes
      (ApiWriteHttpSpec.run s path first (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).status
      (ApiWriteHttpSpec.run s path first (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).mime
      (ApiWriteHttpSpec.run s path first (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).payload.length close).length)
    (hbs : bs.length=(ApiWriteHttpSpec.run s path first (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).payload.length) :
    let reply := ApiWriteHttpSpec.run s path first (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)
    ∃ d n after, n≤212*(MainRequestInputs.entries head).length+18*(MainRequestSpans.body input head amount).length+7045+
        UartWriteAll.time (ResponseHeadSpec.bytes reply.status reply.mime reply.payload.length close) hs+UartWriteAll.time reply.payload bs ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
        (UartTxLoop.events (ResponseHeadSpec.bytes reply.status reply.mime reply.payload.length close)++UartTxLoop.events reply.payload) ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧ d.get 2=0x80ffeb90#32 ∧ d.get 8=fp ∧ d.sameCsr c ∧
      AppState.At after reply.state ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧ ViewFrame.Region ram after 0x80ffec14#32 2048 := by
  dsimp only
  cases allowed : AuthSpec.authorized (HeaderSpec.lookup (MainRequestSpans.raw input head amount) (WireSpec.ascii "authorization") (MainRequestInputs.entries head)) (WireSpec.ascii "dev-key") with
  | false =>
    simp only [ApiWriteHttpSpec.run,allowed,Bool.false_eq_true,ite_false,List.length_nil] at hhs hbs ⊢
    have emptySlots : bs=[] := List.eq_nil_of_length_eq_zero hbs
    subst bs
    obtain ⟨d,n,after,bound,trace,pc,sp,fp,csr,app,inv,rx⟩ := refusal h 401 (Or.inl ⟨allowed,rfl⟩) (by decide) (by decide) hs hhs
    refine ⟨d,n,after,by omega,?_,pc,sp,fp,csr,app,inv,rx⟩
    simpa only [UartTxLoop.reads,List.flatMap_nil,UartTxLoop.events,List.map_nil,List.append_nil] using trace
  | true =>
    cases decoded : WireSpec.decode path (MainRequestSpans.body input head amount) first with
    | error status =>
      simp only [ApiWriteHttpSpec.run,allowed,ite_true,decoded,List.length_nil] at hhs hbs ⊢
      have emptySlots : bs=[] := List.eq_nil_of_length_eq_zero hbs
      subst bs
      have statuses := ApiWriteHttpSpec.decode_errors path (MainRequestSpans.body input head amount) first status decoded
      obtain ⟨d,n,after,bound,trace,pc,sp,fp,csr,app,inv,rx⟩ := refusal h status (Or.inr ⟨allowed,decoded⟩) (by omega) (by omega) hs hhs
      refine ⟨d,n,after,by omega,?_,pc,sp,fp,csr,app,inv,rx⟩
      simpa only [UartTxLoop.reads,List.flatMap_nil,UartTxLoop.events,List.map_nil,List.append_nil] using trace
    | ok cmd =>
      cases result : Spec.transition true s cmd with
      | error err =>
        simp only [ApiWriteHttpSpec.run,allowed,ite_true,decoded,result] at hhs hbs ⊢
        obtain ⟨d,n,after,bound,trace,pc,sp,fp,csr,app,inv,rx⟩ := error h cmd err allowed decoded result hs bs hhs hbs
        exact ⟨d,n,after,by omega,trace,pc,sp,fp,csr,app,inv,rx⟩
      | ok res =>
        simp only [ApiWriteHttpSpec.run,allowed,ite_true,decoded,result] at hhs hbs ⊢
        exact success h cmd res allowed decoded result hs bs hhs hbs
end E5R.Thermostat.MainApiWriteCaller
