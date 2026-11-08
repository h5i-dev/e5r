import Projects.thermostat.TempHttpSpec
import Projects.thermostat.MainTempSuccess
import Projects.thermostat.MainTempRefusals
set_option autoImplicit false
namespace E5R.Thermostat.MainTempTransaction
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board

/-- Every raw POST /temp body and credential outcome, with no auth/decode/
    transition-success premise. The pure reply determines exact bytes/state. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainTempWriteInput.Ready c ram input s head amount served close)
    (hs bs : List UartTxLoop.Slot)
    (hhs : hs.length=(ResponseHeadSpec.bytes
      (TempHttpSpec.run s (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).status
      (TempHttpSpec.run s (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).mime
      (TempHttpSpec.run s (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).payload.length close).length)
    (hbs : bs.length=(TempHttpSpec.run s (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).payload.length) :
    let reply := TempHttpSpec.run s (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)
    ∃ d n after, n≤212*(MainRequestInputs.entries head).length+18*(MainRequestSpans.body input head amount).length+7045+
        UartWriteAll.time (ResponseHeadSpec.bytes reply.status reply.mime reply.payload.length close) hs+UartWriteAll.time reply.payload bs ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
        (UartTxLoop.events (ResponseHeadSpec.bytes reply.status reply.mime reply.payload.length close)++UartTxLoop.events reply.payload) ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧ d.get 2=0x80ffeb90#32 ∧ d.get 8=0x80fff814#32 ∧ d.sameCsr c ∧
      AppState.At after reply.state ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧ ViewFrame.Region ram after 0x80ffec14#32 2048 := by
  dsimp only
  cases allowed : AuthSpec.authorized (HeaderSpec.lookup (MainRequestSpans.raw input head amount) (WireSpec.ascii "authorization") (MainRequestInputs.entries head)) (WireSpec.ascii "dev-key") with
  | false =>
    simp only [TempHttpSpec.run,allowed,Bool.false_eq_true,ite_false,List.length_nil] at hhs hbs ⊢
    have emptySlots : bs=[] := List.eq_nil_of_length_eq_zero hbs
    subst bs
    obtain ⟨d,n,after,bound,trace,pc,sp,fp,csr,app,inv,rx⟩ := MainTempRefusals.contract_exact h 401 (Or.inl ⟨allowed,rfl⟩) (by decide) (by decide) hs hhs
    refine ⟨d,n,after,by omega,?_,pc,sp,fp,csr,app,inv,rx⟩
    simpa only [UartTxLoop.reads,List.flatMap_nil,UartTxLoop.events,List.map_nil,List.append_nil] using trace
  | true =>
    cases parsed : DecimalSpec.parse (TrimMath.trim (MainRequestSpans.body input head amount)) with
    | none =>
      simp only [TempHttpSpec.run,allowed,ite_true,parsed,List.length_nil] at hhs hbs ⊢
      have emptySlots : bs=[] := List.eq_nil_of_length_eq_zero hbs
      subst bs
      have rejected : WireSpec.decode (WireSpec.ascii "/temp") (MainRequestSpans.body input head amount) none=.error 400 := by
        rw [TempHttpSpec.decode,parsed]
      obtain ⟨d,n,after,bound,trace,pc,sp,fp,csr,app,inv,rx⟩ := MainTempRefusals.contract_exact h 400 (Or.inr ⟨allowed,rejected⟩) (by decide) (by decide) hs hhs
      refine ⟨d,n,after,by omega,?_,pc,sp,fp,csr,app,inv,rx⟩
      simpa only [UartTxLoop.reads,List.flatMap_nil,UartTxLoop.events,List.map_nil,List.append_nil] using trace
    | some temperature =>
      simp only [TempHttpSpec.run,allowed,ite_true,parsed,List.length_nil] at hhs hbs ⊢
      have decoded : WireSpec.decode (WireSpec.ascii "/temp") (MainRequestSpans.body input head amount) none=.ok (.reportTemp temperature) := by
        rw [TempHttpSpec.decode,parsed]
      exact MainTempSuccess.contract h (.reportTemp temperature) ⟨some (TempHttpSpec.next s temperature),TempHttpSpec.next s temperature⟩
        allowed decoded (TempHttpSpec.transition s temperature) hs bs hhs hbs
end E5R.Thermostat.MainTempTransaction
