import Projects.thermostat.MainTempEntryReset
import Projects.thermostat.MainTempTransaction
import Projects.thermostat.MainTempSuccessReset
set_option autoImplicit false
namespace E5R.Thermostat.MainTempReset
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board
abbrev received := MainTempSuccessReset.received

def reply (wire : Nat → BitVec 8) (fuel : Nat) (head : Head) (amount : Nat) :=
  TempHttpSpec.run Spec.initial (MainRequestSpans.raw (received wire fuel head amount) head amount)
    (MainRequestSpans.body (received wire fuel head amount) head amount) (MainRequestInputs.entries head)

/-- Every accepted fixed-length POST /temp body/credential case from reset.
    The observable pure evaluator determines401/400/200, full response bytes
    and committed RAM. No auth/decode/transition outcome or layout is assumed. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (wire : Nat → BitVec 8)
    (headerPlan : MainHeaderStreamPlan.Plan) (fuel : Nat) (head : Head) (amount : Nat) (bodyPlan : MainLengthStreamPlan.Plan)
    (hp : c.pc=0x80000000#32) (mpp : c.mpp=0 ∨ c.mpp=3) (masked : c.mie_=false)
    (stack : Memory.Block B 0x80ff0000#32 65536) (space : fuel≤2048)
    (headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 fuel)
    (accepted : (consume wire fuel []).result=.done head) (kind : head.framing=.length amount)
    (bodyValid : MainLengthStreamPlan.Valid bodyPlan wire (consume wire fuel []).input.length
      (head.len+amount-(consume wire fuel []).input.length))
    (route : MainRequestSpans.path (received wire fuel head amount) head=WireSpec.ascii "/temp")
    (method : MainMethodSpec.decode (MainMethodBytes.token (received wire fuel head amount) head.method.2)=.post)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot)
    (hhs : ∀ close, (hs close).length=(ResponseHeadSpec.bytes (reply wire fuel head amount).status (reply wire fuel head amount).mime (reply wire fuel head amount).payload.length close).length)
    (hbs : bs.length=(reply wire fuel head amount).payload.length) :
    let input := (consume wire fuel []).input
    let missing := head.len+amount-input.length
    let bytes := received wire fuel head amount
    let reads := MainHeaderStreamPlan.logs headerPlan 0 (consume wire fuel []).received++MainLengthStreamPlan.logs bodyPlan input.length missing
    let expected := reply wire fuel head amount
    ∃ n d after close,
      n≤12380+212*(MainRequestInputs.entries head).length+18*(MainRequestSpans.body bytes head amount).length+
        (77+86*(head.len+amount))*head.headers.length+5*(head.target.2-head.target.1)+MainHeaderStreamPlan.cost headerPlan 0 fuel+
        MainLengthStreamPlan.cost bodyPlan input.length missing+
        UartWriteAll.time (ResponseHeadSpec.bytes expected.status expected.mime expected.payload.length close) (hs close)+UartWriteAll.time expected.payload bs ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (reads++(UartTxLoop.reads (hs close)++UartTxLoop.reads bs))
        (UartTxLoop.events (ResponseHeadSpec.bytes expected.status expected.mime expected.payload.length close)++UartTxLoop.events expected.payload) ∧
      Observed.input (reads++(UartTxLoop.reads (hs close)++UartTxLoop.reads bs))=bytes ∧
      close=MainCloseSpec.mustClose head.minor 1 (MainRequestSpans.raw bytes head amount) (MainRequestInputs.entries head) ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧ d.get 2=0x80ffeb90#32 ∧ d.get 8=0x80fff814#32 ∧ d.mie_=false ∧
      AppState.At after expected.state ∧ Engine.InvariantAt after 0x80ffebbc#32 := by
  obtain ⟨first,a,mid,close,bound,trace,ready,bytes⟩ := MainTempEntryReset.contract c ram wire headerPlan fuel head amount bodyPlan hp mpp masked stack space headerValid accepted kind bodyValid route method
  obtain ⟨d,last,after,lastBound,sent,pc,sp,fp,csr,app,inv,_⟩ := MainTempTransaction.contract ready (hs close) bs (hhs close) hbs
  have inputOnly : Observed.input ((MainHeaderStreamPlan.logs headerPlan 0 (consume wire fuel []).received++MainLengthStreamPlan.logs bodyPlan (consume wire fuel []).input.length (head.len+amount-(consume wire fuel []).input.length))++(UartTxLoop.reads (hs close)++UartTxLoop.reads bs))=received wire fuel head amount := by
    simp only [Observed.input_append,UartTxLoop.no_input,List.append_nil]
    simpa only [Observed.input_append,received,MainTempSuccessReset.received] using bytes
  refine ⟨first+last,d,after,close,?_,trace.trans sent,inputOnly,ready.closeSpec,pc,sp,fp,(congrArg Prod.fst csr).trans ready.masked,app,inv⟩
  dsimp only [received,MainTempSuccessReset.received,reply] at lastBound ⊢
  omega
end E5R.Thermostat.MainTempReset
