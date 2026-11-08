import Projects.thermostat.MainTempEntryReset
import Projects.thermostat.MainTempSuccess
set_option autoImplicit false
namespace E5R.Thermostat.MainTempSuccessReset
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board

def received (wire : Nat → BitVec 8) (fuel : Nat) (head : Head) (amount : Nat) :=
  (consume wire fuel []).input++arrivals wire (consume wire fuel []).input.length (head.len+amount-(consume wire fuel []).input.length)

/-- One actual authorized/decoded-success POST /temp from reset to its exact
    HTTP/UART reply and persisted commit. All handler layouts are derived.
    Pure accepted-head/framing/route/method/outcome cases remain explicit. -/
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
    (cmd : Spec.Command) (res : Spec.Success)
    (allow : AuthSpec.authorized (HeaderSpec.lookup (MainRequestSpans.raw (received wire fuel head amount) head amount) (WireSpec.ascii "authorization") (MainRequestInputs.entries head)) (WireSpec.ascii "dev-key")=true)
    (decoded : WireSpec.decode (WireSpec.ascii "/temp") (MainRequestSpans.body (received wire fuel head amount) head amount) none=.ok cmd)
    (result : Spec.transition true Spec.initial cmd=.ok res)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot)
    (hhs : ∀ close, (hs close).length=(ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot res.reply).length close).length)
    (hbs : bs.length=(ReplyJson.snapshot res.reply).length) :
    let input := (consume wire fuel []).input
    let missing := head.len+amount-input.length
    let bytes := received wire fuel head amount
    let reads := MainHeaderStreamPlan.logs headerPlan 0 (consume wire fuel []).received++MainLengthStreamPlan.logs bodyPlan input.length missing
    ∃ n d after close,
      n≤12380+212*(MainRequestInputs.entries head).length+18*(MainRequestSpans.body bytes head amount).length+
        (77+86*(head.len+amount))*head.headers.length+5*(head.target.2-head.target.1)+MainHeaderStreamPlan.cost headerPlan 0 fuel+
        MainLengthStreamPlan.cost bodyPlan input.length missing+
        UartWriteAll.time (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot res.reply).length close) (hs close)+UartWriteAll.time (ReplyJson.snapshot res.reply) bs ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (reads++(UartTxLoop.reads (hs close)++UartTxLoop.reads bs))
        (UartTxLoop.events (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot res.reply).length close)++UartTxLoop.events (ReplyJson.snapshot res.reply)) ∧
      Observed.input (reads++(UartTxLoop.reads (hs close)++UartTxLoop.reads bs))=bytes ∧
      close=MainCloseSpec.mustClose head.minor 1 (MainRequestSpans.raw bytes head amount) (MainRequestInputs.entries head) ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧ d.get 2=0x80ffeb90#32 ∧ d.get 8=0x80fff814#32 ∧ d.mie_=false ∧
      AppState.At after (Spec.commit Spec.initial (.ok res)) ∧ Engine.InvariantAt after 0x80ffebbc#32 := by
  obtain ⟨first,a,mid,close,bound,trace,ready,bytes⟩ := MainTempEntryReset.contract c ram wire headerPlan fuel head amount bodyPlan hp mpp masked stack space headerValid accepted kind bodyValid route method
  obtain ⟨d,last,after,lastBound,sent,pc,sp,fp,csr,app,inv,_⟩ := MainTempSuccess.contract ready cmd res allow decoded result (hs close) bs (hhs close) hbs
  have inputOnly : Observed.input ((MainHeaderStreamPlan.logs headerPlan 0 (consume wire fuel []).received++MainLengthStreamPlan.logs bodyPlan (consume wire fuel []).input.length (head.len+amount-(consume wire fuel []).input.length))++(UartTxLoop.reads (hs close)++UartTxLoop.reads bs))=received wire fuel head amount := by
    simp only [Observed.input_append,UartTxLoop.no_input,List.append_nil]
    simpa only [Observed.input_append,received] using bytes
  exact ⟨first+last,d,after,close,by dsimp only [received];omega,trace.trans sent,inputOnly,ready.closeSpec,pc,sp,fp,(congrArg Prod.fst csr).trans ready.masked,app,inv⟩
end E5R.Thermostat.MainTempSuccessReset
