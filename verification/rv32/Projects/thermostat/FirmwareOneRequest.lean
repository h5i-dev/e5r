import Projects.thermostat.ApiReplySpec
import Projects.thermostat.MainReadReset
import Projects.thermostat.MainTempReset
import Projects.thermostat.MainSetpointReset
import Projects.thermostat.MainModeReset
import Projects.thermostat.MainRelayReset
set_option autoImplicit false
namespace E5R.Thermostat.Firmware
open E5R E5R.Thermostat HttpRequestSpec ApiRequestSpec MainHeaderStreamSpec

def reads (r : Fixed11) (headerPlan : MainHeaderStreamPlan.Plan) (bodyPlan : MainLengthStreamPlan.Plan)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot) (close : Bool) :=
  (MainHeaderStreamPlan.logs headerPlan 0 r.headBytes.length++
    MainLengthStreamPlan.logs bodyPlan r.headBytes.length r.body.length)++
    (UartTxLoop.reads (hs close)++UartTxLoop.reads bs)

private def Runs (r : Fixed11) (c : Core) (ram : Word → BitVec 8)
    (headerPlan : MainHeaderStreamPlan.Plan) (bodyPlan : MainLengthStreamPlan.Plan)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot)
    (n : Nat) (d : Core) (after : Word → BitVec 8) (close : Bool) : Prop :=
  let reply := r.reply Spec.initial
  Observed.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,after⟩ (reads r headerPlan bodyPlan hs bs close)
    (UartTxLoop.events (ResponseHeadSpec.bytes reply.status reply.mime reply.payload.length close)++UartTxLoop.events reply.payload) ∧
  Observed.input (reads r headerPlan bodyPlan hs bs close)=r.bytes ∧
  close=ApiReplySpec.close r ∧
  d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧
  d.get 2=0x80ffeb90#32 ∧ d.get 8=0x80fff814#32 ∧ d.mie_=false ∧
  AppState.At after reply.state ∧ Engine.InvariantAt after 0x80ffebbc#32

/-- T1: every structural fixed-length HTTP/1.1 API request, including bad
    credentials and arbitrary command bodies, from actual reset through the
    actual UART/parser/router/auth/kernel/sender to a committed reply boundary.
    Only loader/reset facts and explicit finite delivery/readiness remain. -/
theorem one_request (r : Fixed11) (c : Core) (ram : Word → BitVec 8) (wire : Nat → BitVec 8)
    (headerPlan : MainHeaderStreamPlan.Plan) (bodyPlan : MainLengthStreamPlan.Plan)
    (hp : c.pc=0x80000000#32) (mpp : c.mpp=0 ∨ c.mpp=3) (masked : c.mie_=false)
    (stack : Memory.Block UartPlatform.board 0x80ff0000#32 65536)
    (delivers : ∀ k (hk : k<r.bytes.length), wire k=r.bytes[k]'hk)
    (headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 r.headBytes.length)
    (bodyValid : MainLengthStreamPlan.Valid bodyPlan wire r.headBytes.length r.body.length)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot)
    (hhs : ∀ close, (hs close).length=(ResponseHeadSpec.bytes (r.reply Spec.initial).status
      (r.reply Spec.initial).mime (r.reply Spec.initial).payload.length close).length)
    (hbs : bs.length=(r.reply Spec.initial).payload.length) :
    ∃ n d after,
      Observed.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,after⟩
        (reads r headerPlan bodyPlan hs bs (ApiReplySpec.close r))
        (UartTxLoop.events (ResponseHeadSpec.bytes (r.reply Spec.initial).status (r.reply Spec.initial).mime
          (r.reply Spec.initial).payload.length (ApiReplySpec.close r))++UartTxLoop.events (r.reply Spec.initial).payload) ∧
      Observed.input (reads r headerPlan bodyPlan hs bs (ApiReplySpec.close r))=r.bytes ∧
      d.pc=(if ApiReplySpec.close r then 0x80000978#32 else 0x800017be#32) ∧
      d.get 2=0x80ffeb90#32 ∧ d.get 8=0x80fff814#32 ∧ d.mie_=false ∧
      AppState.At after (r.reply Spec.initial).state ∧ ramRead after 0x80ffebbc#32 .w=0#32 ∧
      Spec.Inv (r.reply Spec.initial).state ∧ Engine.InvariantAt after 0x80ffebbc#32 := by
  have runExact := ApiConsume.exact_head r wire delivers
  have accepted : (consume wire r.headBytes.length []).result=.done r.head := by rw [runExact]
  have headMinor : r.head.minor=1 := rfl
  have headLength : r.head.len=r.headBytes.length := rfl
  have received : MainTempSuccessReset.received wire r.headBytes.length r.head r.body.length=r.bytes :=
    ApiConsume.delivered r wire delivers
  have receivedBytes := ApiConsume.delivered r wire delivers
  have path : MainRequestSpans.path (MainTempSuccessReset.received wire r.headBytes.length r.head r.body.length) r.head=r.route.path := by
    rw [received,ApiRouting.path]
  have method : MainMethodSpec.decode (MainMethodBytes.token (MainTempSuccessReset.received wire r.headBytes.length r.head r.body.length) r.head.method.2)=ApiRouting.method r.route := by
    rw [received,ApiRouting.method_case]
  have space : r.headBytes.length≤2048 := by have := r.headBound; exact Nat.le_trans this (by decide)
  have actualBody : MainLengthStreamPlan.Valid bodyPlan wire (consume wire r.headBytes.length []).input.length
      (r.head.len+r.body.length-(consume wire r.headBytes.length []).input.length) := by
    simpa only [runExact,headLength,Nat.add_sub_cancel_left] using bodyValid
  have run : ∃ n d after close, Runs r c ram headerPlan bodyPlan hs bs n d after close := by
    cases routeEq : r.route with
    | state =>
      have expected : r.reply Spec.initial=⟨Spec.initial,200,WireSpec.ascii "application/json",ReplyJson.snapshot Spec.initial⟩ := by
        unfold Fixed11.reply; rw [routeEq]
      obtain ⟨n,d,after,close,_,trace,rx,closure,pc,sp,fp,mask,app,inv⟩ := MainReadReset.contract
        c ram wire headerPlan r.headBytes.length r.head r.body.length bodyPlan hp mpp masked stack space headerValid accepted rfl actualBody
        (by simpa only [MainTempSuccessReset.received,routeEq,Route.path] using path) (by simpa only [MainTempSuccessReset.received,routeEq,ApiRouting.method] using method)
        hs bs (by simpa only [expected] using hhs) (by simpa only [expected] using hbs)
      refine ⟨n,d,after,close,?_⟩
      rw [receivedBytes] at rx closure
      simp only [runExact,headLength,headMinor,Nat.add_sub_cancel_left,ApiRouting.raw,ApiRouting.entries] at trace rx closure
      simpa only [Runs,reads,expected,ApiReplySpec.close] using
        (show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from ⟨trace,rx,closure,pc,sp,fp,mask,app,inv⟩)
    | temp =>
      have replyEq : MainTempReset.reply wire r.headBytes.length r.head r.body.length=r.reply Spec.initial := by
        unfold MainTempReset.reply
        dsimp only [MainTempReset.received]
        rw [received,ApiRouting.raw,ApiRouting.body,ApiRouting.entries]
        rw [←ApiReplySpec.temp]
        simp only [Fixed11.reply,routeEq,Route.path,Route.capture]
      obtain ⟨n,d,after,close,_,trace,rx,closure,pc,sp,fp,mask,app,inv⟩ := MainTempReset.contract
        c ram wire headerPlan r.headBytes.length r.head r.body.length bodyPlan hp mpp masked stack space headerValid accepted rfl actualBody
        (by simpa only [MainTempSuccessReset.received,routeEq,Route.path] using path) (by simpa only [MainTempSuccessReset.received,routeEq,ApiRouting.method] using method)
        hs bs (by simpa only [replyEq] using hhs) (by simpa only [replyEq] using hbs)
      refine ⟨n,d,after,close,?_⟩
      simp only [replyEq,received,runExact,headLength,headMinor,Nat.add_sub_cancel_left,ApiRouting.raw,ApiRouting.entries] at trace rx closure app
      simpa only [Runs,reads,ApiReplySpec.close] using
        (show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from ⟨trace,rx,closure,pc,sp,fp,mask,app,inv⟩)
    | setpoint =>
      have replyEq : MainSetpointReset.reply wire r.headBytes.length r.head r.body.length=r.reply Spec.initial := by
        unfold MainSetpointReset.reply
        dsimp only [MainSetpointReset.received]
        rw [received,ApiRouting.raw,ApiRouting.body,ApiRouting.entries]
        simp only [Fixed11.reply,routeEq,Route.path,Route.capture]
      obtain ⟨n,d,after,close,_,trace,rx,closure,pc,sp,fp,mask,app,inv⟩ := MainSetpointReset.contract
        c ram wire headerPlan r.headBytes.length r.head r.body.length bodyPlan hp mpp masked stack space headerValid accepted rfl actualBody
        (by simpa only [MainTempSuccessReset.received,routeEq,Route.path] using path) (by simpa only [MainTempSuccessReset.received,routeEq,ApiRouting.method] using method)
        hs bs (by simpa only [replyEq] using hhs) (by simpa only [replyEq] using hbs)
      refine ⟨n,d,after,close,?_⟩
      simp only [replyEq,received,runExact,headLength,headMinor,Nat.add_sub_cancel_left,ApiRouting.raw,ApiRouting.entries] at trace rx closure app
      simpa only [Runs,reads,ApiReplySpec.close] using
        (show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from ⟨trace,rx,closure,pc,sp,fp,mask,app,inv⟩)
    | mode =>
      have replyEq : MainModeReset.reply wire r.headBytes.length r.head r.body.length=r.reply Spec.initial := by
        unfold MainModeReset.reply
        dsimp only [MainModeReset.received]
        rw [received,ApiRouting.raw,ApiRouting.body,ApiRouting.entries]
        simp only [Fixed11.reply,routeEq,Route.path,Route.capture]
      obtain ⟨n,d,after,close,_,trace,rx,closure,pc,sp,fp,mask,app,inv⟩ := MainModeReset.contract
        c ram wire headerPlan r.headBytes.length r.head r.body.length bodyPlan hp mpp masked stack space headerValid accepted rfl actualBody
        (by simpa only [MainTempSuccessReset.received,routeEq,Route.path] using path) (by simpa only [MainTempSuccessReset.received,routeEq,ApiRouting.method] using method)
        hs bs (by simpa only [replyEq] using hhs) (by simpa only [replyEq] using hbs)
      refine ⟨n,d,after,close,?_⟩
      simp only [replyEq,received,runExact,headLength,headMinor,Nat.add_sub_cancel_left,ApiRouting.raw,ApiRouting.entries] at trace rx closure app
      simpa only [Runs,reads,ApiReplySpec.close] using
        (show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from ⟨trace,rx,closure,pc,sp,fp,mask,app,inv⟩)
    | relay segment =>
      have segmentValid : segment≠[] ∧ ∀ b∈segment, isTargetByte b.toNat=true ∧ b≠47#8 ∧ b≠63#8 := by
        have valid := r.routeValid; rw [routeEq] at valid; exact valid
      have replyEq : MainRelayReset.reply wire r.headBytes.length r.head r.body.length segment=r.reply Spec.initial := by
        unfold MainRelayReset.reply
        dsimp only [MainRelayReset.received]
        rw [received,ApiRouting.raw,ApiRouting.body,ApiRouting.entries]
        simp only [Fixed11.reply,routeEq,Route.path,Route.capture,MainRelayCaptured.path]
      obtain ⟨n,d,after,close,_,trace,rx,closure,pc,sp,fp,mask,app,inv⟩ := MainRelayReset.contract
        c ram wire headerPlan r.headBytes.length r.head r.body.length bodyPlan hp mpp masked stack space headerValid accepted rfl actualBody
        segment segmentValid.1 (fun b hb => (segmentValid.2 b hb).2.1)
        (by simpa only [routeEq,Route.path,MainRelayCaptured.path] using path) (by simpa only [MainTempSuccessReset.received,routeEq,ApiRouting.method] using method)
        hs bs (by simpa only [replyEq] using hhs) (by simpa only [replyEq] using hbs)
      refine ⟨n,d,after,close,?_⟩
      simp only [replyEq,received,runExact,headLength,headMinor,Nat.add_sub_cancel_left,ApiRouting.raw,ApiRouting.entries] at trace rx closure app
      simpa only [Runs,reads,ApiReplySpec.close] using
        (show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from ⟨trace,rx,closure,pc,sp,fp,mask,app,inv⟩)
  obtain ⟨n,d,after,close,trace,rx,closure,pc,sp,fp,mask,app,inv⟩ := run
  subst close
  exact ⟨n,d,after,trace,rx,pc,sp,fp,mask,app,app.available,ApiReplySpec.invariant r Spec.initial Spec.initial_inv,inv⟩

end E5R.Thermostat.Firmware
