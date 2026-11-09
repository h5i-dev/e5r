import Projects.thermostat.RuntimeReadTransaction
import Projects.thermostat.RuntimeHeadTransaction
import Projects.thermostat.RuntimeLiteralWriteTransaction
import Projects.thermostat.RuntimeRelayWriteTransaction
import Projects.thermostat.RuntimeRouteRefusal
import Projects.thermostat.RuntimeRouteRelayWrongMethod
import Projects.thermostat.RouteCaseSpec
set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.RuntimeRouteTransaction
open E5R E5R.Thermostat HttpRequestSpec

def reply (s : Spec.Snapshot) (input : List (BitVec 8)) (head : Head) (amount rawUsed : Nat) :=
  RouteSpec.reply s (MainMethodSpec.decode (MainMethodBytes.token input head.method.2)) (RuntimeRequestSpans.path input head)
    (RuntimeRequestSpans.raw input rawUsed) (RuntimeRequestSpans.body input head amount) (RuntimeRequestInputs.entries head)

def isHead (input : List (BitVec 8)) (head : Head) := decide (MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.head)

def Done (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot) (input : List (BitVec 8)) (head : Head)
    (amount rawUsed served : Nat) (close : Bool) (hs bs : List UartTxLoop.Slot) : Prop :=
  let response := reply s input head amount rawUsed
  ∃ n d after,Observed.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
    (UartTxLoop.events (ResponseHeadSpec.bytes response.status response.mime response.payload.length close)++
      UartTxLoop.events (ResponseHeadSpec.body response.status (isHead input head) response.payload)) ∧
    LoopReady.At d after response.state (if close then 0 else served)

/-- Exhaustive actual route/method/auth/body/kernel/reply execution from the
    first real matcher return. The pure router chooses every branch; all
    response bytes, committed state and next-loop layout are conclusions. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32)
    (result : c.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32)) (captures : c.get 11=0#32)
    (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys) (metadata : LoopTransactionMemory.At ram used)
    (hs bs : List UartTxLoop.Slot)
    (hhs : hs.length=(ResponseHeadSpec.bytes (reply s input head amount rawUsed).status (reply s input head amount rawUsed).mime (reply s input head amount rawUsed).payload.length close).length)
    (hbs : bs.length=(ResponseHeadSpec.body (reply s input head amount rawUsed).status (isHead input head) (reply s input head amount rawUsed).payload).length) :
    Done c ram s input head amount rawUsed served close hs bs := by
  have emptyBody (status : Nat) : ResponseHeadSpec.body status (isHead input head) []=[] := by
    simp only [ResponseHeadSpec.body,ite_self]
  have finishEmpty (status : Nat) (same : reply s input head amount rawUsed=⟨s,status,[],[]⟩)
      (execute : hs.length=(ResponseHeadSpec.bytes status [] 0 close).length →
        ∃ n d after,Observed.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs)
          (UartTxLoop.events (ResponseHeadSpec.bytes status [] 0 close)) ∧ LoopReady.At d after s (if close then 0 else served)) :
      Done c ram s input head amount rawUsed served close hs bs := by
    have nil : bs=[] := List.eq_nil_of_length_eq_zero (by simpa only [same,emptyBody,List.length_nil] using hbs)
    subst bs
    obtain ⟨n,d,after,trace,ready⟩ := execute (by simpa only [same,List.length_nil] using hhs)
    refine ⟨n,d,after,?_,?_⟩
    · simpa only [same,emptyBody,List.length_nil,UartTxLoop.reads,UartTxLoop.events,List.flatMap_nil,List.map_nil,List.append_nil] using trace
    · simpa only [same] using ready
  have refused
      (denied : ∀ kind : RouteLiteralInfo.Kind,RuntimeRequestSpans.path input head=RouteLiteralInfo.text kind →
        RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=false)
      (missing : ¬RouteSpec.relayPath (RuntimeRequestSpans.path input head)) : Done c ram s input head amount rawUsed served close hs bs := by
    have same : reply s input head amount rawUsed=⟨s,RouteRefusalSpec.status (RuntimeRequestSpans.path input head),[],[]⟩ :=
      RouteRefusalSpec.reply s _ _ _ _ _ denied missing
    exact finishEmpty _ same (fun len => RuntimeRouteRefusal.contract h pc result denied missing leading metadata hs len)
  have literalRefused (kind : RouteLiteralInfo.Kind) (path : RuntimeRequestSpans.path input head=RouteLiteralInfo.text kind)
      (wrong : RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=false) :
      Done c ram s input head amount rawUsed served close hs bs := by
    apply refused
    · intro other same
      by_cases equal : other=kind
      · subst other;exact wrong
      · exact False.elim (RouteCaseSpec.different kind other (Ne.symm equal) (path.symm.trans same))
    · intro relay;exact RouteCaseSpec.relay_disjoint relay kind path
  have literalWrite (kind : RouteLiteralInfo.Kind) (write : kind≠.state) (path : RuntimeRequestSpans.path input head=RouteLiteralInfo.text kind)
      (allowed : RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=true) :
      Done c ram s input head amount rawUsed served close hs bs := by
    have selected : RouteSpec.select (RuntimeRequestSpans.path input head)=some (RouteLiteralInfo.route kind) := by rw [path];exact RouteCaseSpec.literal kind
    have same : reply s input head amount rawUsed=RuntimeLiteralWriteTransaction.reply kind s input head amount rawUsed := by
      unfold reply RouteSpec.reply RuntimeLiteralWriteTransaction.reply
      rw [selected]
      dsimp only
      rw [allowed]
      cases kind with
      | state => exact False.elim (write rfl)
      | setpoint | temp | mode => simp only [ite_true,RouteLiteralInfo.route,ApiRequestSpec.Route.capture];rw [path]
    have nonHead : isHead input head=false := by
      unfold isHead
      apply decide_eq_false
      intro headEq
      have rejected : RouteSpec.allows (RouteLiteralInfo.route kind) .head=false := by
        cases kind with
        | state => exact False.elim (write rfl)
        | setpoint | temp | mode => rfl
      rw [headEq,rejected] at allowed;cases allowed
    have body : ResponseHeadSpec.body (RuntimeLiteralWriteTransaction.reply kind s input head amount rawUsed).status false
        (RuntimeLiteralWriteTransaction.reply kind s input head amount rawUsed).payload=(RuntimeLiteralWriteTransaction.reply kind s input head amount rawUsed).payload :=
      RouteCaseSpec.write_body s _ _ _ _ _
    obtain ⟨n,d,after,trace,ready⟩ := RuntimeLiteralWriteTransaction.contract kind write h pc result path allowed leading metadata hs bs
      (by simpa only [same] using hhs) (by simpa only [same,nonHead,body] using hbs)
    exact ⟨n,d,after,by simpa only [same,nonHead,body] using trace,by simpa only [same] using ready⟩
  cases selected : RouteSpec.select (RuntimeRequestSpans.path input head) with
  | none =>
    have missing := RouteCaseSpec.missing selected
    exact refused (fun kind same => False.elim (missing.1 kind same)) missing.2
  | some route =>
    have path := RouteCaseSpec.selected _ _ selected
    cases route with
    | state =>
      change RuntimeRequestSpans.path input head=WireSpec.ascii "/state" at path
      have matched : c.get 10=1#32 := by simpa only [path,ite_true] using result
      cases methodEq : MainMethodSpec.decode (MainMethodBytes.token input head.method.2) with
      | get =>
        have same : reply s input head amount rawUsed=⟨s,200,WireSpec.ascii "application/json",ReplyJson.snapshot s⟩ := by
          simp only [reply,RouteSpec.reply,selected,methodEq,RouteSpec.allows,ite_true]
        have nonHead : isHead input head=false := by unfold isHead;rw [methodEq];decide
        obtain ⟨n,d,after,trace,ready⟩ := RuntimeReadTransaction.contract h pc matched captures metadata path methodEq hs bs
          (by simpa only [same] using hhs) (by simpa only [same,nonHead,show ResponseHeadSpec.body 200 false (ReplyJson.snapshot s)=ReplyJson.snapshot s by rfl] using hbs)
        exact ⟨n,d,after,by simpa only [same,nonHead,show ResponseHeadSpec.body 200 false (ReplyJson.snapshot s)=ReplyJson.snapshot s by rfl] using trace,by simpa only [same] using ready⟩
      | head =>
        have same : reply s input head amount rawUsed=⟨s,200,WireSpec.ascii "application/json",ReplyJson.snapshot s⟩ := by
          simp only [reply,RouteSpec.reply,selected,methodEq,RouteSpec.allows,ite_true]
        have yesHead : isHead input head=true := by unfold isHead;rw [methodEq];decide
        obtain ⟨n,d,after,trace,ready⟩ := RuntimeHeadTransaction.contract h pc matched captures metadata path methodEq hs bs
          (by simpa only [same] using hhs) (by simpa only [same,yesHead,ResponseHeadSpec.head_empty,List.length_nil] using hbs)
        exact ⟨n,d,after,by simpa only [same,yesHead,ResponseHeadSpec.head_empty] using trace,by simpa only [same] using ready⟩
      | post | put | patch | delete | other =>
        exact literalRefused .state path (by rw [methodEq];rfl)
    | setpoint =>
      change RuntimeRequestSpans.path input head=WireSpec.ascii "/setpoint" at path
      by_cases allowed : RouteSpec.allows .setpoint (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=true
      · exact literalWrite .setpoint (by decide) path allowed
      · exact literalRefused .setpoint path (Bool.eq_false_iff.mpr allowed)
    | temp =>
      change RuntimeRequestSpans.path input head=WireSpec.ascii "/temp" at path
      by_cases allowed : RouteSpec.allows .temp (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=true
      · exact literalWrite .temp (by decide) path allowed
      · exact literalRefused .temp path (Bool.eq_false_iff.mpr allowed)
    | mode =>
      change RuntimeRequestSpans.path input head=WireSpec.ascii "/mode" at path
      by_cases allowed : RouteSpec.allows .mode (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=true
      · exact literalWrite .mode (by decide) path allowed
      · exact literalRefused .mode path (Bool.eq_false_iff.mpr allowed)
    | relay param =>
      change RouteSpec.relayPath (RuntimeRequestSpans.path input head) ∧ param=(RuntimeRequestSpans.path input head).drop 7 at path
      by_cases put : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.put
      · have same : reply s input head amount rawUsed=RuntimeRelayWriteTransaction.reply s input head amount rawUsed := by
          simp only [reply,RouteSpec.reply,selected,put,RouteSpec.allows,ite_true,ApiRequestSpec.Route.capture,path.2,RuntimeRelayWriteTransaction.reply]
        have nonHead : isHead input head=false := by unfold isHead;rw [put];decide
        have body : ResponseHeadSpec.body (RuntimeRelayWriteTransaction.reply s input head amount rawUsed).status false
            (RuntimeRelayWriteTransaction.reply s input head amount rawUsed).payload=(RuntimeRelayWriteTransaction.reply s input head amount rawUsed).payload :=
          RouteCaseSpec.write_body s _ _ _ _ _
        obtain ⟨n,d,after,trace,ready⟩ := RuntimeRelayWriteTransaction.contract h pc result path.1 put leading metadata hs bs
          (by simpa only [same] using hhs) (by simpa only [same,nonHead,body] using hbs)
        exact ⟨n,d,after,by simpa only [same,nonHead,body] using trace,by simpa only [same] using ready⟩
      · have wrong : RouteSpec.allows (.relay param) (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=false := by
          cases token : MainMethodSpec.decode (MainMethodBytes.token input head.method.2) with
          | put => exact False.elim (put token)
          | get | head | post | patch | delete | other => rfl
        have same : reply s input head amount rawUsed=⟨s,405,[],[]⟩ := RouteSpec.wrong_method selected wrong s _ _ _
        exact finishEmpty 405 same (fun len => RuntimeRouteRelayWrongMethod.contract h pc result path.1 put leading metadata hs len)
end E5R.Thermostat.RuntimeRouteTransaction
