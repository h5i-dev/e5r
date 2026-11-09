import Projects.thermostat.ReadRoutePrepare
import Projects.thermostat.WriteRoutePrepare
import Projects.thermostat.RouteRefusalPrepare
import Projects.thermostat.RuntimeRouteCorrespondence
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeRoutePrepare
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev reply := RuntimeRouteTransaction.reply
abbrev isHead := RuntimeRouteTransaction.isHead

def Done (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot) (input : List (BitVec 8)) (head : Head)
    (amount rawUsed served : Nat) (close : Bool) (used : Word) : Prop :=
  let response := reply s input head amount rawUsed
  ∃ n d after json headOnly,Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
    NormalSendPhase.Ready d after response served used json close headOnly ∧
    ResponseHeadSpec.body response.status headOnly response.payload=ResponseHeadSpec.body response.status (isHead input head) response.payload

theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32)
    (result : c.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32)) (captures : c.get 11=0#32)
    (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys) (metadata : LoopTransactionMemory.At ram used)
    : Done c ram s input head amount rawUsed served close used := by
  have finishEmpty (status : Nat) (same : reply s input head amount rawUsed=⟨s,status,[],[]⟩)
      (execute : ∃ n d after headOnly,Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
        NormalSendPhase.Ready d after ⟨s,status,[],[]⟩ served used false close headOnly) :
      Done c ram s input head amount rawUsed served close used := by
    obtain ⟨n,d,after,headOnly,quiet,ready⟩ := execute
    exact ⟨n,d,after,false,headOnly,quiet,by simpa only [same] using ready,by simp only [same,ResponseHeadSpec.body,ite_self]⟩
  have refused
      (denied : ∀ kind : RouteLiteralInfo.Kind,RuntimeRequestSpans.path input head=RouteLiteralInfo.text kind →
        RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=false)
      (missing : ¬RouteSpec.relayPath (RuntimeRequestSpans.path input head)) : Done c ram s input head amount rawUsed served close used := by
    have same : reply s input head amount rawUsed=⟨s,RouteRefusalSpec.status (RuntimeRequestSpans.path input head),[],[]⟩ :=
      RouteRefusalSpec.reply s _ _ _ _ _ denied missing
    exact finishEmpty _ same ( RouteRefusalPrepare.route_miss h pc result denied missing leading metadata)
  have literalRefused (kind : RouteLiteralInfo.Kind) (path : RuntimeRequestSpans.path input head=RouteLiteralInfo.text kind)
      (wrong : RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=false) :
      Done c ram s input head amount rawUsed served close used := by
    apply refused
    · intro other same
      by_cases equal : other=kind
      · subst other;exact wrong
      · exact False.elim (RouteCaseSpec.different kind other (Ne.symm equal) (path.symm.trans same))
    · intro relay;exact RouteCaseSpec.relay_disjoint relay kind path
  have literalWrite (kind : RouteLiteralInfo.Kind) (write : kind≠.state) (path : RuntimeRequestSpans.path input head=RouteLiteralInfo.text kind)
      (allowed : RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=true) :
      Done c ram s input head amount rawUsed served close used := by
    have selected : RouteSpec.select (RuntimeRequestSpans.path input head)=some (RouteLiteralInfo.route kind) := by rw [path];exact RouteCaseSpec.literal kind
    have same : reply s input head amount rawUsed=RuntimeLiteralWriteTransaction.reply kind s input head amount rawUsed := by
      unfold reply RuntimeRouteTransaction.reply RouteSpec.reply RuntimeLiteralWriteTransaction.reply
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
    obtain ⟨n,d,after,json,quiet,ready⟩ := WriteRoutePrepare.literal kind write h pc result path allowed leading metadata
    exact ⟨n,d,after,json,false,quiet,by simpa only [same] using ready,by rw [nonHead]⟩
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
          simp only [reply,RuntimeRouteTransaction.reply,RouteSpec.reply,selected,methodEq,RouteSpec.allows,ite_true]
        have nonHead : isHead input head=false := by unfold isHead RuntimeRouteTransaction.isHead;rw [methodEq];decide
        obtain ⟨n,d,after,quiet,ready⟩ := ReadRoutePrepare.get h pc matched captures metadata path methodEq
        exact ⟨n,d,after,true,false,quiet,by simpa only [same,ReadHandlerPrepare.reply] using ready,by rw [nonHead]⟩
      | head =>
        have same : reply s input head amount rawUsed=⟨s,200,WireSpec.ascii "application/json",ReplyJson.snapshot s⟩ := by
          simp only [reply,RuntimeRouteTransaction.reply,RouteSpec.reply,selected,methodEq,RouteSpec.allows,ite_true]
        have yesHead : isHead input head=true := by unfold isHead RuntimeRouteTransaction.isHead;rw [methodEq];decide
        obtain ⟨n,d,after,quiet,ready⟩ := ReadRoutePrepare.head h pc matched captures metadata path methodEq
        exact ⟨n,d,after,true,true,quiet,by simpa only [same,ReadHandlerPrepare.reply] using ready,by rw [yesHead]⟩
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
          simp only [reply,RuntimeRouteTransaction.reply,RouteSpec.reply,selected,put,RouteSpec.allows,ite_true,ApiRequestSpec.Route.capture,path.2,RuntimeRelayWriteTransaction.reply]
        have nonHead : isHead input head=false := by unfold isHead RuntimeRouteTransaction.isHead;rw [put];decide
        obtain ⟨n,d,after,json,quiet,ready⟩ := WriteRoutePrepare.relay h pc result path.1 put leading metadata
        exact ⟨n,d,after,json,false,quiet,by simpa only [same] using ready,by rw [nonHead]⟩
      · have wrong : RouteSpec.allows (.relay param) (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=false := by
          cases token : MainMethodSpec.decode (MainMethodBytes.token input head.method.2) with
          | put => exact False.elim (put token)
          | get | head | post | patch | delete | other => rfl
        have same : reply s input head amount rawUsed=⟨s,405,[],[]⟩ := RouteSpec.wrong_method selected wrong s _ _ _
        exact finishEmpty 405 same (RouteRefusalPrepare.route_wrong_method h pc result path.1 put leading metadata)
end E5R.Thermostat.RuntimeRoutePrepare
