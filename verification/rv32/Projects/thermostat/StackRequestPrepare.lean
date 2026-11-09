import Projects.thermostat.StreamRequestPrepare
import Projects.thermostat.StackPhaseEnvelope
import Projects.thermostat.StackRuntimeRoutePrepare
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.StackRequestPrepare
open E5R E5R.Thermostat HttpRequestSpec ProtocolStreamSpec RequestPrepare
abbrev B := StackBoard.board
theorem contract {c ram g} (h : RequestPhase.At c ram g) :
    StackPhaseEnvelope.Envelope (fun m ghost => NormalSendPhase.Entry m.core m.ram ghost) ⟨c,ram⟩ g := by
  obtain ⟨input,original,body,s,head,amount,rawUsed,served,lowValue,close,live,header,payload,parsed,pc,result,captures,metadata,ghost⟩ := h
  have path := RuntimeRouteCorrespondence.path live header
  have originalSlash := RouteReceivedPath.accepted_path original 1024 1024 head parsed
  have leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys := by rw [path];exact originalSlash
  obtain ⟨n,d,after,json,headOnly,quiet,ready,bodyEq⟩ := StackRuntimeRoutePrepare.contract live pc result captures leading metadata
  let response := RuntimeRouteTransaction.reply s input head amount rawUsed
  have responseEq : response=RouteSpec.reply s (MainMethodSpec.decode (MainMethodBytes.token original head.method.2))
      (RuntimeRequestSpans.path original head) original body (RuntimeRequestInputs.entries head) := RuntimeRouteCorrespondence.reply live header payload
  have closeEq := RuntimeRouteCorrespondence.close live header
  have headEq := RuntimeRouteCorrespondence.isHead live header
  let pending : ProtocolStreamSpec.Pending := ⟨response,close,(if close then 0 else served+1),
    ResponseHeadSpec.bytes response.status response.mime response.payload.length close++
      ResponseHeadSpec.body response.status (RuntimeRouteTransaction.isHead original head) response.payload⟩
  have phase : g.phase=.reply pending := by
    rw [ghost]
    unfold ProtocolStreamSpec.dispatch ProtocolStreamSpec.enqueue
    dsimp only
    have pureResponse : response=RouteSpec.reply s (MainMethodSpec.decode (MainMethodBytes.token original head.method.2))
        (MainRequestSpans.path original head) original body (MainRequestInputs.entries head) := responseEq
    have pureClose : close=MainCloseSpec.mustClose head.minor (served+1) original (MainRequestInputs.entries head) := closeEq
    rw [←pureResponse,←pureClose]
    rfl
  have family : NormalSendPhase.Pending response (served+1) close g := ⟨pending,phase,rfl,rfl,rfl⟩
  have queue : pending.remaining=SendPhase.header (NormalSendPhase.call ready)++SendPhase.body (NormalSendPhase.call ready) := by
    change ResponseHeadSpec.bytes response.status response.mime response.payload.length close++
        ResponseHeadSpec.body response.status (RuntimeRouteTransaction.isHead original head) response.payload=
      ResponseHeadSpec.bytes response.status response.mime response.payload.length close++ResponseHeadSpec.body response.status headOnly response.payload
    rw [←headEq]
    exact congrArg (fun bytes => ResponseHeadSpec.bytes response.status response.mime response.payload.length close++bytes) bodyEq.symm
  exact ⟨live.stable.masked,n,⟨d,after⟩,quiet,response,served+1,BitVec.ofNat 32 rawUsed,json,close,headOnly,ready,family,pending,phase,queue⟩
end E5R.Thermostat.StackRequestPrepare
