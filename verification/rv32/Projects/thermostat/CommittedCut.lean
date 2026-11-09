import Projects.thermostat.CutBounds
set_option autoImplicit false
namespace E5R.Thermostat.CommittedCut
open E5R E5R.Thermostat ProtocolStreamSpec

/-- The snapshot already persisted at a UART cut. During a pending response
    the pure stream retains the previous logical snapshot until completion. -/
def snapshot (g : State) : Spec.Snapshot := match g.phase with
  | .reply p => p.response.state
  | _ => g.snapshot

theorem uart_frame {original a before pre obj io src bs ret suffix c ram g}
    (prepared : SendUartReactive.Prepared original a before pre obj io src bs ret)
    (live : UartWritePhase.Active a pre (obj+48#32) io src bs suffix c ram g) :
    ∀ x,(∀ i : Fin 89,x≠obj+BitVec.ofNat 32 i.val) → ram x=before x := by
  intro x apart
  have frame : ∀ x,(∀ i : Fin 41,x≠(obj+48#32)+BitVec.ofNat 32 i.val) → ram x=pre x := by
    intro x separated
    rw [live.2.1]
    exact UartWritePrepare.frame _ _ _ _ _ x separated
  exact (SendUartFrame.outside frame x apart).trans (prepared.outside x apart)

theorem send_frame {call : SendPhase.Call} {m g} (h : SendPhase.Active call m g) :
    ∀ x,(∀ i : Fin 144,x≠call.frame+BitVec.ofNat 32 i.val) →
      (∀ i : Fin 89,x≠call.obj+BitVec.ofNat 32 i.val) →
      (∀ i : Fin 192,x≠call.tx+BitVec.ofNat 32 i.val) → m.ram x=call.before x := by
  intro x hs ho ht
  cases h with
  | head stage anchor prepared live =>
    exact (uart_frame prepared live x ho).trans (stage.post.memoryFrame x hs ho ht)
  | body stage headCore headRam anchor headDone prepared live =>
    exact (uart_frame prepared live x ho).trans ((headDone.outside x ho).trans (stage.post.memoryFrame x hs ho ht))

theorem normal {m g} (h : NormalSendPhase.Active m g) :
    AppState.At m.ram (snapshot g) ∧ Spec.Inv (snapshot g) := by
  obtain ⟨original,before,response,served,used,json,close,headOnly,ready,live,pending⟩ := h
  obtain ⟨p,phase,reply,cl,count⟩ := pending
  have state : snapshot g=response.state := by simp only [snapshot,phase,reply]
  rw [state]
  refine ⟨AppState.preserve before m.ram response.state ready.app ?_,ready.invariant⟩
  have frame := send_frame live
  dsimp only [NormalSendPhase.call] at frame
  intro i
  apply frame
  · exact WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i
  · exact WordRegions.before _ _ _ _ (by decide) (by decide) i
  · exact WordRegions.before _ _ _ _ (by decide) (by decide) i

theorem refusal {m g} (h : RefusalSendPhase.Active m g) :
    AppState.At m.ram (snapshot g) ∧ Spec.Inv (snapshot g) := by
  obtain ⟨original,before,s,served,status,ready,live,pending⟩ := h
  obtain ⟨old,count,p,phase,reply,cl,next⟩ := pending
  have state : snapshot g=s := by simp only [snapshot,phase,reply]
  rw [state]
  refine ⟨AppState.preserve before m.ram s ready.app ?_,ready.invariant⟩
  have frame := send_frame live
  dsimp only [RefusalSendPhase.call] at frame
  intro i
  apply frame
  · exact WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i
  · exact WordRegions.before _ _ _ _ (by decide) (by decide) i
  · exact WordRegions.before _ _ _ _ (by decide) (by decide) i

theorem receive_snapshot {m g} (h : ReceivePhases.Active m g) : snapshot g=g.snapshot := by
  rcases h with header|length|chunk
  · cases header with
    | polling eq _ _ _ | rbr eq _ _ _ => subst g;rfl
  · cases length with
    | polling eq _ _ _ _ | rbr eq _ _ _ _ => subst g;rfl
  · cases chunk with
    | polling eq _ _ _ | rbr eq _ _ _ => subst g;rfl

/-- All actual UART cuts have a committed RAM snapshot, free borrow and
    invariant. This deliberately excludes quiet handler store interiors. -/
theorem active {m g} (h : FirmwareStream.At m g) :
    AppState.At m.ram (snapshot g) ∧ Spec.Inv (snapshot g) ∧
      ramRead m.ram 0x80ffebbc#32 .w=0#32 := by
  have state : AppState.At m.ram (snapshot g) ∧ Spec.Inv (snapshot g) := by
    rcases h with receive|send|reject
    · rw [receive_snapshot receive]
      exact ⟨(CutBounds.receive_commit receive).1,(CutBounds.receive_commit receive).2.1⟩
    · exact normal send
    · exact refusal reject
  exact ⟨state.1,state.2,state.1.available⟩
end E5R.Thermostat.CommittedCut
