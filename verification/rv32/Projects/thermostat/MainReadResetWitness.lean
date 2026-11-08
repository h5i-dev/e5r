import Projects.thermostat.MainReadReset
import Projects.thermostat.MainCloseRequestWitness
import Projects.thermostat.ReadSendWitness
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.MainReadResetWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
open MainCloseRequestWitness

theorem route_facts : ∀ kind : Fin 4,
    MainRequestSpans.path (header kind) (expected kind)=WireSpec.ascii "/state" ∧
    MainMethodSpec.decode (MainMethodBytes.token (header kind) (expected kind).method.2)=.get := by decide +kernel

/-- Four satisfying complete reset/UART requests, including a query and real
    Connection scans: absent, mixed-case close, near misses, later duplicate. -/
theorem execution (kind : Fin 4) : ∃ n d after reads,
    Observed.Steps UartPlatform.board img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩ reads
      (UartTxLoop.events (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot Spec.initial).length (closes kind))++
        UartTxLoop.events (ReplyJson.snapshot Spec.initial)) ∧
    Observed.input reads=header kind ∧
    d.pc=(if closes kind then 0x80000978#32 else 0x800017be#32) ∧ d.mie_=false ∧
    AppState.At after Spec.initial ∧ Engine.InvariantAt after 0x80ffebbc#32 := by
  have fs := facts kind
  have accepted : (consume (wire kind) (header kind).length []).result=.done (expected kind) := by rw [consumed kind]
  have missing : (expected kind).len+0-(header kind).length=0 := by rw [fs.2.1];omega
  have path : MainRequestSpans.path ((consume (wire kind) (header kind).length []).input++arrivals (wire kind) (consume (wire kind) (header kind).length []).input.length
      ((expected kind).len+0-(consume (wire kind) (header kind).length []).input.length)) (expected kind)=WireSpec.ascii "/state" := by
    rw [consumed kind]
    dsimp only
    rw [missing]
    simpa only [arrivals,List.range_zero,List.map_nil,List.append_nil] using (route_facts kind).1
  have get : MainMethodSpec.decode (MainMethodBytes.token ((consume (wire kind) (header kind).length []).input++arrivals (wire kind) (consume (wire kind) (header kind).length []).input.length
      ((expected kind).len+0-(consume (wire kind) (header kind).length []).input.length)) (expected kind).method.2)=.get := by
    rw [consumed kind]
    dsimp only
    rw [missing]
    simpa only [arrivals,List.range_zero,List.map_nil,List.append_nil] using (route_facts kind).2
  obtain ⟨n,d,after,close,limit,trace,bytes,selected,pc,sp,fp,masked,app,inv⟩ := MainReadReset.contract MainInitWitness.core MainInitWitness.ram (wire kind) (plan kind) (header kind).length (expected kind) 0 (plan kind)
    rfl (Or.inr rfl) rfl Blocking.stack_available (by omega) (valid kind _ _) accepted fs.2.2.1 (valid kind _ _) path get
    ReadSendWitness.headerSlots (ReadSendWitness.bodySlots false) (fun _ => List.length_replicate) List.length_replicate
  rw [consumed kind] at trace bytes selected
  dsimp only at trace bytes selected
  rw [missing] at trace bytes selected
  simp only [arrivals,List.range_zero,List.map_nil,List.append_nil] at bytes selected
  have rawEq : MainRequestSpans.raw (header kind) (expected kind) 0=header kind := by simp only [MainRequestSpans.raw,Nat.add_zero,fs.2.1,List.take_length]
  have closeEq : close=closes kind := selected.trans (by rw [rawEq];exact pure_close kind)
  rw [closeEq] at trace pc bytes
  exact ⟨n,d,after,_,trace,bytes,pc,masked,app,inv⟩
end E5R.Thermostat.MainReadResetWitness
