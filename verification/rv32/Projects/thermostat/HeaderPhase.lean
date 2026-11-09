import Projects.thermostat.HeaderReactive
import Projects.thermostat.ReactiveEnvelope
import Projects.thermostat.HeadConsumedExtent
import Projects.thermostat.LoopReady
import Projects.thermostat.MainRouterBankHeaderFrames
set_option autoImplicit false
namespace E5R.Thermostat.HeaderPhase
open E5R E5R.Thermostat HttpRequestSpec ProtocolStreamSpec
abbrev B := UartPlatform.board

/-- Every earlier prefix is still an incomplete head. It is established from
    reset and actual byte reception, not assumed when a complete head appears. -/
def Prefix (input : List (BitVec 8)) : Prop :=
  ∀ k,k≤input.length → HttpRequestBytes.parse (input.take k) 1024 1024=.incomplete

def classify (s : Spec.Snapshot) (served : Nat) (input : List (BitVec 8)) : State :=
  let m := State.mk s served (.head input)
  match HttpRequestBytes.parse input 1024 1024 with
  | .incomplete => m
  | .reject status => ProtocolStreamSpec.reject m status
  | .done head =>
    match head.framing with
    | .empty => ProtocolStreamSpec.dispatch m input [] head
    | .length amount => if amount=0 then ProtocolStreamSpec.dispatch m input [] head
        else {m with phase := .length input head amount []}
    | .chunked => {m with phase := .chunked input head head.len cStart []}

theorem receive_classify (s : Spec.Snapshot) (served : Nat) (input : List (BitVec 8)) (byte : BitVec 8)
    (room : input.length<2048) :
    ProtocolStreamSpec.receive ⟨s,served,.head input⟩ byte=some (classify s served (input++[byte])) := by
  simp only [ProtocolStreamSpec.receive,room,ite_true,classify]
  cases found : HttpRequestBytes.parse (input++[byte]) 1024 1024 with
  | incomplete => rfl
  | reject status => rfl
  | done head =>
    dsimp only
    cases framing : head.framing with
    | empty => rfl
    | length amount => by_cases zero : amount=0 <;> simp only [zero,ite_true,ite_false] <;> rfl
    | chunked => rfl

structure Caller (c : Core) (ram : Word → BitVec 8) (served : Nat) : Prop where
  bank : MainGprBank.At c
  serve : MainServeLayout.At ram served
  room : served<100
  layout : InitRoutes.Layout ram

theorem preserve_caller {c d before after served} (h : Caller c before served)
    (bank : MainGprBank.Frame c d) (serve : MainServeLayout.Frame before after)
    (low : ViewFrame.Region before after 0x80ffeb90#32 132) : Caller d after served := by
  refine ⟨MainGprBank.preserve bank h.bank,MainServeLayout.preserve serve h.serve,h.room,?_⟩
  apply InitRoutes.layout_preserve before after h.layout
  · simpa only [ViewFrame.Region,show 0x80ffeb90#32+72#32=0x80ffebd8#32 by decide +kernel] using HeadRegionFrame.sub low 72 60 (by decide)
  · simpa only [ViewFrame.Region,show 0x80ffeb90#32+16#32=0x80ffeba0#32 by decide +kernel] using HeadRegionFrame.sub low 16 4 (by decide)

inductive At (c : Core) (ram : Word → BitVec 8) (g : State) : Prop where
  | polling {s served input} : g=⟨s,served,.head input⟩ → Prefix input →
      HeaderReactive.Polling c ram input s → Caller c ram served → At c ram g
  | rbr {s served input} : g=⟨s,served,.head input⟩ → Prefix input →
      HeaderReactive.Rbr c ram input s → Caller c ram served → At c ram g

/-- The next module owns accepted/rejected parser continuation. The original
    bytes, first terminal result and all downstream caller layouts are retained. -/
def Terminal (c : Core) (ram : Word → BitVec 8) (g : State) : Prop :=
  ∃ input snapshot served,
    MainHeaderLoopTwo.Boundary c ram input snapshot (HttpRequestBytes.parse input 1024 1024) ∧
    HttpRequestBytes.parse input 1024 1024≠.incomplete ∧
    (∀ k,k<input.length → HttpRequestBytes.parse (input.take k) 1024 1024=.incomplete) ∧
    Caller c ram served ∧ g=classify snapshot served input

def Cut (m : Machine) (g : State) := At m.core m.ram g ∨ Terminal m.core m.ram g

theorem enter {c ram s served} (h : LoopReady.At c ram s served) : At c ram ⟨s,served,.head []⟩ := by
  refine .polling rfl ?_ (HeaderReactive.enter h.receive) ⟨h.bank,h.serve,h.room,h.routes,h.capacity⟩
  intro k bound
  have zero : k=0 := by simpa only [List.length_nil] using Nat.eq_zero_of_le_zero bound
  subst k
  decide +kernel


theorem next {c ram g} (h : At c ram g) (o : Oracle) :
    ∃ d reads next,Observed.stepInstr B img ⟨c,ram⟩ o=⟨.ok d ram [],reads⟩ ∧
      ProtocolStreamTrace.Trace g (Observed.input reads) [] next ∧ ReactiveEnvelope.Envelope Cut ⟨d,ram⟩ next := by
  cases h with
  | @polling s served input eq pref live caller =>
    subst g
    obtain ⟨d,reads,step,post,only,bank⟩ := HeaderReactive.polling_next live o
    have finalCaller := preserve_caller caller bank (MainServeLayout.refl ram) (fun _ => rfl)
    have noInput : Observed.input reads=[] := by
      rcases only with nil|⟨v,single⟩
      · rw [nil];rfl
      · rw [single];rfl
    refine ⟨d,reads,⟨s,served,.head input⟩,step,?_,?_⟩
    · rw [noInput];exact ProtocolStreamTrace.refl _
    · rcases post with waiting|rbr
      · exact ⟨waiting.stable.masked,0,⟨d,ram⟩,.refl _,Or.inl (.polling rfl pref waiting finalCaller)⟩
      · exact ⟨rbr.stable.masked,0,⟨d,ram⟩,.refl _,Or.inl (.rbr rfl pref rbr finalCaller)⟩
  | @rbr s served input eq pref live caller =>
    subst g
    let byte := (UartPoll.byte (o 0)).setWidth 8
    let first := c.wr 10 (UartPoll.byte (o 0)) 0x80000bae#32
    let inputNext := input++[byte]
    obtain ⟨step,post,bank⟩ := HeaderReactive.rbr_next live o
    have continued := HeaderReactive.after_rbr post
    change ∃ n e after,Quiet.Steps B img n ⟨first,ram⟩ ⟨e,after⟩ ∧
      MainHeaderLoopTwo.Boundary e after inputNext s (HttpRequestBytes.parse inputNext 1024 1024) ∧ e.sameCsr first ∧
      MainGprBank.Frame first e ∧ MainServeLayout.Frame ram after ∧ ViewFrame.Region ram after 0x80ffeb90#32 132 at continued
    obtain ⟨n,e,after,quiet,boundary,csr,bankLast,serve,low⟩ := continued
    have firstCaller := preserve_caller caller bank (MainServeLayout.refl ram) (fun _ => rfl)
    have finalCaller := preserve_caller firstCaller bankLast serve low
    have earlier (k : Nat) (bound : k<inputNext.length) : HttpRequestBytes.parse (inputNext.take k) 1024 1024=.incomplete := by
      have oldBound : k≤input.length := by
        have size : inputNext.length=input.length+1 := by simp only [inputNext,List.length_append,List.length_singleton]
        omega
      have same : inputNext.take k=input.take k := by
        simp only [inputNext,List.take_append,Nat.sub_eq_zero_of_le oldBound,List.take_zero,List.append_nil]
      rw [same];exact pref k oldBound
    refine ⟨first,[⟨0x10000000#32,.b,UartPoll.byte (o 0),0⟩],classify s served inputNext,step,?_,live.stable.masked,n,⟨e,after⟩,quiet,?_⟩
    · exact ProtocolStreamTrace.receive (receive_classify s served input byte live.room)
    · by_cases waiting : HttpRequestBytes.parse inputNext 1024 1024=.incomplete
      · have ready : MainHeaderLoopTwo.Ready e after inputNext s := by simpa only [waiting,MainHeaderLoopTwo.Boundary] using boundary
        have fullPrefix : Prefix inputNext := by
          intro k bound
          by_cases strict : k<inputNext.length
          · exact earlier k strict
          · have last : k=inputNext.length := by omega
            rw [last,List.take_length];exact waiting
        exact Or.inl (.polling (by simp only [classify,waiting]) fullPrefix (HeaderReactive.enter ready) finalCaller)
      · exact Or.inr ⟨inputNext,s,served,boundary,waiting,earlier,finalCaller,rfl⟩

theorem safe {c ram g} (h : At c ram g) : ¬Escapes B img ⟨c,ram⟩ := by
  cases h with
  | polling _ _ live _ => exact MainHeaderWaitSafety.safe ⟨live.waiting,live.stable.uart,live.stable.masked⟩
  | rbr _ _ live _ => exact MainHeaderWaitSafety.exit_safe ⟨live.pc,live.stable.uart,live.stable.masked⟩

/-- Reset reaches the real initial header phase. Closing every Terminal case
    remains explicit work; this does not assert Closed Cut. -/
theorem reset (c : Core) (ram : Word → BitVec 8) (pc : c.pc=0x80000000#32)
    (mpp : c.mpp=0 ∨ c.mpp=3) (masked : c.mie_=false)
    (stack : Memory.Block B 0x80ff0000#32 65536) : ReactiveEnvelope.Envelope Cut ⟨c,ram⟩ ProtocolStreamSpec.initial := by
  obtain ⟨d,after,quiet,ready⟩ := LoopReady.reset c ram pc mpp stack
  exact ⟨masked,2550,⟨d,after⟩,quiet,Or.inl (enter ready)⟩


/-- The first complete parse cannot have left a shorter head inside its byte
    buffer. This discharges zero-prefetched-body from actual reactive history. -/
theorem accepted_extent (input : List (BitVec 8)) (head : Head)
    (earlier : ∀ k,k<input.length → HttpRequestBytes.parse (input.take k) 1024 1024=.incomplete)
    (accepted : HttpRequestBytes.parse input 1024 1024=.done head) : head.len=input.length := by
  have truncated := HeadConsumedExtent.bytes_prefix input head accepted
  have bounds := MainHeadAcceptedBounds.bytes input head accepted
  have cap := Nat.min_le_left input.length 1024
  by_cases shorter : head.len<input.length
  · rw [earlier head.len shorter] at truncated
    cases truncated
  · have inside := bounds.length.2
    omega

end E5R.Thermostat.HeaderPhase
