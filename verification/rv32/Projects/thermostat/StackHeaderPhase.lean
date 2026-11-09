import Projects.thermostat.StackHeaderReactive
import Projects.thermostat.StackEnvelope
import Projects.thermostat.HeaderPhase
set_option autoImplicit false
namespace E5R.Thermostat.StackHeaderPhase
open E5R E5R.Thermostat HttpRequestSpec ProtocolStreamSpec HeaderPhase
abbrev B := StackBoard.board
abbrev classify := HeaderPhase.classify
abbrev Envelope (I : Machine → State → Prop) (m : Machine) (g : State) :=
  StackEnvelope.Envelope (fun cut => I cut g) m

theorem next {c ram g} (h : At c ram g) (o : Oracle) :
    ∃ d reads next,Observed.stepInstr B img ⟨c,ram⟩ o=⟨.ok d ram [],reads⟩ ∧
      ProtocolStreamTrace.Trace g (Observed.input reads) [] next ∧ Envelope Cut ⟨d,ram⟩ next := by
  cases h with
  | @polling s served input eq pref live caller =>
    subst g
    obtain ⟨d,reads,step,post,only,bank⟩ := StackHeaderReactive.polling_next live o
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
    obtain ⟨step,post,bank⟩ := StackHeaderReactive.rbr_next live o
    have continued := StackHeaderReactive.after_rbr post
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
        exact Or.inl (.polling (by simp only [classify,HeaderPhase.classify,waiting]) fullPrefix (HeaderReactive.enter ready) finalCaller)
      · exact Or.inr ⟨inputNext,s,served,boundary,waiting,earlier,finalCaller,rfl⟩

theorem safe {c ram g} (h : At c ram g) : ¬Escapes B img ⟨c,ram⟩ := by
  cases h with
  | polling _ _ live _ => exact StackHeaderWait.safe ⟨live.waiting,live.stable.uart,live.stable.masked⟩
  | rbr _ _ live _ => exact StackHeaderWait.exit_safe ⟨live.pc,live.stable.uart,live.stable.masked⟩

end E5R.Thermostat.StackHeaderPhase
