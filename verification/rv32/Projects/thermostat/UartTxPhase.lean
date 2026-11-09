import Projects.thermostat.UartTxReactive
import Projects.thermostat.ProtocolStreamTrace
set_option autoImplicit false
namespace E5R.Thermostat.UartTxPhase
open E5R E5R.Thermostat ProtocolStreamSpec
abbrev B := UartPlatform.board

/-- The actual UART call transmits a prefix of the logical response queue.
    Header-call return need not mean that its body has already been emitted. -/
inductive At (c : Core) (ram : Word → BitVec 8) (g : State) (suffix : List (BitVec 8)) : Prop where
  | loading {src byte rest p} : g.phase=.reply p → p.remaining=(byte::rest)++suffix →
      UartTxReactive.Loading c ram src byte rest → At c ram g suffix
  | polling {src byte rest p} : g.phase=.reply p → p.remaining=(byte::rest)++suffix →
      UartTxReactive.Polling c ram src byte rest → At c ram g suffix
  | before {src byte rest p} : g.phase=.reply p → p.remaining=(byte::rest)++suffix →
      UartTxReactive.BeforeEmit c ram src byte rest → At c ram g suffix
  | emitting {src byte rest p} : g.phase=.reply p → p.remaining=(byte::rest)++suffix →
      UartTxReactive.Emitting c ram src byte rest → At c ram g suffix
  | branch {src bytes p} : g.phase=.reply p → p.remaining=bytes++suffix →
      UartTxReactive.Branch c ram src bytes → At c ram g suffix

def Returned (c : Core) (ram : Word → BitVec 8) (g : State) (suffix : List (BitVec 8)) : Prop :=
  ∃ src p,g.phase=.reply p ∧ p.remaining=suffix ∧ c.pc=0x8000080a#32 ∧
    UartTxReactive.Context c ram src [] ∧ c.get 12=src

theorem masked {c ram g suffix} (h : At c ram g suffix) : c.mie_=false := by
  cases h with
  | loading _ _ live => exact live.context.masked
  | polling _ _ live => exact live.context.masked
  | before _ _ live => exact live.context.masked
  | emitting _ _ live => exact live.context.masked
  | branch _ _ live => exact live.context.masked

/-- Every oracle at every internal UART-loop instruction is safe and refines
    either a silent protocol step or exactly its expected THR byte. No future
    ready poll, complete response or physical FIFO assumption occurs here. -/
theorem next {c ram g suffix} (h : At c ram g suffix) (o : Oracle) :
    ∃ d reads evs next,Observed.stepInstr B img ⟨c,ram⟩ o=⟨.ok d ram evs,reads⟩ ∧
      ProtocolStreamTrace.Trace g (Observed.input reads) (Observed.output evs) next ∧
      (At d ram next suffix ∨ Returned d ram next suffix) ∧
      (∀ r : Reg,r≠12 → r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  cases h with
  | @loading src byte rest p phase queue live =>
    obtain ⟨step,post⟩ := UartTxReactive.load live
    exact ⟨_,[],[],g,step o,ProtocolStreamTrace.refl _,Or.inl (.polling phase queue post),
      (fun r a b e => Core.wr_get_ne _ _ _ _ _ b),rfl⟩
  | @polling src byte rest p phase queue live =>
    obtain ⟨d,reads,step,post,only,regs,csr⟩ := UartTxReactive.polling_next live o
    have noInput : Observed.input reads=[] := by
      rcases only with nil|⟨v,single⟩
      · rw [nil];rfl
      · rw [single];rfl
    refine ⟨d,reads,[],g,step,?_,?_,(fun r a b e => regs r e),csr⟩
    · rw [noInput];exact ProtocolStreamTrace.refl _
    · rcases post with wait|ready
      · exact Or.inl (.polling phase queue wait)
      · exact Or.inl (.before phase queue ready)
  | @before src byte rest p phase queue live =>
    obtain ⟨step,post⟩ := UartTxReactive.increment live
    exact ⟨_,[],[],g,step o,ProtocolStreamTrace.refl _,Or.inl (.emitting phase queue post),
      (fun r a b e => Core.wr_get_ne _ _ _ _ _ a),rfl⟩
  | @emitting src byte rest p phase queue live =>
    obtain ⟨step,post⟩ := UartTxReactive.emit live o
    let next := {g with phase := .reply {p with remaining := rest++suffix}}
    refine ⟨_,[],[⟨0x10000000#32,UartTxByte.word byte⟩],next,step,?_,?_,(fun _ _ _ _ => rfl),rfl⟩
    · rw [UartTxByte.output]
      exact ProtocolStreamTrace.transmit phase queue
    · exact Or.inl (.branch rfl rfl post)
  | @branch src bytes p phase queue live =>
    obtain ⟨d,step,pc,context,pointer,regs,csr⟩ := UartTxReactive.branch live
    refine ⟨d,[],[],g,step o,ProtocolStreamTrace.refl _,?_,(fun r _ _ _ => regs r),csr⟩
    cases bytes with
    | nil => exact Or.inr ⟨src,p,phase,by simpa only [List.nil_append] using queue,by simpa only [ite_true] using pc,context,pointer⟩
    | cons byte rest =>
      exact Or.inl (.loading phase queue ⟨by simpa only [List.cons_ne_nil,ite_false] using pc,context,pointer⟩)

/-- This is unconditional safety of the real UART-loop phases only. Its return
    cutpoint is owned by the actual caller's checked object/tail contract. -/
theorem safe {c ram g suffix} (h : At c ram g suffix) : ¬Escapes B img ⟨c,ram⟩ := by
  rintro (⟨o,f,fault⟩|⟨code,e,enabled,_⟩)
  · obtain ⟨d,reads,evs,next,step,_⟩ := next h o
    have erase := Observed.erase_step B img ⟨c,ram⟩ o
    rw [step] at erase
    rw [←erase] at fault
    cases fault
  · simp [irqEnabled,masked h] at enabled
end E5R.Thermostat.UartTxPhase
