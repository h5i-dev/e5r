import Projects.thermostat.MainLengthState
namespace E5R.Thermostat.MainLengthLoopStep
open E5R E5R.Thermostat MainLengthState

/-- One real fixed-length body receive and count update, followed by a new
    receive descriptor only if further bytes are still required. -/
theorem contract {c ram input s head amount} (h : Ready c ram input s head amount)
    (pending : List Word) (ready datum : Word)
    (notReady : ∀ status∈pending, UartPoll.byte status &&& 1#32=0#32)
    (isReady : UartPoll.byte ready &&& 1#32≠0#32) :
    let next := input++[(UartPoll.byte datum).setWidth 8]
    ∃ n d after, n≤25+4*pending.length ∧ Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainLengthWait.reads pending ready datum) [] ∧
      Boundary d after next s head amount ∧ d.sameCsr c := by
  let next := input++[(UartPoll.byte datum).setWidth 8]
  change ∃ n d after, n≤25+4*pending.length ∧ Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainLengthWait.reads pending ready datum) [] ∧
    Boundary d after next s head amount ∧ d.sameCsr c
  have totalBound := total_bound h.state
  have room : input.length<2048 := Nat.lt_of_lt_of_le h.short totalBound
  obtain ⟨a,mid,receive,apc,a25,a10,layoutA,bytesA,appA,ar,ac,frame⟩ := MainLengthAppend.contract c ram input (head.len+amount) pending ready datum h.pc
    h.state.stable.fp h.state.stable.uart h.state.stable.one h.dst h.state.stable.layout room h.state.stable.bytes totalBound h.state.total h.state.stable.stack notReady isReady
  have stableA : MainHeaderLoopTwo.Stable a mid next s := by
    refine ⟨(ar 2 (by decide) (by decide) (by decide)).trans h.state.stable.sp,
      (ar 8 (by decide) (by decide) (by decide)).trans h.state.stable.fp,
      (ar 19 (by decide) (by decide) (by decide)).trans h.state.stable.uart,
      (ar 22 (by decide) (by decide) (by decide)).trans h.state.stable.one,
      layoutA,bytesA,appA s h.state.stable.app,h.state.stable.invariant,h.state.stable.stack,?_⟩
    exact (congrArg Prod.fst ac).trans h.state.stable.masked
  have stateA : At a mid next s head amount := received h.state stableA frame room ar
  have length : next.length=input.length+1 := by simp only [next,List.length_append,List.length_cons,List.length_nil,Nat.zero_add]
  by_cases more : next.length<head.len+amount
  · have branch : decide (input.length+1<head.len+amount)=true := decide_eq_true (by rw [←length];exact more)
    have pc : a.pc=0x80000c3a#32 := by simpa only [branch,ite_true] using apc
    obtain ⟨d,finish,dpc,d12,layoutD,future,rxFrame,appD,dr,dc⟩ := MainLengthReadSetup.contract B a mid next.length pc stableA.fp a10 stableA.layout (by omega) stableA.stack
    have stableD : MainHeaderLoopTwo.Stable d (MainLengthReadSetup.memory mid next.length) next s := by
      refine ⟨(dr 2 (by decide)).trans stableA.sp,(dr 8 (by decide)).trans stableA.fp,
        (dr 19 (by decide)).trans stableA.uart,(dr 22 (by decide)).trans stableA.one,layoutD,?_,appD s stableA.app,stableA.invariant,stableA.stack,?_⟩
      · intro i;exact (rxFrame ⟨i.val,by have := i.isLt;have := stableA.layout.bound;omega⟩).trans (stableA.bytes i)
      · exact (congrArg Prod.fst dc).trans stableA.masked
    have stateD := prepared stateA stableD future dr
    refine ⟨(14+4*pending.length)+11,d,MainLengthReadSetup.memory mid next.length,by omega,?_,?_,dc.trans ac⟩
    · simpa only [List.append_nil] using receive.trans finish.observed
    · simpa only [Boundary,more,ite_true] using (show Ready d (MainLengthReadSetup.memory mid next.length) next s head amount from ⟨dpc,stateD,d12,more⟩)
  · have branch : decide (input.length+1<head.len+amount)=false := decide_eq_false (by rw [←length];exact more)
    have pc : a.pc=0x80000c98#32 := by simpa only [branch,Bool.false_eq_true,ite_false] using apc
    exact ⟨14+4*pending.length,a,mid,by omega,receive,(if_neg more).mpr ⟨pc,stateA⟩,ac⟩
end E5R.Thermostat.MainLengthLoopStep
