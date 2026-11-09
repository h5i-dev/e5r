import Projects.thermostat.StackBoard
import Projects.thermostat.MainLengthState
import Projects.thermostat.MainServeMemoryFrames
namespace E5R.Thermostat.StackLengthPrepareRegs
open E5R E5R.Thermostat MainLengthState
abbrev B := StackBoard.board

/-- Actual checked capacity and receive-slice setup, with the body invariant
    transported across its stores rather than assumed at the next poll. -/
theorem contract {c ram input s head amount} (h : At c ram input s head amount)
    (hp : c.pc=0x80000c3a#32) (h10 : c.get 10=BitVec.ofNat 32 input.length)
    (short : input.length<head.len+amount) :
    ∃ d, Quiet.Steps B img 11 ⟨c,ram⟩ ⟨d,MainLengthReadSetup.memory ram input.length⟩ ∧
      Ready d (MainLengthReadSetup.memory ram input.length) input s head amount ∧ d.sameCsr c ∧ HeadRegisterFrame.At c d MainLengthReadSetup.writes ∧ MainServeLayout.Frame ram (MainLengthReadSetup.memory ram input.length) := by
  have totalBound := total_bound h
  obtain ⟨d,finish,dpc,d12,layoutD,future,rxFrame,appD,dr,dc⟩ := MainLengthReadSetup.contract B c ram input.length hp h.stable.fp h10 h.stable.layout (by omega) StackBoard.available
  have stableD : MainHeaderLoopTwo.Stable d (MainLengthReadSetup.memory ram input.length) input s := by
    refine ⟨(dr 2 (by decide)).trans h.stable.sp,(dr 8 (by decide)).trans h.stable.fp,
      (dr 19 (by decide)).trans h.stable.uart,(dr 22 (by decide)).trans h.stable.one,layoutD,?_,appD s h.stable.app,h.stable.invariant,h.stable.stack,?_⟩
    · intro i;exact (rxFrame ⟨i.val,by have := i.isLt;have := h.stable.layout.bound;omega⟩).trans (h.stable.bytes i)
    · exact (congrArg Prod.fst dc).trans h.stable.masked
  exact ⟨d,finish,⟨dpc,prepared h stableD future dr,d12,short⟩,dc,dr,MainServeMemoryFrames.whole future (by decide)⟩
end E5R.Thermostat.StackLengthPrepareRegs
