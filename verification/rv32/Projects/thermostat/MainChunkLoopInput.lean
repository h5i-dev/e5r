import Projects.thermostat.MainChunkGuard
import Projects.thermostat.MainChunkLoopInvariant
namespace E5R.Thermostat.MainChunkLoopInput
open E5R E5R.Thermostat HttpRequestSpec

/-- Buffered-input and capacity comparisons derive the next actual call's
    complete precondition. Cursor arithmetic is bounded by the live RX length. -/
theorem contract {B c ram sp start read written filled s}
    (h : MainChunkLoopInvariant.At B c ram sp start read written filled s) (available : read<filled) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      MainChunkInput.Ready B d ram sp (sp+132#32) (sp+3280#32) (BitVec.ofNat 32 read) 1024#32 s ∧
      MainChunkCoreFrame.At c d ∧ d.sameCsr c := by
  have br : read<4294967296 := by have := h.readFilled;have := h.capacity;omega
  have bf : filled<4294967296 := by have := h.capacity;omega
  obtain ⟨d,trace,pc,count,cap,regs,csr⟩ := MainChunkGuard.contract B c ram sp (BitVec.ofNat 32 read)
    (BitVec.ofNat 32 filled) h.framePtr h.cursor h.stack h.align h.layout.filledPtr h.filledWord h.layout.capacity
    (by simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt br,Nat.mod_eq_of_lt bf] using available)
    (by simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bf] using h.capacity) h.pc
  have pre : MainChunkInput.Ready B d ram sp (sp+132#32) (sp+3280#32) (BitVec.ofNat 32 read) 1024#32 s := by
    constructor
    · exact pc
    · exact (regs 2 (by decide) (by decide)).trans h.stackPtr
    · exact (regs 8 (by decide) (by decide)).trans h.framePtr
    · exact (regs 23 (by decide) (by decide)).trans h.statePtr
    · exact (regs 24 (by decide) (by decide)).trans h.cursor
    · exact h.stack
    · exact h.align
    · exact Memory.sub_block h.stack (off := 3280) (by decide) (by decide)
    · exact Memory.word_aligned sp 820 h.align
    · rw [BitVec.add_assoc,←BitVec.ofNat_add]
      exact Memory.block_access h.stack (off := 132+read) (by decide) (by have := h.capacity;omega)
    · exact h.layout.rx
    · exact h.layout.limits
    · simpa only [BitVec.add_assoc,show 3280#32+4#32=3284#32 by decide +kernel] using h.layout.maxBody
    · exact h.object
    · exact h.decoder.bounded
  have stable : MainChunkCoreFrame.At c d := by
    intro r hr
    apply regs r <;> (intro he;subst r;revert hr;decide +kernel)
  exact ⟨d,trace,pre,stable,csr⟩

end E5R.Thermostat.MainChunkLoopInput
