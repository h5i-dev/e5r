import Projects.thermostat.MainChunkExhausted
import Projects.thermostat.MainChunkCapacityFull
import Projects.thermostat.MainChunkCapacityStatus
import Projects.thermostat.MainChunkLoopInvariant
import Projects.thermostat.QuietPrefix
namespace E5R.Thermostat.MainChunkCapacityRefusal
open E5R E5R.Thermostat

/-- Exhausting the actual 2048-byte raw buffer chooses the real 413 error
    cutpoint. It performs no out-of-bounds RX read or write. -/
theorem contract {B c ram sp start read written filled s}
    (h : MainChunkLoopInvariant.At B c ram sp start read written filled s)
    (empty : read=filled) (full : filled=2048) :
    ∃ d, Quiet.Steps B img 9 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000a9a#32 ∧
      d.get 27=413#32 ∧ d.get 9=3#32 ∧ d.get 18=0#32 ∧ d.sameCsr c ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠27 → r≠9 → r≠18 → d.get r=c.get r) := by
  obtain ⟨a,guard,pc,val,frame,csr⟩ := MainChunkExhausted.contract B c ram sp 2048#32
    h.framePtr (by simpa only [empty,full] using h.cursor) h.stack h.align h.layout.filledPtr
    (by simpa only [full] using h.filledWord) h.pc
  obtain ⟨b,test,pc2,cap,frame2,csr2⟩ := MainChunkCapacityFull.contract B a ram sp
    ((frame 8 (by decide)).trans h.framePtr) val h.stack h.align h.layout.capacity pc
  obtain ⟨d,status,pc3,zero,tag,code,frame3,csr3⟩ := MainChunkCapacityStatus.contract B b ram pc2
  refine ⟨d,(guard.trans test).trans status,pc3,code,tag,zero,csr3.trans (csr2.trans csr),?_⟩
  intro r h10 h11 h27 h9 h18
  exact (frame3 r h18 h9 h27).trans ((frame2 r h11).trans (frame r h10))

theorem safe_contract {B c ram sp start read written filled s}
    (h : MainChunkLoopInvariant.At B c ram sp start read written filled s)
    (empty : read=filled) (full : filled=2048) :
    ∃ d, Trace.Closed B img 9 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000a9a#32 ∧
      d.get 27=413#32 ∧ d.get 9=3#32 ∧ d.get 18=0#32 ∧
      (∀ k e reads evs, k<9 → Observed.Steps B img k ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨d,trace,pc,code,tag,zero,csr,frame⟩ := contract h empty full
  exact ⟨d,Interrupt.close trace.det h.masked,pc,code,tag,zero,
    fun _ _ _ _ hk actual => QuietPrefix.safe trace h.masked hk actual⟩
end E5R.Thermostat.MainChunkCapacityRefusal
