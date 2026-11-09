import Projects.thermostat.StackBoard
import Projects.thermostat.MainChunkBuffered
set_option autoImplicit false
namespace E5R.Thermostat.ChunkStackFrame
open E5R E5R.Thermostat

/-- Reindex only the proved stack-membership field. All real registers, RAM
    layouts, decoder state and cursor bounds are retained unchanged. -/
theorem loop {B1 B2 c ram sp start read written filled decoder}
    (h : MainChunkLoopInvariant.At B1 c ram sp start read written filled decoder)
    (stack : Memory.Block B2 sp 4928) : MainChunkLoopInvariant.At B2 c ram sp start read written filled decoder :=
  ⟨h.pc,h.stackPtr,h.framePtr,h.statePtr,h.cursor,h.one,h.uart,h.masked,stack,h.align,
    h.layout,h.filledWord,h.readWord,h.writeWord,h.object,h.decoder,h.startWritten,h.writtenRead,h.readFilled,h.capacity⟩

theorem boundary {B1 B2 c ram sp start filled result}
    (h : MainChunkBuffered.Boundary B1 c ram sp start filled result)
    (stack : Memory.Block B2 sp 4928) : MainChunkBuffered.Boundary B2 c ram sp start filled result := by
  cases stop : result.stop with
  | needInput =>
    simp only [MainChunkBuffered.Boundary,stop] at h ⊢
    exact loop h stack
  | done => simpa only [MainChunkBuffered.Boundary,stop] using h
  | reject status => simpa only [MainChunkBuffered.Boundary,stop] using h

theorem stack : Memory.Block StackBoard.board 0x80ffeb90#32 4928 := by
  have block := Memory.sub_block StackBoard.available (off := 60304) (m := 4928) (by decide) (by decide)
  simpa only [show 0x80ff0000#32+60304#32=0x80ffeb90#32 by decide +kernel] using block
end E5R.Thermostat.ChunkStackFrame
