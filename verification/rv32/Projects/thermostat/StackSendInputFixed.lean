import Projects.thermostat.StackSendInput
import Projects.thermostat.MainResponseExtractedReply
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.StackSendInputFixed
open E5R E5R.Thermostat
abbrev small := StackBoard.board

theorem ram_byte {ram a v} (h : ReadBytes.Byte UartPlatform.board img ram a v)
    (inside : small.inRam a 1=true) : ReadBytes.Byte small img ram a v := by
  cases h with
  | ram _ value => exact .ram inside value
  | rom outside _ => exact False.elim (Bool.noConfusion (outside.symm.trans (StackBoard.included inside)))

/-- All actual firmware Send calls share these initialized stack/TX objects.
    Both possible MIME pointers are ROM, including the empty-slice sentinel. -/
theorem fixed {c ram raw status ct payload close head} (json : Bool)
    (h : SendInput.Pre c ram 0x80ffeb00#32 0x80fff878#32 0x80fffd38#32 0x80fff414#32 0x80ffffc7#32
      (MainResponseExtractedReply.pointer json) raw status ct payload close head) :
    StackSendInput.Pre c ram 0x80ffeb00#32 0x80fff878#32 0x80fffd38#32 0x80fff414#32 0x80ffffc7#32
      (MainResponseExtractedReply.pointer json) raw status ct payload close head := by
  have smallStack : Memory.Block small 0x80ffeb00#32 144 := by
    have region := Memory.sub_block StackBoard.available (off := 60160) (m := 144) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60160#32=0x80ffeb00#32 by decide +kernel] using region
  have smallObject : Memory.Block small 0x80fff878#32 89 := by
    have region := Memory.sub_block StackBoard.available (off := 63608) (m := 89) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+63608#32=0x80fff878#32 by decide +kernel] using region
  have smallResult : Memory.Block small 0x80fffd38#32 8 := by
    have region := Memory.sub_block StackBoard.available (off := 64824) (m := 8) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+64824#32=0x80fffd38#32 by decide +kernel] using region
  have smallTx : Memory.Block small 0x80fff414#32 1024 := by
    have region := Memory.sub_block StackBoard.available (off := 62484) (m := 1024) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+62484#32=0x80fff414#32 by decide +kernel] using region
  have outside : ∀ i : Fin ct.length,UartPlatform.board.inRam
      (MainResponseExtractedReply.pointer json+BitVec.ofNat 32 i.val) 1=false := by
    have finite : ∀ j : Fin 16,UartPlatform.board.inRam
        (MainResponseExtractedReply.pointer json+BitVec.ofNat 32 j.val) 1=false := by
      rw [StackBoard.original_board]
      cases json <;> decide +kernel
    intro i
    exact finite ⟨i.val,Nat.lt_of_lt_of_le i.isLt h.ctBound⟩
  have source := StackAccess.rom_span h.source outside
  have payload : ReadBytes.Span small img ram (0x80fff414#32+192#32) payload := by
    refine ⟨h.payloadBytes.length,h.payloadBytes.nowrap,?_⟩
    intro i
    apply ram_byte (h.payloadBytes.bytes i)
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact Memory.block_access smallTx (off := 192+i.val) (width := 1) (by decide)
      (by have := i.isLt;have := SendInput.payload_bound h;omega)
  exact ⟨h.pc,
    h.sp,
    h.resultArg,
    h.objectArg,
    smallStack,
    h.stackAligned,
    smallObject,
    h.objectAligned,
    smallResult,
    h.resultAligned,
    smallTx,
    h.txStrict,
    h.objectStack,
    h.txStack,
    h.objectTx,
    h.resultStack,
    h.resultObject,
    h.resultTx,
    h.ctStack,
    h.ctObject,
    h.ctTx,
    source,
    payload,
    h.rawBound,
    h.statusLo,
    h.statusHi,
    h.ctBound,
    h.field,
    h.clipped,
    h.fresh,
    h.capacity,
    h.ioWord,
    h.txWord,
    h.ctWord,
    h.ctLength,
    h.bodyLength,
    h.statusWord,
    h.closeWord,
    h.headWord⟩
end E5R.Thermostat.StackSendInputFixed
