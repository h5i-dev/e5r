import Projects.thermostat.WriteReturnPrepare
import Projects.thermostat.StackAccess
import Projects.thermostat.StackNormalResponsePrepare
import Projects.thermostat.StackLoopWriteReturn
set_option autoImplicit false
namespace E5R.Thermostat.StackWriteReturnPrepare
open E5R E5R.Thermostat WriteReturnPrepare
abbrev B := StackBoard.board
theorem contract {kind c ram response served used json close headOnly}
    (h : Ready kind c ram response served used json close headOnly) :
    ∃ n d after,n≤42 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      NormalSendPhase.Ready d after response served used json close headOnly := by
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block StackBoard.available (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have small : (BitVec.ofNat 32 response.status).toNat<65536 := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := h.statusHi;omega)]
    have := h.statusHi;omega
  obtain ⟨a,na,mid,ba,ta,pa,a2,a8,a22,a12,a11,a20,a10,a13,a9,a24,ac,live,a19,a18,a23,a26⟩ :=
    StackLoopWriteReturn.extract kind c ram _ _ _ _ h.pc h.spWord h.fpWord h.two h.one stack h.responseView small
  have region (off size : Nat) (bound : off+size≤3780) : ViewFrame.Region ram mid (sp+BitVec.ofNat 32 off) size := by
    intro i
    have byte := live ⟨off+i.val,by have := i.isLt;omega⟩
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using byte
  have fpRegion : ViewFrame.Region ram mid fp 532 := by
    simpa only [show sp+3204#32=fp by decide +kernel] using region 3204 532 (by decide)
  have app := AppState.preserve ram mid response.state h.app (by
    simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using region 44 25 (by decide))
  have bytes : Bytes.Span UartPlatform.board mid 0x80fff4d4#32 response.payload := ViewFrame.span h.payload (by
    simpa only [show sp+2372#32=0x80fff4d4#32 by decide +kernel] using region 2372 response.payload.length (by have := h.bodyBound;omega))
  have cap : ramRead mid 0x80fff9fc#32 .w=832#32 := by
    simpa only [show fp+488#32=0x80fff9fc#32 by decide +kernel] using (ViewFrame.word fpRegion 488 (by decide)).trans h.replyCapacity
  have flag : mid 0x80fff878#32=(if close then 1#8 else 0#8) := by
    have byte := fpRegion ⟨100,by decide⟩
    have old : ram 0x80fff878#32=(if close then 1#8 else 0#8) := by cases close <;> exact h.closeByte
    simpa only [show fp+100#32=0x80fff878#32 by decide +kernel] using byte.trans old
  have method : MainMethod.head (mid 0x80fff9f4#32)=headOnly := by
    have byte := fpRegion ⟨480,by decide⟩
    have same : mid 0x80fff9f4#32=ram 0x80fff9f4#32 := by simpa only [show fp+480#32=0x80fff9f4#32 by decide +kernel] using byte
    rw [same];exact h.method
  have metadata := LoopTransactionMemory.caller h.metadata (ViewFrame.shrink live (by decide))
  have serve := MainServeLayout.preserve (MainServeLayout.region (ViewFrame.shrink fpRegion (by decide))) h.serve
  have extracted : NormalResponsePrepare.Ready a mid response served used json close headOnly 0x80001710#32 :=
    ⟨pa,a2,a8,a19.trans h.uart,a22,a18.trans h.two,a23.trans h.future,a26.trans h.three,
      (congrArg Prod.fst ac).trans h.masked,h.stack,app,h.invariant,serve,h.room,metadata,h.mime,h.bodyBound,h.statusLo,h.statusHi,
      a12,a11,a20,a10,a13,a9,a24,bytes,cap,flag,method⟩
  obtain ⟨d,after,prepare,ready⟩ := StackNormalResponsePrepare.prepare_extracted extracted
  exact ⟨na+29,d,after,by omega,ta.trans prepare,ready⟩
end E5R.Thermostat.StackWriteReturnPrepare
