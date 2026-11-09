import Projects.thermostat.RejectNextCore
import Projects.thermostat.RejectResponseReady
import Projects.thermostat.MainHeaderDispatchTwo
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.RejectBodyResponse
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32
abbrev fp := 0x80fff814#32

/-- The common actual rejected-Next continuation needs only the recurrence
    metadata and committed App, without a pre-compaction RX/header byte view.
    This is the body-refusal join, not a body-parser correctness assumption. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot) (served status : Nat)
    (cut : MainHeaderDispatchTwo.At c (.reject status))
    (spWord : c.get 2=sp) (fpWord : c.get 8=fp) (uart : c.get 19=0x10000000#32)
    (one : c.get 22=1#32) (masked : c.mie_=false) (stackAll : Memory.Block B 0x80ff0000#32 65536)
    (appBefore : AppState.At ram s) (invariant : Spec.Inv s) (bank : MainGprBank.At c)
    (layout : MainServeLayout.At ram served) (capacity : ramRead ram 0x80ffeba0#32 .w=2048#32)
    (routes : MainRouterTable.At ram) (lo : 200≤status) (hi : status≤599)
    (slots : List UartTxLoop.Slot) (length : slots.length=(ResponseHeadSpec.bytes status [] 0 true).length) :
    ∃ d n after, n≤3318+UartWriteAll.time (ResponseHeadSpec.bytes status [] 0 true) slots ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads slots)
        (UartTxLoop.events (ResponseHeadSpec.bytes status [] 0 true)) ∧ LoopReady.At d after s 0 := by
  obtain ⟨pc,zero,error,variant⟩ := cut
  have stack : Memory.Block B sp 5232 := by
    have part := Memory.sub_block stackAll (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using part
  obtain ⟨a,next,apc,tag,regs,csr,frame⟩ := RejectNextCore.contract B c ram sp pc spWord fpWord variant zero bank.minusOne one stack (by decide)
  let mid := RejectNextCore.memory ram sp
  have appFrame : ViewFrame.Region ram mid 0x80ffebbc#32 25 := by
    have sub := HeadRegionFrame.sub frame 44 25 (by decide)
    simpa only [sp,show 0x80ffeb90#32+44#32=0x80ffebbc#32 by decide +kernel] using sub
  have app := AppState.preserve ram mid s appBefore appFrame
  have serveFrame : ViewFrame.Region ram mid fp 92 := by
    have sub := HeadRegionFrame.sub frame 3204 92 (by decide)
    simpa only [sp,show 0x80ffeb90#32+3204#32=fp by decide +kernel] using sub
  have capWord : ramRead mid 0x80ffeba0#32 .w=2048#32 := by
    have word := ViewFrame.word frame 16 (by decide)
    have value : ramRead mid 0x80ffeba0#32 .w=ramRead ram 0x80ffeba0#32 .w := by
      simpa only [sp,show 0x80ffeb90#32+16#32=0x80ffeba0#32 by decide +kernel] using word
    exact value.trans capacity
  have routeFrame : ViewFrame.Region ram mid 0x80ffebd8#32 60 := by
    have sub := HeadRegionFrame.sub frame 72 60 (by decide)
    simpa only [sp,show 0x80ffeb90#32+72#32=0x80ffebd8#32 by decide +kernel] using sub
  have aBank : MainGprBank.At a := MainGprBank.preserve (fun r mem => by
    have subset : ∀ r : Reg, r∈[21,23,26] → r∈MainSavedGpr.regs := by decide +kernel
    exact regs r (subset r mem)) bank
  obtain ⟨d,n,after,bound,response,ready⟩ := RejectResponseReady.contract a mid s served status apc
    ((regs 2 (by decide)).trans spWord) ((regs 8 (by decide)).trans fpWord)
    ((regs 19 (by decide)).trans uart) ((regs 22 (by decide)).trans one) tag
    ((regs 27 (by decide)).trans error) ((congrArg Prod.fst csr).trans masked) stackAll app invariant aBank
    (MainServeLayout.preserve (MainServeLayout.region serveFrame) layout) capWord (MainRouterTable.preserve routes routeFrame) lo hi slots length
  exact ⟨d,756+n,after,by omega,by simpa only [List.nil_append] using next.observed.trans response,ready⟩
end E5R.Thermostat.RejectBodyResponse
