import Projects.thermostat.RejectResponseView
import Projects.thermostat.RejectResponseComplete
import Projects.thermostat.MainSend
import Projects.thermostat.LoopReady
set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.RejectResponseReady
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32
abbrev fp := 0x80fff814#32

/-- Actual parser-rejection response, including send Future, success dispatch
    and outer restart. No padding bytes or response descriptor are assumed. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot) (served status : Nat)
    (pc : c.pc=0x80001bbc#32) (spWord : c.get 2=sp) (fpWord : c.get 8=fp)
    (uart : c.get 19=0x10000000#32) (one : c.get 22=1#32) (tag : c.get 10=1#32)
    (error : c.get 27=BitVec.ofNat 32 status) (masked : c.mie_=false)
    (stack : Memory.Block B 0x80ff0000#32 65536) (app : AppState.At ram s) (inv : Spec.Inv s)
    (bank : MainGprBank.At c) (layout : MainServeLayout.At ram served)
    (capacity : ramRead ram 0x80ffeba0#32 .w=2048#32) (routes : MainRouterTable.At ram)
    (lo : 200≤status) (hi : status≤599)
    (slots : List UartTxLoop.Slot) (length : slots.length=(ResponseHeadSpec.bytes status [] 0 true).length) :
    ∃ d n after, n≤2562+UartWriteAll.time (ResponseHeadSpec.bytes status [] 0 true) slots ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads slots)
        (UartTxLoop.events (ResponseHeadSpec.bytes status [] 0 true)) ∧ LoopReady.At d after s 0 := by
  have object : Memory.Block B fp 148 := by
    have part := Memory.sub_block stack (off := 63508) (m := 148) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+63508#32=fp by decide +kernel] using part
  let mid := RejectResponseSetup.memory ram 0x80ffffc7#32 (BitVec.ofNat 32 status)
  obtain ⟨a,setup,apc,_,a24,a18,a10,a11,_,a1,ar,ac⟩ := RejectResponseSetup.contract B c ram 0x80ffffc7#32 (BitVec.ofNat 32 status)
    spWord fpWord one tag error layout.tx layout.txCapacity layout.uart object pc
  have a2 := (ar 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans spWord
  have a8 := (ar 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans fpWord
  have a19 := (ar 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans uart
  have a22 := (ar 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans one
  have aBank : MainGprBank.At a := MainGprBank.preserve (fun r mem => by
    have ne : ∀ r : Reg, r∈[21,23,26] → r≠9 ∧ r≠24 ∧ r≠18 ∧ r≠10 ∧ r≠11 ∧ r≠12 ∧ r≠1 := by decide +kernel
    obtain ⟨n9,n24,n18,n10,n11,n12,n1⟩ := ne r mem
    exact ar r n9 n24 n18 n10 n11 n12 n1) bank
  have desc := RejectResponseView.descriptor ram 0x80ffffc7#32 status hi
  have pre := MainSend.input a mid 0x80ffffc7#32 1#32 status [] [] true false apc a2 a10 a11 stack (by decide) lo hi
    (by decide) (by intro b mem;cases mem) desc (Bytes.empty B mid _) (ReadBytes.of_ram (Bytes.empty B mid _))
    (WordRegions.before _ _ _ _ (by decide) (by decide)) (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
  have emptyBody : ResponseHeadSpec.body status false []=[] := by simp [ResponseHeadSpec.body]
  obtain ⟨b,nb,rb,bound,send,ret,result,_,_,_,sendFrame⟩ := Send.contract a mid 0x80ffeb00#32 0x80fff878#32 0x80fffd38#32
    0x80fff414#32 0x80ffffc7#32 1#32 0 status [] [] true false pre slots [] length (by rw [emptyBody];rfl)
  have bpc : b.pc=0x80001c0a#32 := by rw [ret.pc,a1];decide +kernel
  have b8 := ret.x8.trans a8
  have b24 := ret.x24.trans a24
  have b21 := ret.x21.trans aBank.minusOne
  have objectBig : Memory.Block B fp 1320 := by
    have part := Memory.sub_block stack (off := 63508) (m := 1320) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+63508#32=fp by decide +kernel] using part
  have tagB : ramRead rb (fp+1316#32) .w=0xffffffff#32 := by
    simpa only [fp,show 0x80fff814#32+1316#32=0x80fffd38#32 by decide +kernel,BitVec.add_zero] using result
  obtain ⟨e,complete,epc,_,_,er,ec⟩ := RejectResponseComplete.contract B b rb b8 b21 b24 tagB objectBig bpc
  have low : ViewFrame.Region ram rb sp 132 := by
    have first := RejectResponseView.caller_frame ram 0x80ffffc7#32 (BitVec.ofNat 32 status)
    intro i
    apply (sendFrame _
      (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)).trans
    exact first ⟨i.val,by have := i.isLt;omega⟩
  have appRegion : ViewFrame.Region ram rb 0x80ffebbc#32 25 := by
    intro i
    have addr : 0x80ffebbc#32+BitVec.ofNat 32 i.val=sp+BitVec.ofNat 32 (44+i.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [addr]
    exact low ⟨44+i.val,by have := i.isLt;omega⟩
  have appB := AppState.preserve ram rb s app appRegion
  have capB : ramRead rb 0x80ffeba0#32 .w=2048#32 := by
    have word := ViewFrame.word low 16 (by decide)
    have w : ramRead rb 0x80ffeba0#32 .w=ramRead ram 0x80ffeba0#32 .w := by
      simpa only [sp,show 0x80ffeb90#32+16#32=0x80ffeba0#32 by decide +kernel] using word
    exact w.trans capacity
  have routesB : MainRouterTable.At rb := by
    apply MainRouterTable.preserve routes
    intro i
    have addr : 0x80ffebd8#32+BitVec.ofNat 32 i.val=sp+BitVec.ofNat 32 (72+i.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [addr]
    exact low ⟨72+i.val,by have := i.isLt;omega⟩
  have e2 := (er 2 (by decide) (by decide)).trans (ret.sp.trans a2)
  have e8 := (er 8 (by decide) (by decide)).trans b8
  have e19 := (er 19 (by decide) (by decide)).trans (ret.x19.trans a19)
  have e22 := (er 22 (by decide) (by decide)).trans (ret.x22.trans a22)
  have e18 := (er 18 (by decide) (by decide)).trans (ret.x18.trans a18)
  have eMask : e.mie_=false := (congrArg Prod.fst ((ec.trans ret.csr).trans ac)).trans masked
  have eBank : MainGprBank.At e := by
    refine ⟨(er 21 (by decide) (by decide)).trans b21,
      (er 23 (by decide) (by decide)).trans (ret.x23.trans aBank.future),
      (er 26 (by decide) (by decide)).trans (ret.x26.trans aBank.three)⟩
  obtain ⟨d,after,restart,ready,serveAfter,capFrame,routeFrame,bankFrame⟩ := LoopClose.contract e rb s epc e2 e8 e19 e22 e18 eMask stack appB inv capB
  have readyLoop : LoopReady.At d after s 0 := by
    refine ⟨ready,MainGprBank.preserve bankFrame eBank,serveAfter,by decide,?_,MainRouterTable.preserve routesB routeFrame⟩
    have word := ViewFrame.word capFrame 0 (by decide)
    have w : ramRead after 0x80ffeba0#32 .w=ramRead rb 0x80ffeba0#32 .w := by simpa only [BitVec.add_zero] using word
    exact w.trans capB
  have timeB : nb≤2414+UartWriteAll.time (ResponseHeadSpec.bytes status [] 0 true) slots := by
    simp only [emptyBody,List.length_nil] at bound
    change nb≤2400+UartWriteAll.time (ResponseHeadSpec.bytes status [] 0 true) slots+14 at bound
    omega
  refine ⟨d,24+nb+6+118,after,by omega,?_,readyLoop⟩
  have trace := ((setup.observed.trans send).trans complete.observed).trans restart.observed
  simpa only [emptyBody,List.length_nil,UartTxLoop.reads,UartTxLoop.events,List.flatMap_nil,List.map_nil,List.append_nil,List.nil_append] using trace
end E5R.Thermostat.RejectResponseReady
