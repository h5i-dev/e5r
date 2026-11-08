import Projects.thermostat.MainRouterSetup
import Projects.thermostat.MainRouterFirstCall
import Projects.thermostat.MainRouterCloseReset
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.MainRouterEntry
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := MainRequestBuild.B
abbrev sp := MainRequestBuild.sp
abbrev fp := MainRequestBuild.fp
abbrev rx := MainRequestBuild.rx

/-- Real first path-matcher call, with live parsed Request and route futures.
    This does not assume that this pattern, method or handler will match. -/
structure At (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) (head : Head) (amount served : Nat) (close : Bool) : Prop where
  pc : c.pc=0x8000283a#32
  stable : MainTransactionStable.At c ram input s
  stored : MainRequestStored.At ram input head amount
  serve : MainServeLayout.At ram served
  table : MainRouterTable.At ram
  futureWords : ∀ i : Fin 5, ramRead ram (fp+BitVec.ofNat 32 (688+4*i.val)) .w=
    (match i.val with | 0 => 0x80ffebf8#32 | 1 => 0x80fff880#32 | 2 => 0x80ffebbc#32 | 3 => 0x80fff4d4#32 | _ => 832#32)
  closeByte : ram (sp+3304#32)=Encoding.boolByte close
  closeSpec : close=MainCloseSpec.mustClose head.minor served (MainRequestSpans.raw input head amount) (MainRequestInputs.entries head)
  ret : c.get 1=0x800013d2#32
  pattern : c.get 10=0x80005b83#32
  patternLength : c.get 11=6#32
  path : c.get 12=rx+BitVec.ofNat 32 head.target.1
  pathLength : c.get 13=MainRequestBuild.pathLength input head
  params : c.get 14=0x80fff9d0#32
  two : c.get 18=2#32
  future : c.get 23=0x80fff9f0#32
  firstSlot : c.get 24=sp+3740#32
  secondSlot : c.get 25=sp+3784#32
  three : c.get 26=3#32
  low : c.get 27=BitVec.ofNat 32 amount

theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainCloseReady.At c ram input s head amount served close) (routes : MainRouterTable.At ram) :
    ∃ d, Quiet.Steps B img 83 ⟨c,ram⟩ ⟨d,MainRouterSetup.memory ram⟩ ∧
      At d (MainRouterSetup.memory ram) input s head amount served close ∧ d.sameCsr c := by
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block h.stable.stack (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  obtain ⟨a,setup,pa,a11,a13,a10,a12,a14,a18,a15,ar,ac⟩ := MainRouterSetup.contract B c ram h.stable.sp h.stable.fp h.capacityReg h.stable.one stack
    (by simpa only [show MainServeLayout.fp+64#32=0x80fff854#32 by decide +kernel] using h.serve.tx)
    (by simpa only [show MainServeLayout.fp+48#32=0x80fff844#32 by decide +kernel] using h.serve.router)
    (by simpa only [show MainServeLayout.fp+52#32=0x80fff848#32 by decide +kernel] using h.serve.app) h.pc
  let after := MainRouterSetup.memory ram
  have frame (off size : Nat) (bound : off+size≤3688) : ViewFrame.Region ram after (sp+BitVec.ofNat 32 off) size :=
    MainRouterSetup.frame ram off size (by omega) (Or.inl bound)
  have table : MainRouterTable.At after := MainRouterTable.preserve routes (by
    simpa only [show sp+72#32=0x80ffebd8#32 by decide +kernel] using frame 72 60 (by decide))
  have stateFields := table ⟨4,by decide⟩
  have pattern : ramRead after 0x80ffebf8#32 .w=0x80005b83#32 := by simpa only [show 0x80ffebd8#32+BitVec.ofNat 32 (8*4)=0x80ffebf8#32 by decide +kernel] using stateFields.1
  have patternSize : ramRead after 0x80ffebfc#32 .w=6#32 := by simpa only [show 0x80ffebdc#32+BitVec.ofNat 32 (8*4)=0x80ffebfc#32 by decide +kernel] using stateFields.2.1
  have stored := MainRequestStored.preserve h.stored (frame 3312 376 (by decide))
  have path : ramRead after 0x80fff9b0#32 .w=rx+BitVec.ofNat 32 head.target.1 := stored.request.path
  have pathSize : ramRead after 0x80fff9b4#32 .w=MainRequestBuild.pathLength input head := stored.request.pathLength
  obtain ⟨d,call,pd,d10,d11,d12,d13,d14,d1,dr,dc⟩ := MainRouterFirstCall.contract B a after _ (MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2)
    a13 a14 stack pattern patternSize path pathSize pa
  have keep (r : Reg) (safe : r∈[2,8,19,22,23,24,25,26,27]) : d.get r=c.get r := by
    have ne : ∀ r : Reg, r∈[2,8,19,22,23,24,25,26,27] → r≠10 ∧ r≠11 ∧ r≠12 ∧ r≠13 ∧ r≠14 ∧ r≠1 ∧ r≠18 ∧ r≠15 := by decide +kernel
    obtain ⟨n10,n11,n12,n13,n14,n1,n18,n15⟩ := ne r safe
    exact (dr r n10 n11 n12 n13 n14 n1).trans (ar r n11 n13 n10 n12 n14 n18 n15)
  have future : ViewFrame.Region ram after fp 96 := by simpa only [show sp+3204#32=fp by decide +kernel] using frame 3204 96 (by decide)
  have stable : MainTransactionStable.At d after input s := by
    refine ⟨(keep 2 (by decide)).trans h.stable.sp,(keep 8 (by decide)).trans h.stable.fp,
      (keep 19 (by decide)).trans h.stable.uart,(keep 22 (by decide)).trans h.stable.one,h.stable.bound,
      (ViewFrame.word future 84 (by decide)).trans h.stable.filled,?_,?_,h.stable.invariant,h.stable.stack,?_⟩
    · intro i
      have byte := frame 132 2048 (by decide) ⟨i.val,by have := i.isLt;have := h.stable.bound;omega⟩
      have atByte : after (rx+BitVec.ofNat 32 i.val)=ram (rx+BitVec.ofNat 32 i.val) := by simpa only [show sp+132#32=rx by decide +kernel] using byte
      exact atByte.trans (h.stable.bytes i)
    · apply AppState.preserve ram after s h.stable.app
      simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using frame 44 25 (by decide)
    · exact (congrArg Prod.fst (dc.trans ac)).trans h.stable.masked
  have flag : after (sp+3304#32)=Encoding.boolByte close := by
    have byte := frame 3304 1 (by decide) ⟨0,by decide⟩
    simpa only [BitVec.add_zero] using byte.trans h.flag
  exact ⟨d,setup.trans call,⟨pd,stable,stored,MainServeLayout.preserve (MainServeMemoryFrames.whole future (by decide)) h.serve,
    table,MainRouterSetup.state_future ram,flag,h.spec,d1,d10,d11,d12,d13,d14,(dr 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a18,
    (keep 23 (by decide)).trans h.future,(keep 24 (by decide)).trans h.firstSlot,(keep 25 (by decide)).trans h.secondSlot,
    (keep 26 (by decide)).trans h.three,(keep 27 (by decide)).trans h.low⟩,dc.trans ac⟩
end E5R.Thermostat.MainRouterEntry
