import Projects.thermostat.MainHeaderLoopTwo
import Projects.thermostat.MainHeadCopy
import Projects.thermostat.MainBodyHeadDispatch
import Projects.thermostat.MainBodyHeadMemory
import Projects.thermostat.MainHeadAcceptedBounds
namespace E5R.Thermostat.MainHeaderToBody
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32
abbrev fp := 0x80fff814#32

structure Ready (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) (head : Head) : Prop where
  cut : MainBodyHeadDispatch.At c head.framing
  stable : MainHeaderLoopTwo.Stable c ram input s
  view : HeadCompletedView.At ram (fp+116#32) head
  consumed : ramRead ram (fp+444#32) .w=BitVec.ofNat 32 head.len
  two : c.get 18=2#32
  length : c.get 20=BitVec.ofNat 32 head.len
  tag : c.get 9=HeadCompletedView.framingTag head.framing
  bounds : MainHeadAcceptedBounds.At (min input.length 1024) 1024 head

/-- The actual successful main parser boundary through the RAM copy and all
    framing dispatches. The App, RX bytes and live object layout survive. -/
theorem contract {c ram input s head}
    (h : MainHeaderLoopTwo.Boundary c ram input s (.done head))
    (parsed : HttpRequestBytes.parse input 1024 1024=.done head) :
    ∃ n d, 416≤n ∧ n≤417 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,MainBodyHeadMemory.memory ram sp head⟩ ∧
      Ready d (MainBodyHeadMemory.memory ram sp head) input s head ∧ d.sameCsr c := by
  obtain ⟨pc,stable,view,two⟩ := h
  have stack : Memory.Block B sp 4928 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60304) (m := 4928) stable.stack (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have object : Memory.Block B fp 448 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 63508) (m := 448) stable.stack (by decide) (by decide)
    simpa only [show 0x80ff0000#32+63508#32=fp by decide +kernel] using block
  have source : HeadCompletedView.At ram (sp+4520#32) head := by simpa only [HeadFinalResult.At,show sp+4520#32=0x80fffd38#32 by decide +kernel] using view
  obtain ⟨a,ta,apc,asp,saved,copied,ac⟩ := MainHeadCopy.contract B c ram sp head pc stable.sp stack (by decide +kernel) source
  have a8 : a.get 8=fp := saved.x8.trans (by simpa only [MainHeadCopy.values,show ¬((8 : Reg)=1) by decide,ite_false] using stable.fp)
  have a18 : a.get 18=2#32 := saved.x18.trans (by simpa only [MainHeadCopy.values,show ¬((18 : Reg)=1) by decide,ite_false] using two)
  have a22 : a.get 22=1#32 := saved.x22.trans (by simpa only [MainHeadCopy.values,show ¬((22 : Reg)=1) by decide,ite_false] using stable.one)
  have copyView : HeadCompletedView.At (MainHeadCopy304.memory ram sp) (fp+116#32) head := by
    simpa only [show sp+3320#32=fp+116#32 by decide +kernel] using copied
  obtain ⟨n,d,lo,hi,td,cut,len,tag,dr,dc⟩ := MainBodyHeadDispatch.contract B a _ fp head apc a8 a18 a22 copyView object (by decide +kernel)
  have csr : d.sameCsr c := dc.trans ac
  have afterStable : MainHeaderLoopTwo.Stable d (MainBodyHeadMemory.memory ram sp head) input s := by
    refine ⟨(dr 2 (by decide) (by decide)).trans asp,(dr 8 (by decide) (by decide)).trans a8,
      (dr 19 (by decide) (by decide)).trans (saved.x19.trans ?_),
      (dr 22 (by decide) (by decide)).trans a22,MainBodyHeadMemory.layout ram head input.length stable.layout,?_,?_,stable.invariant,stable.stack,?_⟩
    · simpa only [MainHeadCopy.values,show ¬((19 : Reg)=1) by decide,ite_false] using stable.uart
    · intro i
      have frame := MainBodyHeadMemory.frame ram sp head 132 2048 (by decide) (Or.inl (by decide)) (Or.inl (by decide))
      exact (show MainBodyHeadMemory.memory ram sp head (0x80ffec14#32+BitVec.ofNat 32 i.val)=ram (0x80ffec14#32+BitVec.ofNat 32 i.val) from by simpa only [show sp+132#32=0x80ffec14#32 by decide +kernel] using frame ⟨i.val,by have := i.isLt;have := stable.layout.bound;omega⟩).trans (stable.bytes i)
    · apply AppState.preserve ram _ s stable.app
      simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using MainBodyHeadMemory.frame ram sp head 44 25 (by decide) (Or.inl (by decide)) (Or.inl (by decide))
    · exact (congrArg Prod.fst csr).trans stable.masked
  have afterView : HeadCompletedView.At (MainBodyHeadMemory.memory ram sp head) (fp+116#32) head := by
    simpa only [show sp+3320#32=fp+116#32 by decide +kernel] using MainBodyHeadMemory.head ram sp head stack source
  have consumed : ramRead (MainBodyHeadMemory.memory ram sp head) (fp+444#32) .w=BitVec.ofNat 32 head.len := by
    simpa only [show sp+3204#32=fp by decide +kernel] using MainBodyHeadMemory.consumed ram sp head
  refine ⟨412+n,d,by omega,by omega,?_,⟨cut,afterStable,afterView,consumed,(dr 18 (by decide) (by decide)).trans a18,len,tag,MainHeadAcceptedBounds.bytes input head parsed⟩,csr⟩
  simpa only [MainBodyHeadMemory.memory,show sp+3204#32=fp by decide +kernel] using ta.trans td
end E5R.Thermostat.MainHeaderToBody
