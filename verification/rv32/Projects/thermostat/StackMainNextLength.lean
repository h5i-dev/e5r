import Projects.thermostat.MainNextLength
import Projects.thermostat.StackBoard
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.StackMainNextLength
open E5R E5R.Thermostat HttpRequestSpec MainNextLength
abbrev B := StackBoard.board

theorem contract {c ram input s head amount} (h : MainLengthState.At c ram input s head amount)
    (hp : c.pc=0x80000c98#32) (endReg : c.get 25=BitVec.ofNat 32 (head.len+amount))
    (full : head.len+amount≤input.length) :
    ∃ d, Quiet.Steps B img 407 ⟨c,ram⟩ ⟨d,MainNextLengthMemory.memory ram sp head amount⟩ ∧
      Ready d (MainNextLengthMemory.memory ram sp head amount) input s head amount ∧
      (∀ rr : Reg, rr∈[21,23,26] → d.get rr=c.get rr) ∧ d.sameCsr c := by
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60304) (m := 5232) StackBoard.available (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have fpEq : sp+3204#32=fp := by decide +kernel
  have view : HeadCompletedView.At ram (sp+3320#32) head := by simpa only [show sp+3320#32=fp+116#32 by decide +kernel] using h.view
  have a8pre : c.get 8=sp+3204#32 := by simpa only [fpEq] using h.stable.fp
  obtain ⟨a,ta,apc,asp,afp,a9,a18,a27,ar,array,headView,frame,ac⟩ := MainNextLengthPrefix.contract B c ram sp head amount hp h.stable.sp a8pre view h.kind (h.bounds.content amount h.kind) stack (by decide +kernel)
  have a25 : a.get 25=BitVec.ofNat 32 (head.len+amount) := (ar 25 (by decide)).trans endReg
  have consumed : ramRead (MainNextLengthPrefix.memory ram sp head) (sp+3648#32) .w=BitVec.ofNat 32 head.len := by
    have word := ViewFrame.word (frame 3648 4 (by decide) (by decide)) 0 (by decide)
    simp only [BitVec.add_zero] at word
    exact word.trans (by simpa only [show sp+3648#32=fp+444#32 by decide +kernel] using h.consumed)
  obtain ⟨d,td,dpc,d20,d24,dr,headAfter,arrayAfter,_,dc⟩ := MainNextLengthFinish.contract B a _ sp head _ apc asp afp a25 headView h.bounds.version consumed array stack (by decide +kernel)
  have csr : d.sameCsr c := dc.trans ac
  have stable : MainHeaderLoopTwo.Stable d (MainNextLengthMemory.memory ram sp head amount) input s := by
    refine ⟨(dr 2 (by decide)).trans asp,?_,(dr 19 (by decide)).trans ((ar 19 (by decide)).trans h.stable.uart),
      (dr 22 (by decide)).trans ((ar 22 (by decide)).trans h.stable.one),?_,?_,?_,h.stable.invariant,h.stable.stack,?_⟩
    · simpa only [fpEq] using (dr 8 (by decide)).trans afp
    · apply MainHeaderLayout.preserve h.stable.layout
      simpa only [fpEq] using MainNextLengthMemory.frame ram sp head amount 3204 449 (by decide) (by decide)
    · intro i
      have rx := MainNextLengthMemory.frame ram sp head amount 132 2048 (by decide) (by decide)
      exact (show MainNextLengthMemory.memory ram sp head amount (0x80ffec14#32+BitVec.ofNat 32 i.val)=ram (0x80ffec14#32+BitVec.ofNat 32 i.val) from by simpa only [show sp+132#32=0x80ffec14#32 by decide +kernel] using rx ⟨i.val,by have := i.isLt;have := h.stable.layout.bound;omega⟩).trans (h.stable.bytes i)
    · apply AppState.preserve ram _ s h.stable.app
      simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using MainNextLengthMemory.frame ram sp head amount 44 25 (by decide) (by decide)
    · exact (congrArg Prod.fst csr).trans h.stable.masked
  refine ⟨d,ta.trans td,⟨dpc,stable,(dr 9 (by decide)).trans a9,(dr 18 (by decide)).trans a18,(dr 27 (by decide)).trans a27,
    d20,d24,(dr 25 (by decide)).trans a25,headAfter,arrayAfter,
    MainNextLengthMemory.methodStart ram sp head amount,MainNextLengthMemory.methodEnd ram sp head amount,
    MainNextLengthMemory.targetStart ram sp head amount,MainNextLengthMemory.targetEnd ram sp head amount,
    MainNextLengthMemory.minor ram sp head amount,h.bounds,h.kind,full⟩,?_,csr⟩
  intro rr safe
  have subset : ∀ rr : Reg, rr∈[21,23,26] → rr∈[2,8,9,18,19,21,22,23,25,26,27] ∧ rr∈[19,20,21,22,23,24,25,26] := by decide +kernel
  obtain ⟨tailSafe,firstSafe⟩ := subset rr safe
  exact (dr rr tailSafe).trans (ar rr firstSafe)
end E5R.Thermostat.StackMainNextLength
