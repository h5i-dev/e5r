import Projects.thermostat.MainLengthPrepareRegs
import Projects.thermostat.MainGprBank
import Projects.thermostat.MainLengthStartMemory
import Projects.thermostat.MainLengthEnoughBranch
namespace E5R.Thermostat.MainLengthEnterRegs
open E5R E5R.Thermostat HttpRequestSpec MainLengthState

/-- Actual Content-Length setup and available-byte test. A full body skips
    receiving; a short body enters the proved UART receive invariant. -/
theorem contract {c ram input s head} (h : MainHeaderToBody.Ready c ram input s head)
    (amount : Nat) (kind : head.framing=.length amount) :
    ∃ n d after, 6≤n ∧ n≤17 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      Boundary d after input s head amount ∧ d.sameCsr c ∧ d.get 25=BitVec.ofNat 32 (head.len+amount) ∧ MainGprBank.Frame c d ∧ MainServeLayout.Frame ram after := by
  have amountBound := h.bounds.content amount kind
  have lenBound : head.len≤1024 := Nat.le_trans h.bounds.length.2 (Nat.min_le_right _ _)
  have totalBound : head.len+amount≤2048 := by omega
  have filledBound := h.stable.layout.bound
  have pc : c.pc=0x80000c26#32 := by simpa only [kind,MainBodyHeadDispatch.At] using h.cut
  have object : Memory.Block B fp 456 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 63508) (m := 456) h.stable.stack (by decide) (by decide)
    simpa only [show 0x80ff0000#32+63508#32=fp by decide +kernel] using block
  have payload : ramRead ram (fp+124#32) .w=BitVec.ofNat 32 amount := by
    simpa only [BitVec.add_assoc,show 116#32+8#32=124#32 by decide +kernel] using (h.view.framing amount kind).1
  let mid := MainLengthStart.memory ram fp (BitVec.ofNat 32 amount) (BitVec.ofNat 32 head.len) (BitVec.ofNat 32 input.length)
  obtain ⟨a,ta,apc,a25,a10,ar,ac⟩ := MainLengthStart.contract B c ram fp _ _ _ h.stable.fp h.length payload h.stable.layout.filledPtr h.stable.layout.filled object (by decide +kernel) pc
  have sum : BitVec.ofNat 32 amount+BitVec.ofNat 32 head.len=BitVec.ofNat 32 (head.len+amount) := by rw [←BitVec.ofNat_add,Nat.add_comm]
  have test : taken .geu (BitVec.ofNat 32 input.length) (BitVec.ofNat 32 amount+BitVec.ofNat 32 head.len)=decide (head.len+amount≤input.length) := by
    rw [sum]
    exact HeadTargetMath.geu input.length (head.len+amount) filledBound totalBound
  obtain ⟨b,tb,bpc,br,bc⟩ := MainLengthEnoughBranch.contract B a mid _ _ (decide (head.len+amount≤input.length)) apc a10 a25 test
  have kept (rr : Reg) (h25 : rr≠25) (h10 : rr≠10) : b.get rr=c.get rr := (br rr).trans (ar rr h25 h10)
  have csr : b.sameCsr c := bc.trans ac
  have future : ViewFrame.Region ram mid fp 449 := by
    simpa only [BitVec.add_zero] using MainLengthStartMemory.region ram fp _ _ (BitVec.ofNat 32 input.length) 0 449 (Or.inl (by decide)) (by decide)
  have stable : MainHeaderLoopTwo.Stable b mid input s := by
    refine ⟨(kept 2 (by decide) (by decide)).trans h.stable.sp,(kept 8 (by decide) (by decide)).trans h.stable.fp,
      (kept 19 (by decide) (by decide)).trans h.stable.uart,(kept 22 (by decide) (by decide)).trans h.stable.one,
      MainHeaderLayout.preserve h.stable.layout future,?_,?_,h.stable.invariant,h.stable.stack,?_⟩
    · intro i
      apply Eq.trans (MainLengthStartMemory.frame ram fp _ _ _ _ (fun j => WordZero.separated rx (fp+452#32) 2048 4 (by decide +kernel) (by decide +kernel) ⟨i.val,by have := i.isLt;omega⟩ j))
      exact h.stable.bytes i
    · apply AppState.preserve ram mid s h.stable.app
      intro i
      exact MainLengthStartMemory.frame ram fp _ _ _ _ (fun j => WordZero.separated 0x80ffebbc#32 (fp+452#32) 25 4 (by decide +kernel) (by decide +kernel) i j)
    · exact (congrArg Prod.fst csr).trans h.stable.masked
  have view : HeadCompletedView.At mid (fp+116#32) head := MainCopyView.head
    (MainLengthStartMemory.region ram fp _ _ (BitVec.ofNat 32 input.length) 116 304 (Or.inl (by decide)) (by decide)) head h.view
  have consumed : ramRead mid (fp+444#32) .w=BitVec.ofNat 32 head.len := (ViewFrame.word future 444 (by decide)).trans h.consumed
  have total : ramRead mid (fp+452#32) .w=BitVec.ofNat 32 (head.len+amount) :=
    (MainLengthStartMemory.total ram fp _ _ (BitVec.ofNat 32 input.length)).trans sum
  have state : At b mid input s head amount := ⟨stable,view,consumed,(kept 18 (by decide) (by decide)).trans h.two,
    (kept 20 (by decide) (by decide)).trans h.length,(kept 9 (by decide) (by decide)).trans h.tag,widen h.bounds (Nat.min_le_right _ _),kind,total⟩
  have bankFirst : MainGprBank.Frame c b := by
    intro rr safe
    have ne : ∀ r : Reg, r∈[21,23,26] → r≠25 ∧ r≠10 := by decide +kernel
    obtain ⟨h25,h10⟩ := ne rr safe
    exact kept rr h25 h10
  by_cases short : input.length<head.len+amount
  · have branch : decide (head.len+amount≤input.length)=false := decide_eq_false (by omega)
    have pc : b.pc=0x80000c3a#32 := by simpa only [branch,Bool.false_eq_true,ite_false] using bpc
    obtain ⟨d,td,ready,dc,dr,serveD⟩ := MainLengthPrepareRegs.contract state pc ((br 10).trans a10) short
    refine ⟨17,d,_,by decide,by decide,(ta.trans tb).trans td,?_,dc.trans csr,(dr 25 (by decide)).trans ((br 25).trans (a25.trans sum)),?_,MainServeLayout.trans (MainServeMemoryFrames.whole future (by decide)) serveD⟩
    · simpa only [Boundary,short,ite_true] using ready
    · intro rr safe
      have ne : ∀ r : Reg, r∈[21,23,26] → r∉MainLengthReadSetup.writes := by decide +kernel
      exact (dr rr (ne rr safe)).trans (bankFirst rr safe)
  · have branch : decide (head.len+amount≤input.length)=true := decide_eq_true (by omega)
    have pc : b.pc=0x80000c98#32 := by simpa only [branch,ite_true] using bpc
    refine ⟨6,b,mid,by decide,by decide,ta.trans tb,?_,csr,(br 25).trans (a25.trans sum),bankFirst,MainServeMemoryFrames.whole future (by decide)⟩
    simpa only [Boundary,short,ite_false] using (show b.pc=0x80000c98#32 ∧ At b mid input s head amount from ⟨pc,state⟩)
end E5R.Thermostat.MainLengthEnterRegs
