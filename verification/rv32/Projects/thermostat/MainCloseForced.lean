import Projects.thermostat.MainCloseForcedCore
import Projects.thermostat.MainCloseCommitFrame
import Projects.thermostat.MainCloseReady
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.MainCloseForced
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := MainRequestBuild.B
abbrev sp := MainRequestBuild.sp
abbrev fp := MainRequestBuild.fp
abbrev rx := MainRequestBuild.rx

theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat}
    (h : MainRequestBuild.Ready c ram input s head amount served) (forced : head.minor=0 ∨ 100≤served) :
    ∃ n d, n≤19 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,MainCloseCommit.memory ram sp 1#32⟩ ∧
      MainCloseReady.At d (MainCloseCommit.memory ram sp 1#32) input s head amount served true ∧ d.sameCsr c := by
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block h.stable.stack (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  obtain ⟨n,d,nb,trace,pc,d12,d10,d20,d21,d24,d25,dr,csr⟩ := MainCloseForcedCore.contract B c ram sp head.minor served h.bounds.version h.countBound forced h.pc h.stable.sp
    (by simpa only [show sp+3204#32=fp by decide +kernel] using h.stable.fp) h.minorReg h.countReg stack (by decide +kernel)
    (by simpa only [show fp+44#32=sp+3248#32 by decide +kernel,show sp+3204#32=fp by decide +kernel] using h.serve.config)
    (by simpa only [show fp+8#32=sp+3212#32 by decide +kernel] using h.serve.requests)
    (by simpa only [show fp+68#32=sp+3272#32 by decide +kernel] using h.serve.txCapacity)
  let after := MainCloseCommit.memory ram sp 1#32
  have frame (off size : Nat) (bound : off+size≤5232) (apart : off+size≤3304 ∨ 3305≤off) : ViewFrame.Region ram after (sp+BitVec.ofNat 32 off) size := MainCloseCommitFrame.frame ram sp 1#32 off size bound apart
  have keep (r : Reg) (safe : r∈[2,8,9,18,19,22,23,26,27]) : d.get r=c.get r := by
    have ne : ∀ r : Reg, r∈[2,8,9,18,19,22,23,26,27] → r≠10 ∧ r≠11 ∧ r≠12 ∧ r≠20 ∧ r≠21 ∧ r≠24 ∧ r≠25 ∧ r≠1 := by decide +kernel
    obtain ⟨a,b,e,f,g,i,j,k⟩ := ne r safe
    exact dr r a b e f g i j k
  have future : ViewFrame.Region ram after fp 96 := by
    simpa only [show sp+3204#32=fp by decide +kernel] using frame 3204 96 (by decide) (Or.inl (by decide))
  have stable : MainTransactionStable.At d after input s := by
    refine ⟨(keep 2 (by decide)).trans h.stable.sp,(keep 8 (by decide)).trans h.stable.fp,
      (keep 19 (by decide)).trans h.stable.uart,(keep 22 (by decide)).trans h.stable.one,h.stable.bound,
      (ViewFrame.word future 84 (by decide)).trans h.stable.filled,?_,?_,h.stable.invariant,h.stable.stack,(congrArg Prod.fst csr).trans h.stable.masked⟩
    · intro i
      have byte := frame 132 2048 (by decide) (Or.inl (by decide)) ⟨i.val,by have := i.isLt;have := h.stable.bound;omega⟩
      have atByte : after (rx+BitVec.ofNat 32 i.val)=ram (rx+BitVec.ofNat 32 i.val) := by simpa only [show sp+132#32=rx by decide +kernel] using byte
      exact atByte.trans (h.stable.bytes i)
    · apply AppState.preserve ram after s h.stable.app
      simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using frame 44 25 (by decide) (Or.inl (by decide))
  have stored := MainRequestStored.preserve (MainRequestStored.fromReady h) (frame 3312 376 (by decide) (Or.inr (by decide)))
  have flag : after (sp+3304#32)=Encoding.boolByte true := by
    simpa only [Encoding.boolByte,ite_true,show (1 : BitVec 8)=1#8 by decide +kernel,show byteOf 1#32 0=1#8 by decide +kernel] using MainCloseCommitFrame.byte ram sp 1#32
  have spec : true=MainCloseSpec.mustClose head.minor served (MainRequestSpans.raw input head amount) (MainRequestInputs.entries head) := by
    rcases forced with version|count
    · rw [version];exact (MainCloseSpec.http10 _ _ _).symm
    · exact (MainCloseSpec.limit _ _ count _ _).symm
  exact ⟨n,d,nb,trace,⟨pc,stable,stored,MainServeLayout.preserve (MainServeMemoryFrames.whole future (by decide)) h.serve,h.countBound,h.positive,
    (keep 18 (by decide)).trans h.countReg,(keep 9 (by decide)).trans h.minorReg,(keep 23 (by decide)).trans h.future,
    (keep 26 (by decide)).trans h.three,(keep 27 (by decide)).trans h.low,d20,d21,d24,d25,d12,d10,
    (ViewFrame.word future 92 (by decide)).trans h.usedWord,flag,spec⟩,csr⟩
end E5R.Thermostat.MainCloseForced
