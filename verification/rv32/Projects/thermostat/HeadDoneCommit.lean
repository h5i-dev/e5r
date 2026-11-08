import Projects.thermostat.HeadDoneCopyCall
import Projects.thermostat.HeadCopyHeader256
import Projects.thermostat.HeadDoneMemory
import Projects.thermostat.HeadReturn
import Projects.thermostat.HeadSavedTail
namespace E5R.Thermostat.HeadDoneCommit
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp tag low high method targetStart targetEnd count length minor : Word) :=
  HeadDoneStore.memory (HeadCopyHeader256.memory ram sp) sp tag low high method targetStart targetEnd count length minor

/-- Actual success-path memcpy call, result stores and complete parser ABI return.
    This entry follows the separate Host and framing checks. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (sp tag low high method targetStart targetEnd count length minor : Word) (saved : Reg → Word)
    (hp : c.pc=0x80003486#32) (h2 : c.get 2=sp) (h20 : c.get 20=tag) (h18 : c.get 18=low)
    (h19 : c.get 19=high) (h9 : c.get 9=count) (h24 : c.get 24=length) (h8 : c.get 8=minor)
    (output : ramRead ram (sp+52#32) .w=sp+4904#32)
    (methodWord : ramRead ram (sp+20#32) .w=method)
    (targetStartWord : ramRead ram (sp+24#32) .w=targetStart)
    (targetEndWord : ramRead ram (sp+28#32) .w=targetEnd)
    (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0) (stored : HeadSaved.At ram sp saved) :
    ∃ d, Quiet.Steps B img 380 ⟨c,ram⟩ ⟨d,memory ram sp tag low high method targetStart targetEnd count length minor⟩ ∧
      d.pc=saved 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d saved ∧ d.sameCsr c := by
  have smallStack : Memory.Block B sp 56 := by simpa only [BitVec.add_zero] using Memory.sub_block stack (off := 0) (by decide) (by decide)
  obtain ⟨a,ta,apc,a21,a10,a11,a12,a1,ar,ac⟩ := HeadDoneCopyCall.contract B c ram sp (sp+4904#32) h2 output smallStack aligned hp
  have asp : a.get 2=sp := (ar 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2
  obtain ⟨b,tb,ret,_⟩ := HeadCopyHeader256.contract B a ram sp apc asp
    (by simpa only [show (sp+4904#32)+32#32=sp+4936#32 by rw [BitVec.add_assoc];rfl] using a10) a11 a12 stack aligned
  have bsp : b.get 2=sp := ret.sp.trans asp
  have bpc : b.pc=0x8000349a#32 := by rw [ret.pc,a1];decide +kernel
  have stable : ∀ r : Reg, r∈([8,9,18,19,20,24] : List Reg) → r≠21 ∧ r≠10 ∧ r≠11 ∧ r≠12 ∧ r≠1 := by decide +kernel
  have keep (r : Reg) (h : r∈([8,9,18,19,20,24] : List Reg)) : a.get r=c.get r := by
    obtain ⟨h21,h10,h11,h12,h1⟩ := stable r h
    exact ar r h21 h10 h11 h12 h1
  have scratch : ViewFrame.Region ram (HeadCopyHeader256.memory ram sp) sp 56 := by
    simpa only [BitVec.add_zero] using HeadCopyHeader256.frame ram sp 0 56 (by decide) (Or.inl (by decide))
  have word (off : Nat) (bound : off+4≤56) := ViewFrame.word scratch off bound
  have outBlock : Memory.Block B (sp+4904#32) 297 := Memory.sub_block stack (by decide) (by decide)
  obtain ⟨z,tz,zpc,_,zr,zc⟩ := HeadDoneStore.contract B b (HeadCopyHeader256.memory ram sp) sp tag low high method targetStart targetEnd count length minor
    bsp (ret.x21.trans a21) (ret.x20.trans ((keep 20 (by decide)).trans h20))
    (ret.x18.trans ((keep 18 (by decide)).trans h18)) (ret.x19.trans ((keep 19 (by decide)).trans h19))
    (ret.x9.trans ((keep 9 (by decide)).trans h9)) (ret.x24.trans ((keep 24 (by decide)).trans h24))
    (ret.x8.trans ((keep 8 (by decide)).trans h8))
    ((word 20 (by decide)).trans methodWord) ((word 24 (by decide)).trans targetStartWord) ((word 28 (by decide)).trans targetEndWord)
    smallStack outBlock aligned bpc
  have savedCopy : HeadSaved.At (HeadCopyHeader256.memory ram sp) sp saved :=
    HeadSavedTail.preserve stored (HeadCopyHeader256.frame ram sp 332 52 (by decide) (Or.inl (by decide)))
  have savedStore := HeadSavedTail.preserve savedCopy
    (HeadDoneMemory.region (HeadCopyHeader256.memory ram sp) sp tag low high method targetStart targetEnd count length minor 332 52 (by decide) (Or.inl (by decide)) (Or.inl (by decide)))
  have abiStack : Memory.Block B sp 384 := by simpa only [BitVec.add_zero] using Memory.sub_block stack (off := 0) (by decide) (by decide)
  obtain ⟨d,td,dpc,dsp,regs,_,dc⟩ := HeadReturn.contract B z _ sp saved zpc ((zr 2 (by decide)).trans bsp) abiStack aligned savedStore
  exact ⟨d,((ta.trans tb).trans tz).trans td,dpc,dsp,regs,((dc.trans zc).trans ret.csr).trans ac⟩
end E5R.Thermostat.HeadDoneCommit
