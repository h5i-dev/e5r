import Projects.thermostat.MainRequestZeroCall
import Projects.thermostat.ResetZeroMemsetQuiet
import Projects.thermostat.ViewFrame
import Projects.thermostat.FrameOffsets
set_option autoImplicit false
namespace E5R.Thermostat.MainRequestZero
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) := WordZero.writes ram (sp+3648#32) 9

/-- Real six-instruction call and complete aligned36-byte memset. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc=0x80001230#32) (h2 : c.get 2=sp) (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 52 ⟨c,ram⟩ ⟨d,memory ram sp⟩ ∧ d.pc=0x80001246#32 ∧
      (∀ r : Reg, r≠1 → r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → r≠15 → r≠16 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,call,pa,a12,a10,a11,a1,ar,ac⟩ := MainRequestZeroCall.contract B c ram sp h2 hp
  have block : Memory.Block B (sp+3648#32) 36 := Memory.sub_block stack (off := 3648) (by decide) (by decide)
  have top : (sp+3648#32).toNat+4*9<2^32 := by
    rw [WordZero.add_nat sp 3648 (by have := stack.2.2;omega)]
    have := stack.2.2
    omega
  obtain ⟨d,zero,pd,dc,dr,_,_⟩ := ZeroMemset.contract_quiet B a ram (sp+3648#32) 9 pa a10 a11 a12 (by decide)
    (Memory.word_aligned sp 912 aligned) block top
  refine ⟨d,call.trans zero,?_,?_,dc.trans ac⟩
  · rw [a1] at pd
    exact pd.trans (by decide +kernel)
  · intro r h1 h10 h11 h12 h13 h14 h15 h16
    exact (dr r h12 h13 h14 h15 h16).trans (ar r h12 h10 h11 h1)

theorem bytes {B : Board} (ram : Word → BitVec 8) (sp : Word) (stack : Memory.Block B sp 5232) :
    ∀ i : Fin 36, memory ram sp ((sp+3648#32)+BitVec.ofNat 32 i.val)=0#8 := by
  unfold memory
  apply WordZero.zero_bytes ram (sp+3648#32) 9
  rw [WordZero.add_nat sp 3648 (by have := stack.2.2;omega)]
  have := stack.2.2
  omega

theorem frame (ram : Word → BitVec 8) (sp : Word) (off size : Nat) (bound : off+size≤5232)
    (apart : off+size≤3648 ∨ 3684≤off) : ViewFrame.Region ram (memory ram sp) (sp+BitVec.ofNat 32 off) size := by
  intro i
  apply WordZero.frame
  intro j
  have hj : j.val<36 := j.isLt
  simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using FrameOffsets.ne sp off 3648 i.val j.val
    (by have := i.isLt;omega) (by omega) (by have := i.isLt;rcases apart with h|h <;>omega)
end E5R.Thermostat.MainRequestZero
