import Projects.thermostat.CharRestore
import Projects.thermostat.CursorFinish
import Projects.thermostat.Memory
import Projects.thermostat.ParamMath
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.CharFinish
open E5R E5R.Thermostat

theorem store (B : Board) (c : Core) (ram : Word → BitVec 8) (obj : Word) (next : Nat)
    (hp : c.pc = 0x800023b4#32) (h19 : c.get 19 = obj) (h9 : c.get 9 = BitVec.ofNat 32 next)
    (hm : Memory.Block B obj 12) (ha : obj.toNat%4 = 0) :
    DetStep B img ⟨c,ram⟩ ⟨c.goto 0x800023b8#32,ramWrite ram (obj+8#32) (BitVec.ofNat 32 next) .w⟩ := by
  refine detStep_of (by rw [hp];decide) (by rw [hp];exact ch2147492788) fun o => ?_
  rw [exec_store,h19,h9,interp_store_ram (B := B) (img := img) (w := .w) o
    (Memory.word_aligned obj 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide)),hp];rfl

def flagWord (remaining len : Nat) : Word := if len ≤ remaining then 0#32 else 1#32

theorem flag (B : Board) (c : Core) (ram : Word → BitVec 8) (remaining len : Nat)
    (hp : c.pc = 0x800023b8#32) (h18 : c.get 18 = BitVec.ofNat 32 remaining) (h8 : c.get 8 = BitVec.ofNat 32 len)
    (hr : remaining < 2^32) (hl : len < 2^32) :
    DetStep B img ⟨c,ram⟩ ⟨c.wr 10 (flagWord remaining len) 0x800023bc#32,ram⟩ := by
  refine detStep_of (by rw [hp];decide) (by rw [hp];exact ch2147492792) fun o => ?_
  rw [exec_op,h18,h8,hp]
  have hg : (BitVec.ofNat 32 remaining).ult (BitVec.ofNat 32 len) = decide (remaining < len) :=
    ParamMath.ult remaining len hr hl
  change interp B img o (.done (c.wr 10 (if (BitVec.ofNat 32 remaining).ult (BitVec.ofNat 32 len) then 1 else 0) 0x800023bc#32)) ram 0 [] = _
  rw [hg]
  by_cases hf : len ≤ remaining
  · rw [decide_eq_false (show ¬remaining < len by omega)]
    simp only [Bool.false_eq_true,ite_false,flagWord,ite_eq_left hf];rfl
  · rw [decide_eq_true (show remaining < len by omega)]
    simp only [ite_true,flagWord,ite_eq_right hf];rfl

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (remaining len : Nat)
    (hp : c.pc = 0x800023b8#32) (h18 : c.get 18 = BitVec.ofNat 32 remaining) (h8 : c.get 8 = BitVec.ofNat 32 len)
    (hr : remaining < 2^32) (hl : len < 2^32) (hm : Memory.Block B (c.get 2) 32) (ha : (c.get 2).toNat%4 = 0) :
    ∃ d, DetSteps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = ramRead ram (c.get 2+28#32) .w &&& ~~~1 ∧
      d.get 2 = c.get 2+32#32 ∧ d.get 10 = flagWord remaining len ∧ CursorRestore.Restored c d ram ∧ d.sameCsr c ∧ HighFrame.Frame c d := by
  let a := c.wr 10 (flagWord remaining len) 0x800023bc#32
  have ta : DetStep B img ⟨c,ram⟩ ⟨a,ram⟩ := flag B c ram remaining len hp h18 h8 hr hl
  have asp : a.get 2 = c.get 2 := Core.wr_get_ne _ _ _ _ _ (by decide)
  obtain ⟨d,td,dpc,dsp,dsaved,d10,dcsr,dhigh⟩ := CharRestore.contract_full B a ram rfl (by simpa only [asp] using hm) (by simpa only [asp] using ha)
  refine ⟨d,.step ta td,by simpa only [asp] using dpc,by simpa only [asp] using dsp,?_,?_,dcsr.trans (by rfl),?_⟩
  · exact d10.trans (Core.wr_get_self _ _ _ _ (by decide))
  · constructor
    · simpa only [asp] using dsaved.x1
    · simpa only [asp] using dsaved.x8
    · simpa only [asp] using dsaved.x9
    · simpa only [asp] using dsaved.x18
    · simpa only [asp] using dsaved.x19
  · intro r hr
    exact (dhigh r hr).trans (Core.wr_get_ne _ _ _ _ _ (HighFrame.ne r 10 hr (by decide)))
end E5R.Thermostat.CharFinish
