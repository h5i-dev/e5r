-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CursorFinish
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.CursorFinish
theorem store_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (obj : Word) (next : Nat)
    (hp : c.pc = 0x800022d8#32) (h19 : c.get 19 = obj) (h9 : c.get 9 = BitVec.ofNat 32 next)
    (hm : Memory.Block B obj 12) (ha : obj.toNat%4 = 0) :
    Quiet.Step B img ⟨c,ram⟩ ⟨c.goto 0x800022dc#32,ramWrite ram (obj+8#32) (BitVec.ofNat 32 next) .w⟩ := by
  refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact cu2147492568) fun o => ?_
  rw [exec_store,h19,h9,interp_store_ram (B := B) (img := img) (w := .w) o
    (Memory.word_aligned obj 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide)),hp];rfl

end E5R.Thermostat.CursorFinish
namespace E5R.Thermostat.CursorFinish
theorem flag_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (remaining len : Nat)
    (hp : c.pc = 0x800022dc#32) (h18 : c.get 18 = BitVec.ofNat 32 remaining) (h8 : c.get 8 = BitVec.ofNat 32 len)
    (hr : remaining < 2^32) (hl : len < 2^32) :
    Quiet.Step B img ⟨c,ram⟩ ⟨c.wr 10 (flagWord remaining len) 0x800022e0#32,ram⟩ := by
  refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact cu2147492572) fun o => ?_
  rw [exec_op,h18,h8,hp]
  have hg : (BitVec.ofNat 32 remaining).ult (BitVec.ofNat 32 len) = decide (remaining < len) :=
    ParamMath.ult remaining len hr hl
  change interp B img o (.done (c.wr 10 (if (BitVec.ofNat 32 remaining).ult (BitVec.ofNat 32 len) then 1 else 0) 0x800022e0#32)) ram 0 [] = _
  rw [hg]
  by_cases hf : len ≤ remaining
  · rw [decide_eq_false (show ¬remaining < len by omega)]
    simp only [Bool.false_eq_true,ite_false,flagWord,ite_eq_left hf];rfl
  · rw [decide_eq_true (show remaining < len by omega)]
    simp only [ite_true,flagWord,ite_eq_right hf];rfl

end E5R.Thermostat.CursorFinish
