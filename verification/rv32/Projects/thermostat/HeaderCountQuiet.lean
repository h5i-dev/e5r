-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.HeaderCount
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.HeaderCount
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (req : Word) (count : Nat)
    (hb : count ≤ 16) (hp : c.pc = 0x800026c0#32) (h10 : c.get 10 = req) (h12 : c.get 12 = 13#32)
    (hm : Memory.Block B req 336) (ha : req.toNat%4 = 0)
    (hcount : ramRead ram (req+288#32) .w = BitVec.ofNat 32 count) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if count = 0 then 0x8000274e#32 else 0x800026ce#32) ∧
      d.get 13 = 13#32 ∧ d.get 14 = BitVec.ofNat 32 count ∧
      (∀ r : Reg, r ≠ 12 → r ≠ 13 → r ≠ 14 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 13 13#32 0x800026c2#32
  let c2 := c1.wr 14 (BitVec.ofNat 32 count) 0x800026c6#32
  let c3 := c2.wr 12 17#32 0x800026c8#32
  let c4 := c3.goto 0x800026cc#32
  let d := c4.goto (if count = 0 then 0x8000274e#32 else 0x800026ce#32)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact hd2147493568) fun o => ?_
    rw [exec_op,Core.get_zero,h12,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x800026c2#32).getLsbD 0 = false;decide) hd2147493570 fun o => ?_
    have hv : c1.get 10 = req := by simp [c1,Core.wr_get_ne,h10]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned req 72 ha)
      (Memory.block_access hm (off := 288) (by decide) (by decide)),hcount];rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x800026c6#32).getLsbD 0 = false;decide) hd2147493574 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x800026c8#32).getLsbD 0 = false;decide) hd2147493576 fun o => ?_
    have v14 : c3.get 14 = BitVec.ofNat 32 count := by simp [c3,c2,Core.wr_get_ne,Core.wr_get]
    have v12 : c3.get 12 = 17#32 := by simp [c3,Core.wr_get]
    rw [exec_branch,v14,v12]
    have ht : taken .geu (BitVec.ofNat 32 count) 17#32 = false := by
      change (!taken .ltu (BitVec.ofNat 32 count) (BitVec.ofNat 32 17)) = false
      rw [ParamMath.ult count 17 (by omega) (by decide),decide_eq_true (by omega)];rfl
    rw [ht];rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x800026cc#32).getLsbD 0 = false;decide) hd2147493580 fun o => ?_
    have v14 : c4.get 14 = BitVec.ofNat 32 count := by simp [c4,c3,c2,Core.wr_get_ne,Core.wr_get]
    rw [exec_branch,v14,Core.get_zero]
    change interp B img o (if taken .eq (BitVec.ofNat 32 count) (BitVec.ofNat 32 0) then _ else _) ram 0 [] = _
    rw [Usize.eq count 0 (by omega) (by decide)]
    by_cases he : count = 0
    · rw [decide_eq_true he];simp only [ite_true,d,ite_eq_left he]
      change interp B img o (jump c4 (0x800026cc#32+0x82#32)) ram 0 [] = _
      rw [show 0x800026cc#32+0x82#32 = 0x8000274e#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    · rw [decide_eq_false he];simp only [Bool.false_eq_true,ite_false,d,ite_eq_right he];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.single s4)))),rfl,?_,?_,?_,by rfl⟩
  · simp [d,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [d,c4,c3,c2,Core.wr_get_ne,Core.wr_get]
  · intro r h1 h2 h3;simp [d,c4,c3,c2,c1,Core.wr_get_ne,h1,h2,h3]

end E5R.Thermostat.HeaderCount
