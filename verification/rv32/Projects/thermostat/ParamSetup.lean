import Projects.thermostat.ParamCode
import Projects.thermostat.ParamInput
import Projects.thermostat.Usize
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ParamSetup
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (req pathPtr : Word)
    (path : List (BitVec 8)) (s e count : Nat) (h : ParamInput.Capture B ram req pathPtr path s e count)
    (hlen : 1 ≤ e-s ∧ e-s ≤ 10) (hp : c.pc = 0x800027c2#32)
    (h10 : c.get 10 = req) (h11 : c.get 11 = BitVec.ofNat 32 e)
    (h14 : c.get 14 = BitVec.ofNat 32 s) :
    ∃ d, DetSteps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800027d8#32 ∧
      d.get 11 = 0#32 ∧ d.get 13 = 0#32 ∧ d.get 10 = 10#32 ∧ d.get 14 = pathPtr+BitVec.ofNat 32 s ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 13 → r ≠ 14 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x800027cc#32
  let c2 := c1.wr 11 0#32 0x800027ce#32
  let c3 := c2.wr 13 0#32 0x800027d0#32
  let c4 := c3.wr 10 pathPtr 0x800027d4#32
  let c5 := c4.wr 14 (pathPtr+BitVec.ofNat 32 s) 0x800027d6#32
  let d := c5.wr 10 10#32 0x800027d8#32
  have hpath : path.length < 2^32 := h.bytes.length
  have he : e < 2^32 := by have := h.bounded;omega
  have hs : s < 2^32 := by have := h.ordered;omega
  have hne : e ≠ s := by omega
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact pm2147493826) fun o => ?_
    rw [exec_branch,h11,h14,Usize.ne e s he hs]
    simp only [decide_eq_true hne,ite_true]
    change interp B img o (jump c (c.pc+10#32)) ram 0 [] = _
    rw [hp,show 0x800027c2#32+10#32 = 0x800027cc#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x800027cc#32).getLsbD 0 = false;decide) pm2147493836 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x800027ce#32).getLsbD 0 = false;decide) pm2147493838 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x800027d0#32).getLsbD 0 = false;decide) pm2147493840 fun o => ?_
    have hv : c3.get 10 = req := by simp [c3,c2,c1,Core.wr_get_ne,h10]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned req 76 h.aligned) (Memory.block_access h.object (off := 304) (by decide) (by decide)),h.path_pointer];rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x800027d4#32).getLsbD 0 = false;decide) pm2147493844 fun o => ?_
    have hv14 : c4.get 14 = BitVec.ofNat 32 s := by simp [c4,c3,c2,c1,Core.wr_get_ne,h14]
    have hv10 : c4.get 10 = pathPtr := by simp [c4,Core.wr_get]
    rw [exec_op,hv14,hv10]
    simp only [alu,BitVec.add_comm (BitVec.ofNat 32 s) pathPtr];rfl
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x800027d6#32).getLsbD 0 = false;decide) pm2147493846 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5))))),rfl,?_,?_,?_,?_,?_,by rfl⟩
  · simp [d,c5,c4,c3,c2,Core.wr_get_ne,Core.wr_get]
  · simp [d,c5,c4,c3,Core.wr_get_ne,Core.wr_get]
  · simp [d,Core.wr_get]
  · simp [d,c5,Core.wr_get_ne,Core.wr_get]
  · intro r h1 h2 h3 h4;simp [d,c5,c4,c3,c2,c1,Core.wr_get_ne,h1,h2,h3,h4]
end E5R.Thermostat.ParamSetup
