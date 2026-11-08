import Projects.thermostat.WriteErrorCode
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.WriteErrorCall
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp dst cap : Word) (hs : c.get 2=sp) (h19 : c.get 19=dst) (h18 : c.get 18=cap)
    (hp : c.pc = 0x80000656#32) :
    ∃ d, DetSteps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80001e4a#32 ∧
      d.get 10 = sp+24#32 ∧ d.get 11 = dst ∧ d.get 12 = cap ∧ d.get 1 = 0x80000664#32 ∧ (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 1 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (sp+24#32) 0x80000658#32
  let c2 := c1.wr 11 (dst) 0x8000065a#32
  let c3 := c2.wr 12 (cap) 0x8000065c#32
  let c4 := c3.wr 1 (0x8000165c#32) 0x80000660#32
  let c5 := c4.wr 1 (0x80000664#32) 0x80001e4a#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact er2147485270) fun o => ?_
    rw [exec_opimm,hs,hp];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80000658#32).getLsbD 0 = false;decide) er2147485272 fun o => ?_
    have hv : c1.get 19=dst := by simp [c1,Core.wr_get_ne,Core.wr_get,hs,h19,h18]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x8000065a#32).getLsbD 0 = false;decide) er2147485274 fun o => ?_
    have hv : c2.get 18=cap := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,hs,h19,h18]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x8000065c#32).getLsbD 0 = false;decide) er2147485276 fun o => ?_
    rw [exec_auipc];first | rfl | (rw [hp]; rfl)
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80000660#32).getLsbD 0 = false;decide) er2147485280 fun o => ?_
    have hv : c4.get 1=0x8000165c#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h19,h18]
    rw [exec_jalr,hv]
    change interp B img o (.done ((c4.set 1 0x80000664#32).goto 0x80001e4a#32)) ram 0 [] = _
    first | rfl | (rw [hp]; rfl)
  refine ⟨c5,.step s0 (.step s1 (.step s2 (.step s3 (.single s4)))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h19,h18]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h19,h18]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h19,h18]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h19,h18]
  · intro r h10 h11 h12 h1
    simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h19,h18,h10,h11,h12,h1]
end E5R.Thermostat.WriteErrorCall
