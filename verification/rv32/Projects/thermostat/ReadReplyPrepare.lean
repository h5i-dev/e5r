import Projects.thermostat.ReadReplyCode
import Projects.thermostat.Memory
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ReadReplyPrepare
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp dst cap : Word) (hs : c.get 2=sp) (h24 : c.get 24=dst) (h20 : c.get 20=cap)
    (hp : c.pc = 0x80001b5e#32) :
    ∃ d, DetSteps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80001eb8#32 ∧
      d.get 10 = sp+4520#32 ∧ d.get 11 = dst ∧ d.get 12 = cap ∧ d.get 1 = 0x80001b72#32 ∧ (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 1 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (4096#32) 0x80001b60#32
  let c2 := c1.wr 10 (4520#32) 0x80001b64#32
  let c3 := c2.wr 10 (sp+4520#32) 0x80001b66#32
  let c4 := c3.wr 11 (dst) 0x80001b68#32
  let c5 := c4.wr 12 (cap) 0x80001b6a#32
  let c6 := c5.wr 1 (0x80001b6a#32) 0x80001b6e#32
  let c7 := c6.wr 1 (0x80001b72#32) 0x80001eb8#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact rr2147490654) fun o => ?_
    rw [exec_lui,hp];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80001b60#32).getLsbD 0 = false;decide) rr2147490656 fun o => ?_
    have hv : c1.get 10=4096#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,hs,h24,h20]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80001b64#32).getLsbD 0 = false;decide) rr2147490660 fun o => ?_
    have hv : c2.get 10=4520#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,hs,h24,h20]
    have hs : c2.get 2=sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,hs,h24,h20]
    rw [exec_op,hv,hs]
    change interp B img o (.done (c2.wr 10 (4520#32+sp) 0x80001b66#32)) ram 0 [] = _
    rw [show 4520#32+sp=sp+4520#32 from BitVec.add_comm _ _];first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80001b66#32).getLsbD 0 = false;decide) rr2147490662 fun o => ?_
    have hv : c3.get 24=dst := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h24,h20]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80001b68#32).getLsbD 0 = false;decide) rr2147490664 fun o => ?_
    have hv : c4.get 20=cap := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h24,h20]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x80001b6a#32).getLsbD 0 = false;decide) rr2147490666 fun o => ?_
    rw [exec_auipc];first | rfl | (rw [hp]; rfl)
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine detStep_of (by change (0x80001b6e#32).getLsbD 0 = false;decide) rr2147490670 fun o => ?_
    have hv : c6.get 1=0x80001b6a#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h24,h20]
    rw [exec_jalr,hv]
    change interp B img o (.done ((c6.set 1 0x80001b72#32).goto 0x80001eb8#32)) ram 0 [] = _
    first | rfl | (rw [hp]; rfl)
  refine ⟨c7,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.single s6)))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h24,h20]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h24,h20]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h24,h20]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h24,h20]
  · intro r h10 h11 h12 h1
    simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h24,h20,h10,h11,h12,h1]
end E5R.Thermostat.ReadReplyPrepare
