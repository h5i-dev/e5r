import Projects.thermostat.ReadShellCode
import Projects.thermostat.Wrapper
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ReadEntry
open E5R E5R.Thermostat

def setup (c : Core) : Core :=
  let c1 := c.wr 25 (c.get 9+4#32) 2147490326#32
  let c2 := c1.wr 10 (4096#32) 2147490328#32
  let c3 := c2.wr 10 (4520#32) 2147490332#32
  let c4 := c3.wr 10 (4520#32+c.get 2) 2147490334#32
  let c5 := c4.wr 11 (4096#32) 2147490336#32
  let c6 := c5.wr 11 (4824#32) 2147490340#32
  let c7 := c6.wr 11 (4824#32+c.get 2) 2147490342#32
  let c8 := c7.wr 13 (c.get 2+2047#32) 2147490346#32
  let c9 := c8.wr 13 (c.get 2+3968#32) 2147490350#32
  let c10 := c9.wr 12 (c.get 9+4#32) 2147490352#32
  let c11 := c10.wr 1 (0x80001a30#32) 2147490356#32
  c11.wr 1 (0x80001a38#32) 2147491366#32

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80001a12) : DetSteps B img 12 ⟨c,ram⟩ ⟨setup c,ram⟩ := by
  let c1 := c.wr 25 (c.get 9+4#32) 2147490326#32
  let c2 := c1.wr 10 (4096#32) 2147490328#32
  let c3 := c2.wr 10 (4520#32) 2147490332#32
  let c4 := c3.wr 10 (4520#32+c.get 2) 2147490334#32
  let c5 := c4.wr 11 (4096#32) 2147490336#32
  let c6 := c5.wr 11 (4824#32) 2147490340#32
  let c7 := c6.wr 11 (4824#32+c.get 2) 2147490342#32
  let c8 := c7.wr 13 (c.get 2+2047#32) 2147490346#32
  let c9 := c8.wr 13 (c.get 2+3968#32) 2147490350#32
  let c10 := c9.wr 12 (c.get 9+4#32) 2147490352#32
  let c11 := c10.wr 1 (0x80001a30#32) 2147490356#32
  let c12 := c11.wr 1 (0x80001a38#32) 2147491366#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact rs2147490322) fun o => ?_
    have hv : c.get 9 = (c.get 9) := by simp [Core.wr_get]
    rw [exec_opimm,hv]
    simp only [alu,BitVec.zero_add]
    rw [hp]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (2147490326#32).getLsbD 0 = false;decide) (rs2147490326) fun o => ?_
    rw [exec_lui]
    rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (2147490328#32).getLsbD 0 = false;decide) (rs2147490328) fun o => ?_
    have hv : c2.get 10 = (4096#32) := by simp [c1,c2,Core.wr_get]
    rw [exec_opimm,hv]
    simp only [alu,BitVec.zero_add]
    rw [show 4096#32+424#32 = 4520#32 by decide +kernel]
    rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (2147490332#32).getLsbD 0 = false;decide) (rs2147490332) fun o => ?_
    have ha : c3.get 10 = (4520#32) := by simp [c1,c2,c3,Core.wr_get]
    have hb : c3.get 2 = (c.get 2) := by simp [c1,c2,c3,Core.wr_get]
    rw [exec_op,ha,hb]
    simp only [alu,BitVec.zero_add]
    rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (2147490334#32).getLsbD 0 = false;decide) (rs2147490334) fun o => ?_
    rw [exec_lui]
    rfl
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (2147490336#32).getLsbD 0 = false;decide) (rs2147490336) fun o => ?_
    have hv : c5.get 11 = (4096#32) := by simp [c1,c2,c3,c4,c5,Core.wr_get]
    rw [exec_opimm,hv]
    simp only [alu,BitVec.zero_add]
    rw [show 4096#32+728#32 = 4824#32 by decide +kernel]
    rfl
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine detStep_of (by change (2147490340#32).getLsbD 0 = false;decide) (rs2147490340) fun o => ?_
    have ha : c6.get 11 = (4824#32) := by simp [c1,c2,c3,c4,c5,c6,Core.wr_get]
    have hb : c6.get 2 = (c.get 2) := by simp [c1,c2,c3,c4,c5,c6,Core.wr_get]
    rw [exec_op,ha,hb]
    simp only [alu,BitVec.zero_add]
    rfl
  have s7 : DetStep B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine detStep_of (by change (2147490342#32).getLsbD 0 = false;decide) (rs2147490342) fun o => ?_
    have hv : c7.get 2 = (c.get 2) := by simp [c1,c2,c3,c4,c5,c6,c7,Core.wr_get]
    rw [exec_opimm,hv]
    simp only [alu,BitVec.zero_add]
    rfl
  have s8 : DetStep B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine detStep_of (by change (2147490346#32).getLsbD 0 = false;decide) (rs2147490346) fun o => ?_
    have hv : c8.get 13 = (c.get 2+2047#32) := by simp [c1,c2,c3,c4,c5,c6,c7,c8,Core.wr_get]
    rw [exec_opimm,hv]
    simp only [alu,BitVec.zero_add]
    rw [BitVec.add_assoc]
    rw [show 2047#32+1921#32 = 3968#32 by decide +kernel]
    rfl
  have s9 : DetStep B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine detStep_of (by change (2147490350#32).getLsbD 0 = false;decide) (rs2147490350) fun o => ?_
    have ha : c9.get 0 = (0#32) := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,Core.wr_get]
    have hb : c9.get 25 = (c.get 9+4#32) := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,Core.wr_get]
    rw [exec_op,ha,hb]
    simp only [alu,BitVec.zero_add]
    rfl
  have s10 : DetStep B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine detStep_of (by change (2147490352#32).getLsbD 0 = false;decide) (rs2147490352) fun o => ?_
    rw [exec_auipc]
    simp only [BitVec.add_zero]
    rfl
  have s11 : DetStep B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine detStep_of (by change (2147490356#32).getLsbD 0 = false;decide) (rs2147490356) fun o => ?_
    have hv : c11.get 1 = 0x80001a30#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,Core.wr_get]
    rw [exec_jalr,hv]
    rw [show (0x80001a30#32+1014#32) &&& ~~~1 = 0x80001e26#32 by decide +kernel]
    rfl
  exact .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.single s11)))))))))))
end E5R.Thermostat.ReadEntry
