import Projects.thermostat.DecodeCode
import Projects.thermostat.PackedBytes
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.CommandPack
open E5R E5R.Thermostat

def execute (c : Core) : Core :=
  let c1 := c.wr 11 (c.get 11 <<< 16) 0x8000220e#32
  let c2 := c1.wr 10 (c.get 10 ||| c.get 12) 0x80002210#32
  c2.wr 10 ((c.get 10 ||| c.get 12) ||| (c.get 11 <<< 16)) 0x80002212#32

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (hp : c.pc = 0x8000220c#32) :
    DetSteps B img 3 ⟨c,ram⟩ ⟨execute c,ram⟩ := by
  let c1 := c.wr 11 (c.get 11 <<< 16) 0x8000220e#32
  let c2 := c1.wr 10 (c.get 10 ||| c.get 12) 0x80002210#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wd2147492364) fun o => ?_
    rw [exec_opimm,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x8000220e#32).getLsbD 0 = false;decide) wd2147492366 fun o => ?_
    have h10 : c1.get 10 = c.get 10 := by simp [c1,Core.wr_get_ne]
    have h12 : c1.get 12 = c.get 12 := by simp [c1,Core.wr_get_ne]
    rw [exec_op,h10,h12];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨execute c,ram⟩ := by
    refine detStep_of (by change (0x80002210#32).getLsbD 0 = false;decide) wd2147492368 fun o => ?_
    have h10 : c2.get 10 = c.get 10 ||| c.get 12 := by simp [c2,Core.wr_get]
    have h11 : c2.get 11 = c.get 11 <<< 16 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_op,h10,h11];rfl
  exact .step s0 (.step s1 (.single s2))

theorem fields (c : Core) : (execute c).pc = 0x80002212#32 ∧
    (execute c).get 10 = (c.get 10 ||| c.get 12) ||| (c.get 11 <<< 16) ∧
    (∀ r : Reg, r ≠ 10 → r ≠ 11 → (execute c).get r = c.get r) ∧ (execute c).sameCsr c := by
  refine ⟨rfl,?_,?_,by rfl⟩
  · simp [execute,Core.wr_get]
  · intro r h1 h2;simp [execute,Core.wr_get_ne,h1,h2]

theorem numeric (c : Core) (report : Bool)
    (htag : c.get 10 = if report then 1#32 else 0#32) (hpad : c.get 12 = 0#32) :
    WireSpec.CommandWord ((execute c).get 10)
      (if report then .reportTemp ((c.get 11).setWidth 16) else .setpoint ((c.get 11).setWidth 16)) := by
  rw [(fields c).2.1,htag,hpad,BitVec.or_zero]
  exact PackedBytes.numeric report (c.get 11)

theorem error400 (c : Core) (htag : c.get 10 = 255#32) (hpad : c.get 12 = 0#32) (hstatus : c.get 11 = 400#32) :
    WireSpec.ResultWord ((execute c).get 10) (.error 400) := by
  rw [(fields c).2.1,htag,hpad,hstatus]
  unfold WireSpec.ResultWord
  decide +kernel
end E5R.Thermostat.CommandPack
