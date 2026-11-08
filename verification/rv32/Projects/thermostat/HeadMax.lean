import Projects.thermostat.HttpParseCode00
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadMax
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (limits length : Word) (h13 : c.get 13=limits) (h12 : c.get 12=length)
(hm : B.inRam limits 4=true) (ha : limits.toNat%4=0)
(hmax : ramRead ram limits .w=1024#32)
    (hp : c.pc=0x80002c7c#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002c82#32 ∧
      d.get 16=1024#32 ∧ d.get 14=length ∧ (∀ r : Reg, r≠16 → r≠14 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 16 (1024#32) 0x80002c80#32
  let c2 := c1.wr 14 (length) 0x80002c82#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495036) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h13,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o ha hm,hmax,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002c80#32).getLsbD 0=false;decide) hh2147495040 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v12 : c1.get 12=length := by simp [c1,Core.wr_get_ne,Core.wr_get,h13,h12]
    rw [exec_op,Core.get_zero,v12,(show alu .add (0 : Word) length=length from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h13,h12]
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h13,h12]
  · intro reg h16 h14;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h13,h12,h16,h14]
end E5R.Thermostat.HeadMax
