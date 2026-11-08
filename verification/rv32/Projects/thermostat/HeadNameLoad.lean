import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadNameLoad
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf count : Word) (byte : BitVec 8) (h20 : c.get 20=buf) (h14 : c.get 14=count) (hm : B.inRam (buf+count) 1=true) (hbyte : ram (buf+count)=byte)
    (hp : c.pc=0x80002ff0#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002ff8#32 ∧
      d.get 30=BitVec.ofNat 32 byte.toNat ∧ (∀ r : Reg, r≠30 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 30 (buf+count) 0x80002ff4#32
  let c2 := c1.wr 30 (BitVec.ofNat 32 byte.toNat) 0x80002ff8#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495920) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_op,h20,h14];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ff4#32).getLsbD 0=false;decide) hh2147495924 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v30 : c1.get 30=buf+count := by simp [c1,Core.wr_get_ne,Core.wr_get,h20,h14]
    rw [exec_load,v30,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hm,Memory.load_byte,hbyte];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h20,h14]
  · intro reg h30;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h20,h14,h30]
end E5R.Thermostat.HeadNameLoad
