import Projects.thermostat.HttpParseCode00
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadScanLoad
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf index : Word) (b : BitVec 8) (h11 : c.get 11=buf) (h9 : c.get 9=index)
(hm : B.inRam (buf+index) 1=true) (hbyte : ram (buf+index)=b)
    (hp : c.pc=0x80002c90#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002c98#32 ∧
      d.get 5=buf+index ∧ d.get 6=BitVec.ofNat 32 b.toNat ∧ (∀ r : Reg, r≠5 → r≠6 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 5 (buf+index) 0x80002c94#32
  let c2 := c1.wr 6 (BitVec.ofNat 32 b.toNat) 0x80002c98#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495056) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_op,h11,h9,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002c94#32).getLsbD 0=false;decide) hh2147495060 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v5 : c1.get 5=buf+index := by simp [c1,Core.wr_get_ne,Core.wr_get,h11,h9]
    rw [exec_load,v5,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hm,
    Memory.load_byte,hbyte];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h9]
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h9]
  · intro reg h5 h6;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h9,h5,h6]
end E5R.Thermostat.HeadScanLoad
