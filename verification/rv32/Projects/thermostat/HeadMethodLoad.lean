import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadMethodLoad
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf index length : Word) (b : BitVec 8) (h12 : c.get 12=length) (h17 : c.get 17=index) (h11 : c.get 11=buf)
(hne : taken .eq length index=false) (hm : B.inRam (buf+index) 1=true) (hbyte : ram (buf+index)=b)
    (hp : c.pc=0x80002cfa#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002d06#32 ∧
      d.get 28=buf+index ∧ d.get 19=BitVec.ofNat 32 b.toNat ∧ (∀ r : Reg, r≠28 → r≠19 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80002cfe#32
  let c2 := c1.wr 28 (buf+index) 0x80002d02#32
  let c3 := c2.wr 19 (BitVec.ofNat 32 b.toNat) 0x80002d06#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495162) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_branch,h12,h17,hne,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002cfe#32).getLsbD 0=false;decide) hh2147495166 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v11 : c1.get 11=buf := by simp [c1,Core.wr_get_ne,Core.wr_get,h12,h17,h11]
    have v17 : c1.get 17=index := by simp [c1,Core.wr_get_ne,Core.wr_get,h12,h17,h11]
    rw [exec_op,v11,v17];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80002d02#32).getLsbD 0=false;decide) hh2147495170 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v28 : c2.get 28=buf+index := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h12,h17,h11]
    rw [exec_load,v28,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hm,
    Memory.load_byte,hbyte];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h17,h11]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h17,h11]
  · intro reg h28 h19;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h17,h11,h28,h19]
end E5R.Thermostat.HeadMethodLoad
