import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadValueLoad
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (ptr remaining : Word) (byte : BitVec 8) (h10 : c.get 10=ptr) (h31 : c.get 31=remaining)
(ht : taken .eq remaining (0 : Word)=false) (hm : B.inRam ptr 1=true) (hbyte : ram ptr=byte)
    (hp : c.pc=0x8000307c#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003086#32 ∧
      d.get 30=BitVec.ofNat 32 byte.toNat ∧ d.get 12=9#32 ∧ (∀ r : Reg, r≠30 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80003080#32
  let c2 := c1.wr 30 (BitVec.ofNat 32 byte.toNat) 0x80003084#32
  let c3 := c2.wr 12 (9#32) 0x80003086#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496060) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_branch,h31,Core.get_zero,ht];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003080#32).getLsbD 0=false;decide) hh2147496064 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v10 : c1.get 10=ptr := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h31]
    rw [exec_load,v10,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hm,Memory.load_byte,hbyte];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80003084#32).getLsbD 0=false;decide) hh2147496068 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h31]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h31]
  · intro reg h30 h12;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h31,h30,h12]
end E5R.Thermostat.HeadValueLoad
