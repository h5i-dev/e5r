import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadFieldsScanLoad
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (relative count cursor start : Word) (byte : BitVec 8) (h13 : c.get 13=relative) (h21 : c.get 21=count) (h14 : c.get 14=cursor) (h24 : c.get 24=start)
(ht : taken .eq (relative+count) (0 : Word)=false)
(hm : B.inRam (cursor+start) 1=true) (hbyte : ram (cursor+start)=byte)
    (hp : c.pc=0x80002f6e#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002f7e#32 ∧
      d.get 15=cursor+start ∧ d.get 30=BitVec.ofNat 32 byte.toNat ∧ (∀ r : Reg, r≠15 → r≠30 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 15 (relative+count) 0x80002f72#32
  let c2 := c1.goto 0x80002f76#32
  let c3 := c2.wr 15 (cursor+start) 0x80002f7a#32
  let c4 := c3.wr 30 (BitVec.ofNat 32 byte.toNat) 0x80002f7e#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495790) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_op,h13,h21];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f72#32).getLsbD 0=false;decide) hh2147495794 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v15 : c1.get 15=relative+count := by simp [c1,Core.wr_get_ne,Core.wr_get,h13,h21,h14,h24]
    rw [exec_branch,v15,Core.get_zero,ht];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f76#32).getLsbD 0=false;decide) hh2147495798 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v14 : c2.get 14=cursor := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h13,h21,h14,h24]
    have v24 : c2.get 24=start := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h13,h21,h14,h24]
    rw [exec_op,v14,v24];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f7a#32).getLsbD 0=false;decide) hh2147495802 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v15 : c3.get 15=cursor+start := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h21,h14,h24]
    rw [exec_load,v15,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hm,Memory.load_byte,hbyte];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h21,h14,h24]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h21,h14,h24]
  · intro reg h15 h30;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h21,h14,h24,h15,h30]
end E5R.Thermostat.HeadFieldsScanLoad
