import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadTargetLoad
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (m offset length base : Word) (byte : BitVec 8) (h17 : c.get 17=m) (h30 : c.get 30=offset) (h12 : c.get 12=length) (h28 : c.get 28=base)
(ht : taken .geu (m+offset+1#32) length=false)
(hm : B.inRam (base+offset+1#32) 1=true) (hbyte : ram (base+offset+1#32)=byte)
    (hp : c.pc=0x80002dd8#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002df0#32 ∧
      d.get 7=m+offset ∧ d.get 18=m+offset+1#32 ∧ d.get 6=base+offset ∧ d.get 20=BitVec.ofNat 32 byte.toNat ∧ d.get 21=BitVec.ofNat 32 byte.toNat+0xffffffdf#32 ∧ (∀ r : Reg, r≠7 → r≠18 → r≠6 → r≠20 → r≠21 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 7 (m+offset) 0x80002ddc#32
  let c2 := c1.wr 18 (m+offset+1#32) 0x80002de0#32
  let c3 := c2.goto 0x80002de4#32
  let c4 := c3.wr 6 (base+offset) 0x80002de8#32
  let c5 := c4.wr 20 (BitVec.ofNat 32 byte.toNat) 0x80002dec#32
  let c6 := c5.wr 21 (BitVec.ofNat 32 byte.toNat+0xffffffdf#32) 0x80002df0#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495384) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_op,h17,h30];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ddc#32).getLsbD 0=false;decide) hh2147495388 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v7 : c1.get 7=m+offset := by simp [c1,Core.wr_get_ne,Core.wr_get,h17,h30,h12,h28]
    rw [exec_opimm,v7];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80002de0#32).getLsbD 0=false;decide) hh2147495392 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v18 : c2.get 18=m+offset+1#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h17,h30,h12,h28]
    have v12 : c2.get 12=length := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h17,h30,h12,h28]
    rw [exec_branch,v18,v12,ht];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80002de4#32).getLsbD 0=false;decide) hh2147495396 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v28 : c3.get 28=base := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h30,h12,h28]
    have v30 : c3.get 30=offset := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h30,h12,h28]
    rw [exec_op,v28,v30];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80002de8#32).getLsbD 0=false;decide) hh2147495400 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v6 : c4.get 6=base+offset := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h30,h12,h28]
    rw [exec_load,v6,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hm,
    Memory.load_byte,hbyte];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80002dec#32).getLsbD 0=false;decide) hh2147495404 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v20 : c5.get 20=BitVec.ofNat 32 byte.toNat := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h30,h12,h28]
    rw [exec_opimm,v20];first | rfl | (rw [hp];rfl)
  refine ⟨c6,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h30,h12,h28]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h30,h12,h28]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h30,h12,h28]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h30,h12,h28]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h30,h12,h28]
  · intro reg h7 h18 h6 h20 h21;simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h30,h12,h28,h7,h18,h6,h20,h21]
end E5R.Thermostat.HeadTargetLoad
