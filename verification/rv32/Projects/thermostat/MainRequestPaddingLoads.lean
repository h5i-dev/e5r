import Projects.thermostat.MainRequestBuildCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainRequestPaddingLoads
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp b0 b1 b2 b3 b4 b5 b6 : Word) (h8 : c.get 8=sp+3204#32) (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
(hbyte0 : extend .b false (ramRead ram (sp+4240#32) .b)=b0) (hbyte1 : extend .b false (ramRead ram (sp+4241#32) .b)=b1) (hbyte2 : extend .b false (ramRead ram (sp+4242#32) .b)=b2) (hbyte3 : extend .b false (ramRead ram (sp+4243#32) .b)=b3) (hbyte4 : extend .b false (ramRead ram (sp+4244#32) .b)=b4) (hbyte5 : extend .b false (ramRead ram (sp+4245#32) .b)=b5) (hbyte6 : extend .b false (ramRead ram (sp+4246#32) .b)=b6)
    (hp : c.pc=0x800011e2#32) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800011fe#32 ∧
      d.get 10=b0 ∧ d.get 11=b1 ∧ d.get 12=b2 ∧ d.get 13=b3 ∧ d.get 14=b4 ∧ d.get 15=b5 ∧ d.get 16=b6 ∧ (∀ r : Reg, r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → r≠15 → r≠16 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (b0) 0x800011e6#32
  let c2 := c1.wr 11 (b1) 0x800011ea#32
  let c3 := c2.wr 12 (b2) 0x800011ee#32
  let c4 := c3.wr 13 (b3) 0x800011f2#32
  let c5 := c4.wr 14 (b4) 0x800011f6#32
  let c6 := c5.wr 15 (b5) 0x800011fa#32
  let c7 := c6.wr 16 (b6) 0x800011fe#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147488226) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=sp+3204#32 := by simp [Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1036#32=4240#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 4240) (by decide) (by decide)),hbyte0];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800011e6#32).getLsbD 0=false;decide) re2147488230 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=sp+3204#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1037#32=4241#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 4241) (by decide) (by decide)),hbyte1];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800011ea#32).getLsbD 0=false;decide) re2147488234 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v8 : c2.get 8=sp+3204#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1038#32=4242#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 4242) (by decide) (by decide)),hbyte2];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800011ee#32).getLsbD 0=false;decide) re2147488238 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v8 : c3.get 8=sp+3204#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1039#32=4243#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 4243) (by decide) (by decide)),hbyte3];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800011f2#32).getLsbD 0=false;decide) re2147488242 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v8 : c4.get 8=sp+3204#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1040#32=4244#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 4244) (by decide) (by decide)),hbyte4];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800011f6#32).getLsbD 0=false;decide) re2147488246 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v8 : c5.get 8=sp+3204#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1041#32=4245#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 4245) (by decide) (by decide)),hbyte5];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x800011fa#32).getLsbD 0=false;decide) re2147488250 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v8 : c6.get 8=sp+3204#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1042#32=4246#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 4246) (by decide) (by decide)),hbyte6];first | rfl | (rw [hp];rfl)
  refine ⟨c7,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.single t6)))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · intro reg h10 h11 h12 h13 h14 h15 h16;simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h12,h13,h14,h15,h16]
end E5R.Thermostat.MainRequestPaddingLoads
