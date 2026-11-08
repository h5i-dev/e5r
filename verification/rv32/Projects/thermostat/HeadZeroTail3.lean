import Projects.thermostat.ZeroCode
import Projects.thermostat.WordZero
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadZeroTail3
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (e : Word) :=
  ramWrite (ramWrite (ramWrite (ram) (e) (0#32) .b) (e+1#32) (0#32) .b) (e+2#32) (0#32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (e : Word) (h11 : c.get 11=0#32) (h12 : c.get 12=271#32) (h13 : c.get 13=e)
(hm : Memory.Block B e 3) (htop : e.toNat+3<2^32)
    (hp : c.pc=0x8000567e#32) :
    ∃ d, Quiet.Steps B img 15 ⟨c,ram⟩ ⟨d,memory ram e⟩ ∧ d.pc=0x8000569e#32 ∧
      d.get 12=0#32 ∧ d.get 14=e+3#32 ∧ d.get 13=e+3#32 ∧ (∀ r : Reg, r≠12 → r≠14 → r≠13 → d.get r=c.get r) ∧ d.sameCsr c := by
  have compare : taken .ltu e (e+3#32)=true := by
    change decide (e.toNat<(e+3#32).toNat)=true
    rw [WordZero.add_nat e 3 htop]
    simp only [show e.toNat<e.toNat+3 by omega,decide_true]
  let c1 := c.wr 12 (3#32) 0x80005680#32
  let c2 := c1.wr 14 (e+3#32) 0x80005684#32
  let c3 := c2.goto 0x80005694#32
  let c4 := c3.wr 12 (2#32) 0x80005696#32
  let r1 := ramWrite ram (e) (0#32) .b
  let c5 := c4.goto 0x8000569a#32
  let c6 := c5.wr 13 (e+1#32) 0x8000569c#32
  let c7 := c6.goto 0x80005694#32
  let c8 := c7.wr 12 (1#32) 0x80005696#32
  let r2 := ramWrite r1 (e+1#32) (0#32) .b
  let c9 := c8.goto 0x8000569a#32
  let c10 := c9.wr 13 (e+2#32) 0x8000569c#32
  let c11 := c10.goto 0x80005694#32
  let c12 := c11.wr 12 (0#32) 0x80005696#32
  let r3 := ramWrite r2 (e+2#32) (0#32) .b
  let c13 := c12.goto 0x8000569a#32
  let c14 := c13.wr 13 (e+3#32) 0x8000569c#32
  let c15 := c14.goto 0x8000569e#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact ze2147505790) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h12,show alu .and 271#32 3#32=3#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80005680#32).getLsbD 0=false;decide) ze2147505792 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v13 : c1.get 13=e := by simp [c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
    have v12 : c1.get 12=3#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
    rw [exec_op,v13,v12];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80005684#32).getLsbD 0=false;decide) ze2147505796 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v13 : c2.get 13=e := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
    have v14 : c2.get 14=e+3#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
    rw [exec_branch,v13,v14,compare]
    simp only [ite_true]
    change Observed.interp B img o (jump c2 (0x80005684#32+0x10#32)) ram 0 [] [] = _
    rw [show 0x80005684#32+0x10#32=0x80005694#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80005694#32).getLsbD 0=false;decide) ze2147505812 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v12 : c3.get 12=3#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
    rw [exec_opimm,v12,show alu .add 3#32 0xffffffff#32=2#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,r1⟩ := by
    refine Quiet.step_of (by change (0x80005696#32).getLsbD 0=false;decide) ze2147505814 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 r1 [],[]⟩
    have v13 : c4.get 13=e := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
    have v11 : c4.get 11=0#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
    rw [exec_store,v13,v11,BitVec.add_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _)
      (by simpa only [BitVec.add_zero] using (Memory.block_access hm (off := 0) (by decide) (by decide)))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r1⟩ ⟨c6,r1⟩ := by
    refine Quiet.step_of (by change (0x8000569a#32).getLsbD 0=false;decide) ze2147505818 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r1 0 [] [] = ⟨.ok c6 r1 [],[]⟩
    have v13 : c5.get 13=e := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
    rw [exec_opimm,v13]
    rfl
  have t6 : Quiet.Step B img ⟨c6,r1⟩ ⟨c7,r1⟩ := by
    refine Quiet.step_of (by change (0x8000569c#32).getLsbD 0=false;decide) ze2147505820 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r1 0 [] [] = ⟨.ok c7 r1 [],[]⟩
    have v12 : c6.get 12=2#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
    rw [exec_branch,v12,Core.get_zero,show taken .ne 2#32 (0 : Word)=true by decide +kernel]
    simp only [ite_true]
    change Observed.interp B img o (jump c6 (0x8000569c#32+0xfffffff8#32)) r1 0 [] [] = _
    rw [show 0x8000569c#32+0xfffffff8#32=0x80005694#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r1⟩ ⟨c8,r1⟩ := by
    refine Quiet.step_of (by change (0x80005694#32).getLsbD 0=false;decide) ze2147505812 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r1 0 [] [] = ⟨.ok c8 r1 [],[]⟩
    have v12 : c7.get 12=2#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
    rw [exec_opimm,v12,show alu .add 2#32 0xffffffff#32=1#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r1⟩ ⟨c9,r2⟩ := by
    refine Quiet.step_of (by change (0x80005696#32).getLsbD 0=false;decide) ze2147505814 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r1 0 [] [] = ⟨.ok c9 r2 [],[]⟩
    have v13 : c8.get 13=e+1#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
    have v11 : c8.get 11=0#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
    rw [exec_store,v13,v11,BitVec.add_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _)
      (by simpa only [BitVec.add_zero] using (Memory.block_access hm (off := 1) (by decide) (by decide)))];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r2⟩ ⟨c10,r2⟩ := by
    refine Quiet.step_of (by change (0x8000569a#32).getLsbD 0=false;decide) ze2147505818 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r2 0 [] [] = ⟨.ok c10 r2 [],[]⟩
    have v13 : c9.get 13=e+1#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
    rw [exec_opimm,v13]
    change Observed.interp B img o (.done (c9.wr 13 ((e+1#32)+1#32) (c9.pc+2#32))) r2 0 [] [] = _
    rw [BitVec.add_assoc,show 1#32+1#32=2#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r2⟩ ⟨c11,r2⟩ := by
    refine Quiet.step_of (by change (0x8000569c#32).getLsbD 0=false;decide) ze2147505820 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r2 0 [] [] = ⟨.ok c11 r2 [],[]⟩
    have v12 : c10.get 12=1#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
    rw [exec_branch,v12,Core.get_zero,show taken .ne 1#32 (0 : Word)=true by decide +kernel]
    simp only [ite_true]
    change Observed.interp B img o (jump c10 (0x8000569c#32+0xfffffff8#32)) r2 0 [] [] = _
    rw [show 0x8000569c#32+0xfffffff8#32=0x80005694#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r2⟩ ⟨c12,r2⟩ := by
    refine Quiet.step_of (by change (0x80005694#32).getLsbD 0=false;decide) ze2147505812 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r2 0 [] [] = ⟨.ok c12 r2 [],[]⟩
    have v12 : c11.get 12=1#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
    rw [exec_opimm,v12,show alu .add 1#32 0xffffffff#32=0#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,r2⟩ ⟨c13,r3⟩ := by
    refine Quiet.step_of (by change (0x80005696#32).getLsbD 0=false;decide) ze2147505814 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r2 0 [] [] = ⟨.ok c13 r3 [],[]⟩
    have v13 : c12.get 13=e+2#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
    have v11 : c12.get 11=0#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
    rw [exec_store,v13,v11,BitVec.add_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _)
      (by simpa only [BitVec.add_zero] using (Memory.block_access hm (off := 2) (by decide) (by decide)))];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r3⟩ ⟨c14,r3⟩ := by
    refine Quiet.step_of (by change (0x8000569a#32).getLsbD 0=false;decide) ze2147505818 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r3 0 [] [] = ⟨.ok c14 r3 [],[]⟩
    have v13 : c13.get 13=e+2#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
    rw [exec_opimm,v13]
    change Observed.interp B img o (.done (c13.wr 13 ((e+2#32)+1#32) (c13.pc+2#32))) r3 0 [] [] = _
    rw [BitVec.add_assoc,show 2#32+1#32=3#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,r3⟩ ⟨c15,r3⟩ := by
    refine Quiet.step_of (by change (0x8000569c#32).getLsbD 0=false;decide) ze2147505820 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) r3 0 [] [] = ⟨.ok c15 r3 [],[]⟩
    have v12 : c14.get 12=0#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
    rw [exec_branch,v12,Core.get_zero,show taken .ne 0#32 (0 : Word)=false by decide +kernel]
    rfl
  refine ⟨c15,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.single t14)))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13]
  · intro reg h12 h14 h13;simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h12,h14,h13]
end E5R.Thermostat.HeadZeroTail3
