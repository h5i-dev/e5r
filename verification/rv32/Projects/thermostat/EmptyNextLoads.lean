import Projects.thermostat.SuccessNextCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.EmptyNextLoads
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp high0 high1 high2 low : Word) (h2 : c.get 2=sp) (h8 : c.get 8=sp+3204#32)
(hpad : ramRead ram (sp+3324#32) .w=0#32) (hlow : extend .h false (ramRead ram (sp+3328#32) .h)=low)
(half0 : extend .h false (ramRead ram (sp+4532#32) .h)=high0)
(half1 : extend .h false (ramRead ram (sp+4530#32) .h)=high1)
(half2 : extend .h true (ramRead ram (sp+4534#32) .h)=high2)
(stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
    (hp : c.pc=0x80000fc0#32) :
    ∃ d, Quiet.Steps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000fde#32 ∧
      d.get 18=0#32 ∧ d.get 27=low ∧ d.get 10=high0 ∧ d.get 12=high2 ∧ d.get 11=high1 ∧ (∀ r : Reg, r≠18 → r≠27 → r≠10 → r≠12 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 18 (0#32) 0x80000fc4#32
  let c2 := c1.wr 27 (low) 0x80000fc8#32
  let c3 := c2.wr 10 (4096#32) 0x80000fca#32
  let c4 := c3.wr 10 (4530#32) 0x80000fce#32
  let c5 := c4.wr 12 (sp+4530#32) 0x80000fd2#32
  let c6 := c5.wr 10 (high0) 0x80000fd6#32
  let c7 := c6.wr 11 (high1) 0x80000fda#32
  let c8 := c7.wr 12 (high2) 0x80000fde#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact xn2147487680) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=sp+3204#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h8]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+120#32=3324#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 831 aligned) (Memory.block_access stack (off := 3324) (by decide) (by decide)),hpad];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000fc4#32).getLsbD 0=false;decide) xn2147487684 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=sp+3204#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h8]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+124#32=3328#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 1664 (by omega)) (Memory.block_access stack (off := 3328) (by decide) (by decide)),hlow];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000fc8#32).getLsbD 0=false;decide) xn2147487688 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000fca#32).getLsbD 0=false;decide) xn2147487690 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v10 : c3.get 10=4096#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80000fce#32).getLsbD 0=false;decide) xn2147487694 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v2 : c4.get 2=sp := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
    have v10 : c4.get 10=4530#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
    rw [exec_op,v2,v10];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80000fd2#32).getLsbD 0=false;decide) xn2147487698 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v12 : c5.get 12=sp+4530#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
    rw [exec_load,v12,BitVec.add_assoc,show 4530#32+2#32=4532#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 2266 (by omega)) (Memory.block_access stack (off := 4532) (by decide) (by decide)),half0];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80000fd6#32).getLsbD 0=false;decide) xn2147487702 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v12 : c6.get 12=sp+4530#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
    rw [exec_load,v12,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 2265 (by omega)) (Memory.block_access stack (off := 4530) (by decide) (by decide)),half1];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80000fda#32).getLsbD 0=false;decide) xn2147487706 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v12 : c7.get 12=sp+4530#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
    rw [exec_load,v12,BitVec.add_assoc,show 4530#32+4#32=4534#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 2267 (by omega)) (Memory.block_access stack (off := 4534) (by decide) (by decide)),half2];first | rfl | (rw [hp];rfl)
  refine ⟨c8,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.single t7))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
  · intro reg h18 h27 h10 h12 h11;simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h27,h10,h12,h11]
end E5R.Thermostat.EmptyNextLoads
