import Projects.thermostat.MainNextLengthWords
import Projects.thermostat.MainNextCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainNextLengthLoads
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (amount : Nat) (h2 : c.get 2=sp) (h8 : c.get 8=sp+3204#32)
(words : MainNextLengthWords.At ram sp amount) (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
    (hp : c.pc=0x80000c98#32) :
    ∃ d, Quiet.Steps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000cb6#32 ∧
      d.get 12=0#32 ∧ d.get 10=0#32 ∧ d.get 11=0#32 ∧ d.get 9=1#32 ∧ d.get 18=0#32 ∧ d.get 27=BitVec.ofNat 32 amount ∧ (∀ r : Reg, r≠12 → r≠10 → r≠11 → r≠9 → r≠18 → r≠27 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (sp+2047#32) 0x80000c9c#32
  let c2 := c1.wr 12 (sp+3330#32) 0x80000ca0#32
  let c3 := c2.wr 10 (0#32) 0x80000ca4#32
  let c4 := c3.wr 11 (0#32) 0x80000ca8#32
  let c5 := c4.wr 12 (0#32) 0x80000cac#32
  let c6 := c5.wr 9 (1#32) 0x80000cae#32
  let c7 := c6.wr 18 (0#32) 0x80000cb2#32
  let c8 := c7.wr 27 (BitVec.ofNat 32 amount) 0x80000cb6#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact nx2147486872) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h2];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000c9c#32).getLsbD 0=false;decide) nx2147486876 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v12 : c1.get 12=sp+2047#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h8]
    rw [exec_opimm,v12]
    change Observed.interp B img o (Eff.done (c1.wr 12 ((sp+2047#32)+1283#32) 0x80000ca0#32)) ram 0 [] []=_
    rw [BitVec.add_assoc,show 2047#32+1283#32=3330#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000ca0#32).getLsbD 0=false;decide) nx2147486880 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v12 : c2.get 12=sp+3330#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
    rw [exec_load,v12,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 1665 (by omega)) (Memory.block_access stack (off := 3330) (by decide) (by decide)),words.half0];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000ca4#32).getLsbD 0=false;decide) nx2147486884 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v12 : c3.get 12=sp+3330#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
    rw [exec_load,v12,BitVec.add_assoc,show 3330#32+2#32=3332#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 1666 (by omega)) (Memory.block_access stack (off := 3332) (by decide) (by decide)),words.half1];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80000ca8#32).getLsbD 0=false;decide) nx2147486888 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v12 : c4.get 12=sp+3330#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
    rw [exec_load,v12,BitVec.add_assoc,show 3330#32+4#32=3334#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 1667 (by omega)) (Memory.block_access stack (off := 3334) (by decide) (by decide)),words.half2];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80000cac#32).getLsbD 0=false;decide) nx2147486892 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v8 : c5.get 8=sp+3204#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+116#32=3320#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 830 aligned) (Memory.block_access stack (off := 3320) (by decide) (by decide)),words.tag];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80000cae#32).getLsbD 0=false;decide) nx2147486894 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v8 : c6.get 8=sp+3204#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+120#32=3324#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 831 aligned) (Memory.block_access stack (off := 3324) (by decide) (by decide)),words.padding];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80000cb2#32).getLsbD 0=false;decide) nx2147486898 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v8 : c7.get 8=sp+3204#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+124#32=3328#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 1664 (by omega)) (Memory.block_access stack (off := 3328) (by decide) (by decide)),words.low];first | rfl | (rw [hp];rfl)
  refine ⟨c8,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.single t7))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8]
  · intro reg h12 h10 h11 h9 h18 h27;simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h10,h11,h9,h18,h27]
end E5R.Thermostat.MainNextLengthLoads
