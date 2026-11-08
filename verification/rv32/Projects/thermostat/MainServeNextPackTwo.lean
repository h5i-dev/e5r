import Projects.thermostat.MainServeNextCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainServeNextPackTwo
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp word half byte : Word) :=
  ramWrite (ramWrite (ramWrite (ram) (sp+4240#32) (word) .w) (sp+4244#32) (half) .h) (sp+4246#32) (byte) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp word half byte : Word) (h8 : c.get 8=sp+3204#32) (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
(h9 : c.get 9=1#32) (h18 : c.get 18=0#32)
(hword : ramRead ram (sp+3960#32) .w=word)
(hhalf : extend .h true (ramRead ram (sp+3964#32) .h)=half)
(hbyte : extend .b false (ramRead ram (sp+3966#32) .b)=byte)
    (hp : c.pc=0x80000b1a#32) :
    ∃ d, Quiet.Steps B img 13 ⟨c,ram⟩ ⟨d,memory ram sp word half byte⟩ ∧ d.pc=0x80000b4a#32 ∧
      d.get 11=word ∧ d.get 12=half ∧ d.get 13=byte ∧ d.get 10=0#32 ∧ d.get 14=0xffffffff#32 ∧ (∀ r : Reg, r≠11 → r≠12 → r≠13 → r≠10 → r≠14 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (word) 0x80000b1e#32
  let c2 := c1.wr 12 (half) 0x80000b22#32
  let c3 := c2.wr 13 (byte) 0x80000b26#32
  let c4 := c3.wr 10 (1#32) 0x80000b2a#32
  let c5 := c4.wr 14 (0#32) 0x80000b2e#32
  let c6 := c5.wr 10 (0#32) 0x80000b32#32
  let c7 := c6.wr 10 (0#32) 0x80000b34#32
  let c8 := c7.wr 14 (0xffffffff#32) 0x80000b38#32
  let c9 := c8.wr 10 (0#32) 0x80000b3c#32
  let c10 := c9.wr 10 (0#32) 0x80000b3e#32
  let r1 := ramWrite ram (sp+4240#32) (word) .w
  let c11 := c10.goto 0x80000b42#32
  let r2 := ramWrite r1 (sp+4244#32) (half) .h
  let c12 := c11.goto 0x80000b46#32
  let r3 := ramWrite r2 (sp+4246#32) (byte) .b
  let c13 := c12.goto 0x80000b4a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact sn2147486490) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=sp+3204#32 := by simp [Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+756#32=3960#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 990 aligned) (Memory.block_access stack (off := 3960) (by decide) (by decide)),hword];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000b1e#32).getLsbD 0=false;decide) sn2147486494 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=sp+3204#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+760#32=3964#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 1982 (by omega)) (Memory.block_access stack (off := 3964) (by decide) (by decide)),hhalf];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000b22#32).getLsbD 0=false;decide) sn2147486498 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v8 : c2.get 8=sp+3204#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+762#32=3966#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access stack (off := 3966) (by decide) (by decide)),hbyte];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000b26#32).getLsbD 0=false;decide) sn2147486502 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v9 : c3.get 9=1#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    rw [exec_opimm,v9];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80000b2a#32).getLsbD 0=false;decide) sn2147486506 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v18 : c4.get 18=0#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    rw [exec_op,Core.get_zero,v18];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80000b2e#32).getLsbD 0=false;decide) sn2147486510 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v10 : c5.get 10=1#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80000b32#32).getLsbD 0=false;decide) sn2147486514 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v10 : c6.get 10=0#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    have v14 : c6.get 14=0#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    rw [exec_op,v10,v14];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80000b34#32).getLsbD 0=false;decide) sn2147486516 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v9 : c7.get 9=1#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    rw [exec_opimm,v9];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80000b38#32).getLsbD 0=false;decide) sn2147486520 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v10 : c8.get 10=0#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    rw [exec_op,Core.get_zero,v10];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80000b3c#32).getLsbD 0=false;decide) sn2147486524 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v10 : c9.get 10=0#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    have v14 : c9.get 14=0xffffffff#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    rw [exec_op,v10,v14];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,r1⟩ := by
    refine Quiet.step_of (by change (0x80000b3e#32).getLsbD 0=false;decide) sn2147486526 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 r1 [],[]⟩
    have v8 : c10.get 8=sp+3204#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    have v11 : c10.get 11=word := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    rw [exec_store,v8,v11,BitVec.add_assoc,show 3204#32+1036#32=4240#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1060 aligned) (Memory.block_access stack (off := 4240) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r1⟩ ⟨c12,r2⟩ := by
    refine Quiet.step_of (by change (0x80000b42#32).getLsbD 0=false;decide) sn2147486530 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r1 0 [] [] = ⟨.ok c12 r2 [],[]⟩
    have v8 : c11.get 8=sp+3204#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    have v12 : c11.get 12=half := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    rw [exec_store,v8,v12,BitVec.add_assoc,show 3204#32+1040#32=4244#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 2122 (by omega)) (Memory.block_access stack (off := 4244) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,r2⟩ ⟨c13,r3⟩ := by
    refine Quiet.step_of (by change (0x80000b46#32).getLsbD 0=false;decide) sn2147486534 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r2 0 [] [] = ⟨.ok c13 r3 [],[]⟩
    have v8 : c12.get 8=sp+3204#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    have v13 : c12.get 13=byte := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    rw [exec_store,v8,v13,BitVec.add_assoc,show 3204#32+1042#32=4246#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access stack (off := 4246) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c13,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.single t12)))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
  · intro reg h11 h12 h13 h10 h14;simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18,h11,h12,h13,h10,h14]
end E5R.Thermostat.MainServeNextPackTwo
