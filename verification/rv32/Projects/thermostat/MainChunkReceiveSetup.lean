import Projects.thermostat.MainChunkReceiveCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainChunkReceiveSetup
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp filled io : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+3664#32) (io) .w) (sp+3668#32) (filled+(sp+132#32)) .w) (sp+3672#32) (2048#32-filled) .w) (sp+3676#32) (0#32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp filled io : Word) (h8 : c.get 8=sp+3204#32) (h10 : c.get 10=filled)
(hm : Memory.Block B sp 4928) (ha : sp.toNat%4=0)
(hcap : ramRead ram (sp+3316#32) .w=2048#32)
(hrx : ramRead ram (sp+3312#32) .w=sp+132#32)
(hio : ramRead ram (sp+3644#32) .w=io) (hbound : filled.toNat<2048)
    (hp : c.pc=0x80000f8c#32) :
    ∃ d, Quiet.Steps B img 11 ⟨c,ram⟩ ⟨d,memory ram sp filled io⟩ ∧ d.pc=0x80000fb0#32 ∧
      d.get 11=2048#32-filled ∧ d.get 12=sp+132#32 ∧ d.get 13=io ∧ d.get 10=filled+(sp+132#32) ∧ (∀ r : Reg, r≠11 → r≠12 → r≠13 → r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (2048#32) 0x80000f8e#32
  let c2 := c1.goto 0x80000f92#32
  let c3 := c2.goto 0x80000f96#32
  let c4 := c3.wr 12 (sp+132#32) 0x80000f98#32
  let c5 := c4.wr 13 (io) 0x80000f9c#32
  let c6 := c5.wr 11 (2048#32-filled) 0x80000f9e#32
  let c7 := c6.wr 10 (filled+(sp+132#32)) 0x80000fa0#32
  let r1 := ramWrite ram (sp+3664#32) (io) .w
  let c8 := c7.goto 0x80000fa4#32
  let r2 := ramWrite r1 (sp+3668#32) (filled+(sp+132#32)) .w
  let c9 := c8.goto 0x80000fa8#32
  let r3 := ramWrite r2 (sp+3672#32) (2048#32-filled) .w
  let c10 := c9.goto 0x80000fac#32
  let r4 := ramWrite r3 (sp+3676#32) (0#32) .b
  let c11 := c10.goto 0x80000fb0#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact cr2147487628) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=sp+3204#32 := by simp [Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+112#32=3316#32 by decide +kernel,
    Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 829 ha)
    (Memory.block_access hm (off := 3316) (by decide) (by decide)),hcap];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f8e#32).getLsbD 0=false;decide) cr2147487630 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v11 : c1.get 11=2048#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    have v10 : c1.get 10=filled := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    have ht : taken .eq 2048#32 filled=false := by
     change decide (2048#32=filled)=false
     apply decide_eq_false
     intro he
     have hn := congrArg BitVec.toNat he
     change 2048=filled.toNat at hn;omega
    rw [exec_branch,v11,v10,ht];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f92#32).getLsbD 0=false;decide) cr2147487634 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v11 : c2.get 11=2048#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    have v10 : c2.get 10=filled := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    have ht : taken .ltu 2048#32 filled=false := by simp [taken,BitVec.ult,show ¬2048<filled.toNat by omega]
    rw [exec_branch,v11,v10,ht];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f96#32).getLsbD 0=false;decide) cr2147487638 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v8 : c3.get 8=sp+3204#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+108#32=3312#32 by decide +kernel,
    Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 828 ha)
    (Memory.block_access hm (off := 3312) (by decide) (by decide)),hrx];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f98#32).getLsbD 0=false;decide) cr2147487640 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v8 : c4.get 8=sp+3204#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+440#32=3644#32 by decide +kernel,
    Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 911 ha)
    (Memory.block_access hm (off := 3644) (by decide) (by decide)),hio];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f9c#32).getLsbD 0=false;decide) cr2147487644 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v11 : c5.get 11=2048#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    have v10 : c5.get 10=filled := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_op,v11,v10];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f9e#32).getLsbD 0=false;decide) cr2147487646 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v12 : c6.get 12=sp+132#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    have v10 : c6.get 10=filled := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_op,v12,v10];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,r1⟩ := by
    refine Quiet.step_of (by change (0x80000fa0#32).getLsbD 0=false;decide) cr2147487648 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 r1 [],[]⟩
    have v8 : c7.get 8=sp+3204#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    have vv : c7.get 13=io := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_store,v8,vv,BitVec.add_assoc,show 3204#32+460#32=3664#32 by decide +kernel,
    Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 916 ha)
    (Memory.block_access hm (off := 3664) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r1⟩ ⟨c9,r2⟩ := by
    refine Quiet.step_of (by change (0x80000fa4#32).getLsbD 0=false;decide) cr2147487652 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r1 0 [] [] = ⟨.ok c9 r2 [],[]⟩
    have v8 : c8.get 8=sp+3204#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    have vv : c8.get 10=filled+(sp+132#32) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_store,v8,vv,BitVec.add_assoc,show 3204#32+464#32=3668#32 by decide +kernel,
    Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 917 ha)
    (Memory.block_access hm (off := 3668) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r2⟩ ⟨c10,r3⟩ := by
    refine Quiet.step_of (by change (0x80000fa8#32).getLsbD 0=false;decide) cr2147487656 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r2 0 [] [] = ⟨.ok c10 r3 [],[]⟩
    have v8 : c9.get 8=sp+3204#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    have vv : c9.get 11=2048#32-filled := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_store,v8,vv,BitVec.add_assoc,show 3204#32+468#32=3672#32 by decide +kernel,
    Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 918 ha)
    (Memory.block_access hm (off := 3672) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r3⟩ ⟨c11,r4⟩ := by
    refine Quiet.step_of (by change (0x80000fac#32).getLsbD 0=false;decide) cr2147487660 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r3 0 [] [] = ⟨.ok c11 r4 [],[]⟩
    have v8 : c10.get 8=sp+3204#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_store,v8,Core.get_zero,BitVec.add_assoc,show 3204#32+472#32=3676#32 by decide +kernel,
    Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by change (sp+3676#32).toNat%1=0;omega)
    (Memory.block_access hm (off := 3676) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c11,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.single t10)))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
  · intro reg h11 h12 h13 h10;simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h12,h13,h10]
end E5R.Thermostat.MainChunkReceiveSetup
