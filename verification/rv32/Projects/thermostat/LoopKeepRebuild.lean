import Projects.thermostat.LoopKeepRebuildCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.LoopKeepRebuild
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (_used : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (0x80fff814#32+436#32) (0x80fff868#32) .w) (0x80fff814#32+440#32) (0x80ffffc7#32) .w) (0x80fff814#32+448#32) (0#32) .b) (0x80fff814#32+420#32) (0x80fff860#32) .w) (0x80fff814#32+424#32) (0x80fff868#32) .w) (0x80fff814#32+428#32) (0x80ffffc7#32) .w) (0x80fff814#32+432#32) (0x80fff860#32) .w) (0x80fff814#32+84#32) (0#32) .w) (0x80fff814#32+100#32) (0x80ffec14#32) .w) (0x80fff814#32+104#32) (2048#32) .w) (0x80fff814#32+108#32) (0x80ffec14#32) .w) (0x80fff814#32+112#32) (2048#32) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (used : Word) (sp : c.get 2=0x80ffeb90#32) (fp : c.get 8=0x80fff814#32) (consumed : ramRead ram (0x80fff814#32+92#32) .w=used) (filled : ramRead ram (0x80fff814#32+84#32) .w=used) (uart : ramRead ram (0x80fff814#32+72#32) .w=0x80ffffc7#32) (rx : ramRead ram (0x80fff814#32+56#32) .w=0x80ffec14#32) (capacity : ramRead ram (0x80fff814#32+60#32) .w=2048#32) (object : Memory.Block B 0x80fff814#32 449)
    (hp : c.pc=0x800017e0#32) :
    ∃ d, Quiet.Steps B img 23 ⟨c,ram⟩ ⟨d,memory ram used⟩ ∧ d.pc=0x80000a10#32 ∧
      d.get 10=0x80fff860#32 ∧ d.get 12=0#32 ∧ d.get 11=0x80ffffc7#32 ∧ d.get 13=0x80ffec14#32 ∧ d.get 14=2048#32 ∧ d.get 15=0x80fff868#32 ∧ (∀ r : Reg, r≠10 → r≠12 → r≠11 → r≠13 → r≠14 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (used) 0x800017e2#32
  let c2 := c1.wr 12 (used) 0x800017e4#32
  let c3 := c2.wr 11 (0x80ffffc7#32) 0x800017e6#32
  let c4 := c3.wr 13 (0x80ffec14#32) 0x800017e8#32
  let c5 := c4.wr 14 (2048#32) 0x800017ea#32
  let c6 := c5.wr 12 (0#32) 0x800017ec#32
  let c7 := c6.wr 15 (0x80fff38f#32) 0x800017f0#32
  let c8 := c7.wr 15 (0x80fff868#32) 0x800017f4#32
  let r1 := ramWrite ram (0x80fff814#32+436#32) (0x80fff868#32) .w
  let c9 := c8.goto 0x800017f8#32
  let r2 := ramWrite r1 (0x80fff814#32+440#32) (0x80ffffc7#32) .w
  let c10 := c9.goto 0x800017fc#32
  let r3 := ramWrite r2 (0x80fff814#32+448#32) (0#32) .b
  let c11 := c10.goto 0x80001800#32
  let c12 := c11.wr 10 (0x80fff38f#32) 0x80001804#32
  let c13 := c12.wr 10 (0x80fff860#32) 0x80001808#32
  let r4 := ramWrite r3 (0x80fff814#32+420#32) (0x80fff860#32) .w
  let c14 := c13.goto 0x8000180c#32
  let r5 := ramWrite r4 (0x80fff814#32+424#32) (0x80fff868#32) .w
  let c15 := c14.goto 0x80001810#32
  let r6 := ramWrite r5 (0x80fff814#32+428#32) (0x80ffffc7#32) .w
  let c16 := c15.goto 0x80001814#32
  let r7 := ramWrite r6 (0x80fff814#32+432#32) (0x80fff860#32) .w
  let c17 := c16.goto 0x80001818#32
  let r8 := ramWrite r7 (0x80fff814#32+84#32) (0#32) .w
  let c18 := c17.goto 0x8000181a#32
  let r9 := ramWrite r8 (0x80fff814#32+100#32) (0x80ffec14#32) .w
  let c19 := c18.goto 0x8000181c#32
  let r10 := ramWrite r9 (0x80fff814#32+104#32) (2048#32) .w
  let c20 := c19.goto 0x8000181e#32
  let r11 := ramWrite r10 (0x80fff814#32+108#32) (0x80ffec14#32) .w
  let c21 := c20.goto 0x80001820#32
  let r12 := ramWrite r11 (0x80fff814#32+112#32) (2048#32) .w
  let c22 := c21.goto 0x80001822#32
  let c23 := c22.goto 0x80000a10#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact LoopKeepRebuildCode.at2147489760) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=0x80fff814#32 := by simp [Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 23 (by decide))
      (Memory.block_access object (off := 92) (by decide) (by decide)),consumed];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800017e2#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489762 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=0x80fff814#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 21 (by decide))
      (Memory.block_access object (off := 84) (by decide) (by decide)),filled];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800017e4#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489764 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v8 : c2.get 8=0x80fff814#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 18 (by decide))
      (Memory.block_access object (off := 72) (by decide) (by decide)),uart];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800017e6#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489766 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v8 : c3.get 8=0x80fff814#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 14 (by decide))
      (Memory.block_access object (off := 56) (by decide) (by decide)),rx];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800017e8#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489768 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v8 : c4.get 8=0x80fff814#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 15 (by decide))
      (Memory.block_access object (off := 60) (by decide) (by decide)),capacity];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800017ea#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489770 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v12 : c5.get 12=used := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    have v10 : c5.get 10=used := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_op,v12,v10,show alu .sub used used=0#32 from BitVec.sub_self used];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x800017ec#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489772 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v2 : c6.get 2=0x80ffeb90#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x800017f0#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489776 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v15 : c7.get 15=0x80fff38f#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_opimm,v15];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,r1⟩ := by
    refine Quiet.step_of (by change (0x800017f4#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489780 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 r1 [],[]⟩
    have v8 : c8.get 8=0x80fff814#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    have v15 : c8.get 15=0x80fff868#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_store,v8,v15,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 109 (by decide))
      (Memory.block_access object (off := 436) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r1⟩ ⟨c10,r2⟩ := by
    refine Quiet.step_of (by change (0x800017f8#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489784 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r1 0 [] [] = ⟨.ok c10 r2 [],[]⟩
    have v8 : c9.get 8=0x80fff814#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    have v11 : c9.get 11=0x80ffffc7#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_store,v8,v11,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 110 (by decide))
      (Memory.block_access object (off := 440) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r2⟩ ⟨c11,r3⟩ := by
    refine Quiet.step_of (by change (0x800017fc#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489788 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r2 0 [] [] = ⟨.ok c11 r3 [],[]⟩
    have v8 : c10.get 8=0x80fff814#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_store,v8,Core.get_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o
      (by exact Nat.mod_one _)
      (Memory.block_access object (off := 448) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r3⟩ ⟨c12,r3⟩ := by
    refine Quiet.step_of (by change (0x80001800#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489792 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r3 0 [] [] = ⟨.ok c12 r3 [],[]⟩
    have v2 : c11.get 2=0x80ffeb90#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,r3⟩ ⟨c13,r3⟩ := by
    refine Quiet.step_of (by change (0x80001804#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489796 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r3 0 [] [] = ⟨.ok c13 r3 [],[]⟩
    have v10 : c12.get 10=0x80fff38f#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r3⟩ ⟨c14,r4⟩ := by
    refine Quiet.step_of (by change (0x80001808#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489800 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r3 0 [] [] = ⟨.ok c14 r4 [],[]⟩
    have v8 : c13.get 8=0x80fff814#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    have v10 : c13.get 10=0x80fff860#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_store,v8,v10,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 105 (by decide))
      (Memory.block_access object (off := 420) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,r4⟩ ⟨c15,r5⟩ := by
    refine Quiet.step_of (by change (0x8000180c#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489804 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) r4 0 [] [] = ⟨.ok c15 r5 [],[]⟩
    have v8 : c14.get 8=0x80fff814#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    have v15 : c14.get 15=0x80fff868#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_store,v8,v15,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 106 (by decide))
      (Memory.block_access object (off := 424) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,r5⟩ ⟨c16,r6⟩ := by
    refine Quiet.step_of (by change (0x80001810#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489808 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) r5 0 [] [] = ⟨.ok c16 r6 [],[]⟩
    have v8 : c15.get 8=0x80fff814#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    have v11 : c15.get 11=0x80ffffc7#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_store,v8,v11,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 107 (by decide))
      (Memory.block_access object (off := 428) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,r6⟩ ⟨c17,r7⟩ := by
    refine Quiet.step_of (by change (0x80001814#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489812 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) r6 0 [] [] = ⟨.ok c17 r7 [],[]⟩
    have v8 : c16.get 8=0x80fff814#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    have v10 : c16.get 10=0x80fff860#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_store,v8,v10,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 108 (by decide))
      (Memory.block_access object (off := 432) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,r7⟩ ⟨c18,r8⟩ := by
    refine Quiet.step_of (by change (0x80001818#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489816 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) r7 0 [] [] = ⟨.ok c18 r8 [],[]⟩
    have v8 : c17.get 8=0x80fff814#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    have v12 : c17.get 12=0#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_store,v8,v12,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 21 (by decide))
      (Memory.block_access object (off := 84) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,r8⟩ ⟨c19,r9⟩ := by
    refine Quiet.step_of (by change (0x8000181a#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489818 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) r8 0 [] [] = ⟨.ok c19 r9 [],[]⟩
    have v8 : c18.get 8=0x80fff814#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    have v13 : c18.get 13=0x80ffec14#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_store,v8,v13,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 25 (by decide))
      (Memory.block_access object (off := 100) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,r9⟩ ⟨c20,r10⟩ := by
    refine Quiet.step_of (by change (0x8000181c#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489820 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) r9 0 [] [] = ⟨.ok c20 r10 [],[]⟩
    have v8 : c19.get 8=0x80fff814#32 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    have v14 : c19.get 14=2048#32 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_store,v8,v14,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 26 (by decide))
      (Memory.block_access object (off := 104) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,r10⟩ ⟨c21,r11⟩ := by
    refine Quiet.step_of (by change (0x8000181e#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489822 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) r10 0 [] [] = ⟨.ok c21 r11 [],[]⟩
    have v8 : c20.get 8=0x80fff814#32 := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    have v13 : c20.get 13=0x80ffec14#32 := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_store,v8,v13,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 27 (by decide))
      (Memory.block_access object (off := 108) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,r11⟩ ⟨c22,r12⟩ := by
    refine Quiet.step_of (by change (0x80001820#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489824 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) r11 0 [] [] = ⟨.ok c22 r12 [],[]⟩
    have v8 : c21.get 8=0x80fff814#32 := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    have v14 : c21.get 14=2048#32 := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_store,v8,v14,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 28 (by decide))
      (Memory.block_access object (off := 112) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,r12⟩ ⟨c23,r12⟩ := by
    refine Quiet.step_of (by change (0x80001822#32).getLsbD 0=false;decide) LoopKeepRebuildCode.at2147489826 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) r12 0 [] [] = ⟨.ok c23 r12 [],[]⟩
    have v14 : c22.get 14=2048#32 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    have v12 : c22.get 12=0#32 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
    rw [exec_branch,v14,v12,show taken .geu 2048#32 0#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c22.pc=0x80001822#32 from rfl,show 0x80001822#32+0xfffff1ee#32=0x80000a10#32 by decide +kernel]
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c23,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.single t22)))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
  · simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
  · simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
  · simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
  · simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
  · simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp]
  · intro reg h10 h12 h11 h13 h14 h15;simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,h10,h12,h11,h13,h14,h15]
end E5R.Thermostat.LoopKeepRebuild
