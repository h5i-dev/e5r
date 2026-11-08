import Projects.thermostat.MainChunkCode
import Projects.thermostat.QuietRam
import Projects.thermostat.FrameOffsets
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainChunkPersist
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp index : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+3696#32) (ramRead ram (sp+4840#32) .w) .w) (sp+3700#32) (ramRead ram (sp+4844#32) .w) .w) (sp+3704#32) (ramRead ram (sp+4848#32) .w) .w) (sp+3708#32) (ramRead ram (sp+4852#32) .w) .w) (sp+3680#32) (ramRead ram (sp+4824#32) .w) .w) (sp+3684#32) (ramRead ram (sp+4828#32) .w) .w) (sp+3688#32) (ramRead ram (sp+4832#32) .w) .w) (sp+3692#32) (ramRead ram (sp+4836#32) .w) .w) (sp+3656#32) (index+1#32) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp index : Word) (h8 : c.get 8=sp+3204#32) (h23 : c.get 23=sp+3680#32) (hm : Memory.Block B sp 4928) (ha : sp.toNat%4=0) (hindex : ramRead ram (sp+3656#32) .w=index)
    (hp : c.pc=0x80000f10#32) :
    ∃ d, Quiet.Steps B img 21 ⟨c,ram⟩ ⟨d,memory ram sp index⟩ ∧ d.pc=0x80000f62#32 ∧
      d.get 11=ramRead ram (sp+4840#32) .w ∧ d.get 12=ramRead ram (sp+4844#32) .w ∧ d.get 13=ramRead ram (sp+4848#32) .w ∧ d.get 14=ramRead ram (sp+4852#32) .w ∧ d.get 15=ramRead ram (sp+4824#32) .w ∧ d.get 16=ramRead ram (sp+4828#32) .w ∧ d.get 17=ramRead ram (sp+4832#32) .w ∧ d.get 5=ramRead ram (sp+4836#32) .w ∧ d.get 24=index+1#32 ∧ d.get 10=extend .h false (ramRead ram (sp+4856#32) .h) ∧ d.get 27=extend .h false (ramRead ram (sp+4858#32) .h) ∧ (∀ r : Reg, r≠11 → r≠12 → r≠13 → r≠14 → r≠15 → r≠16 → r≠17 → r≠5 → r≠24 → r≠10 → r≠27 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (ramRead ram (sp+4840#32) .w) 0x80000f14#32
  let c2 := c1.wr 12 (ramRead ram (sp+4844#32) .w) 0x80000f18#32
  let c3 := c2.wr 13 (ramRead ram (sp+4848#32) .w) 0x80000f1c#32
  let c4 := c3.wr 14 (ramRead ram (sp+4852#32) .w) 0x80000f20#32
  let c5 := c4.wr 15 (ramRead ram (sp+4824#32) .w) 0x80000f24#32
  let c6 := c5.wr 16 (ramRead ram (sp+4828#32) .w) 0x80000f28#32
  let c7 := c6.wr 17 (ramRead ram (sp+4832#32) .w) 0x80000f2c#32
  let c8 := c7.wr 5 (ramRead ram (sp+4836#32) .w) 0x80000f30#32
  let c9 := c8.wr 24 (index) 0x80000f34#32
  let c10 := c9.wr 10 (extend .h false (ramRead ram (sp+4856#32) .h)) 0x80000f38#32
  let r1 := ramWrite ram (sp+3696#32) (ramRead ram (sp+4840#32) .w) .w
  let c11 := c10.goto 0x80000f3c#32
  let r2 := ramWrite r1 (sp+3700#32) (ramRead ram (sp+4844#32) .w) .w
  let c12 := c11.goto 0x80000f40#32
  let r3 := ramWrite r2 (sp+3704#32) (ramRead ram (sp+4848#32) .w) .w
  let c13 := c12.goto 0x80000f44#32
  let r4 := ramWrite r3 (sp+3708#32) (ramRead ram (sp+4852#32) .w) .w
  let c14 := c13.goto 0x80000f48#32
  let c15 := c14.wr 27 (extend .h false (ramRead ram (sp+4858#32) .h)) 0x80000f4c#32
  let c16 := c15.wr 24 (index+1#32) 0x80000f4e#32
  let r5 := ramWrite r4 (sp+3680#32) (ramRead ram (sp+4824#32) .w) .w
  let c17 := c16.goto 0x80000f52#32
  let r6 := ramWrite r5 (sp+3684#32) (ramRead ram (sp+4828#32) .w) .w
  let c18 := c17.goto 0x80000f56#32
  let r7 := ramWrite r6 (sp+3688#32) (ramRead ram (sp+4832#32) .w) .w
  let c19 := c18.goto 0x80000f5a#32
  let r8 := ramWrite r7 (sp+3692#32) (ramRead ram (sp+4836#32) .w) .w
  let c20 := c19.goto 0x80000f5e#32
  let r9 := ramWrite r8 (sp+3656#32) (index+1#32) .w
  let c21 := c20.goto 0x80000f62#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact cc2147487504) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=sp+3204#32 := by simp [Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1636#32=4840#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1210 ha)
        (Memory.block_access hm (off := 4840) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f14#32).getLsbD 0=false;decide) cc2147487508 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=sp+3204#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1640#32=4844#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1211 ha)
        (Memory.block_access hm (off := 4844) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f18#32).getLsbD 0=false;decide) cc2147487512 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v8 : c2.get 8=sp+3204#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1644#32=4848#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1212 ha)
        (Memory.block_access hm (off := 4848) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f1c#32).getLsbD 0=false;decide) cc2147487516 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v8 : c3.get 8=sp+3204#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1648#32=4852#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1213 ha)
        (Memory.block_access hm (off := 4852) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f20#32).getLsbD 0=false;decide) cc2147487520 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v8 : c4.get 8=sp+3204#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1620#32=4824#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1206 ha)
        (Memory.block_access hm (off := 4824) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f24#32).getLsbD 0=false;decide) cc2147487524 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v8 : c5.get 8=sp+3204#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1624#32=4828#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1207 ha)
        (Memory.block_access hm (off := 4828) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f28#32).getLsbD 0=false;decide) cc2147487528 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v8 : c6.get 8=sp+3204#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1628#32=4832#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1208 ha)
        (Memory.block_access hm (off := 4832) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f2c#32).getLsbD 0=false;decide) cc2147487532 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v8 : c7.get 8=sp+3204#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1632#32=4836#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1209 ha)
        (Memory.block_access hm (off := 4836) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f30#32).getLsbD 0=false;decide) cc2147487536 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v8 : c8.get 8=sp+3204#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+452#32=3656#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 914 ha)
        (Memory.block_access hm (off := 3656) (by decide) (by decide)),hindex];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f34#32).getLsbD 0=false;decide) cc2147487540 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v8 : c9.get 8=sp+3204#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1652#32=4856#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 2428 (by omega))
        (Memory.block_access hm (off := 4856) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,r1⟩ := by
    refine Quiet.step_of (by change (0x80000f38#32).getLsbD 0=false;decide) cc2147487544 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 r1 [],[]⟩
    have v23 : c10.get 23=sp+3680#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    have v11 : c10.get 11=ramRead ram (sp+4840#32) .w := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_store,v23,v11,BitVec.add_assoc,show 3680#32+16#32=3696#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 924 ha)
        (Memory.block_access hm (off := 3696) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r1⟩ ⟨c12,r2⟩ := by
    refine Quiet.step_of (by change (0x80000f3c#32).getLsbD 0=false;decide) cc2147487548 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r1 0 [] [] = ⟨.ok c12 r2 [],[]⟩
    have v23 : c11.get 23=sp+3680#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    have v12 : c11.get 12=ramRead ram (sp+4844#32) .w := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_store,v23,v12,BitVec.add_assoc,show 3680#32+20#32=3700#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 925 ha)
        (Memory.block_access hm (off := 3700) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,r2⟩ ⟨c13,r3⟩ := by
    refine Quiet.step_of (by change (0x80000f40#32).getLsbD 0=false;decide) cc2147487552 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r2 0 [] [] = ⟨.ok c13 r3 [],[]⟩
    have v23 : c12.get 23=sp+3680#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    have v13 : c12.get 13=ramRead ram (sp+4848#32) .w := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_store,v23,v13,BitVec.add_assoc,show 3680#32+24#32=3704#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 926 ha)
        (Memory.block_access hm (off := 3704) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r3⟩ ⟨c14,r4⟩ := by
    refine Quiet.step_of (by change (0x80000f44#32).getLsbD 0=false;decide) cc2147487556 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r3 0 [] [] = ⟨.ok c14 r4 [],[]⟩
    have v23 : c13.get 23=sp+3680#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    have v14 : c13.get 14=ramRead ram (sp+4852#32) .w := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_store,v23,v14,BitVec.add_assoc,show 3680#32+28#32=3708#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 927 ha)
        (Memory.block_access hm (off := 3708) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,r4⟩ ⟨c15,r4⟩ := by
    refine Quiet.step_of (by change (0x80000f48#32).getLsbD 0=false;decide) cc2147487560 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) r4 0 [] [] = ⟨.ok c15 r4 [],[]⟩
    have loadFrame : ramRead r4 (sp+4858#32) .h=ramRead ram (sp+4858#32) .h := by
      rw [FrameOffsets.half _ sp _ 4858 3708 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.half _ sp _ 4858 3704 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.half _ sp _ 4858 3700 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.half _ sp _ 4858 3696 .w (by decide) (by decide) (by decide)]
    have v8 : c14.get 8=sp+3204#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1654#32=4858#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 2429 (by omega))
        (Memory.block_access hm (off := 4858) (by decide) (by decide)),loadFrame];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,r4⟩ ⟨c16,r4⟩ := by
    refine Quiet.step_of (by change (0x80000f4c#32).getLsbD 0=false;decide) cc2147487564 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) r4 0 [] [] = ⟨.ok c16 r4 [],[]⟩
    have v24 : c15.get 24=index := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_opimm,v24];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,r4⟩ ⟨c17,r5⟩ := by
    refine Quiet.step_of (by change (0x80000f4e#32).getLsbD 0=false;decide) cc2147487566 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) r4 0 [] [] = ⟨.ok c17 r5 [],[]⟩
    have v23 : c16.get 23=sp+3680#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    have v15 : c16.get 15=ramRead ram (sp+4824#32) .w := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_store,v23,v15,BitVec.add_assoc,show 3680#32+0#32=3680#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 920 ha)
        (Memory.block_access hm (off := 3680) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,r5⟩ ⟨c18,r6⟩ := by
    refine Quiet.step_of (by change (0x80000f52#32).getLsbD 0=false;decide) cc2147487570 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) r5 0 [] [] = ⟨.ok c18 r6 [],[]⟩
    have v23 : c17.get 23=sp+3680#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    have v16 : c17.get 16=ramRead ram (sp+4828#32) .w := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_store,v23,v16,BitVec.add_assoc,show 3680#32+4#32=3684#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 921 ha)
        (Memory.block_access hm (off := 3684) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,r6⟩ ⟨c19,r7⟩ := by
    refine Quiet.step_of (by change (0x80000f56#32).getLsbD 0=false;decide) cc2147487574 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) r6 0 [] [] = ⟨.ok c19 r7 [],[]⟩
    have v23 : c18.get 23=sp+3680#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    have v17 : c18.get 17=ramRead ram (sp+4832#32) .w := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_store,v23,v17,BitVec.add_assoc,show 3680#32+8#32=3688#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 922 ha)
        (Memory.block_access hm (off := 3688) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,r7⟩ ⟨c20,r8⟩ := by
    refine Quiet.step_of (by change (0x80000f5a#32).getLsbD 0=false;decide) cc2147487578 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) r7 0 [] [] = ⟨.ok c20 r8 [],[]⟩
    have v23 : c19.get 23=sp+3680#32 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    have v5 : c19.get 5=ramRead ram (sp+4836#32) .w := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_store,v23,v5,BitVec.add_assoc,show 3680#32+12#32=3692#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 923 ha)
        (Memory.block_access hm (off := 3692) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,r8⟩ ⟨c21,r9⟩ := by
    refine Quiet.step_of (by change (0x80000f5e#32).getLsbD 0=false;decide) cc2147487582 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) r8 0 [] [] = ⟨.ok c21 r9 [],[]⟩
    have v8 : c20.get 8=sp+3204#32 := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    have v24 : c20.get 24=index+1#32 := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
    rw [exec_store,v8,v24,BitVec.add_assoc,show 3204#32+452#32=3656#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 914 ha)
        (Memory.block_access hm (off := 3656) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c21,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.single t20)))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
  · simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
  · simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
  · simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
  · simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
  · simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
  · simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
  · simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
  · simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
  · simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
  · simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23]
  · intro reg h11 h12 h13 h14 h15 h16 h17 h5 h24 h10 h27;simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h23,h11,h12,h13,h14,h15,h16,h17,h5,h24,h10,h27]
end E5R.Thermostat.MainChunkPersist
