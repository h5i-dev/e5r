import Projects.thermostat.StateHeadCode
import Projects.thermostat.MainStateRouteCode
import Projects.thermostat.QuietRam
import Projects.thermostat.FrameOffsets
import Projects.thermostat.ViewFrame
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.StateHeadSetup
open E5R E5R.Thermostat
abbrev sp : Word := 0x80ffeb90#32

def memory (ram : Word → BitVec 8)  :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+3680#32) (0#32) .w) (sp+3956#32) (0#32) .b) (sp+3932#32) (832#32) .w) (sp+3916#32) (2164255745#32) .w) (sp+3920#32) (2164258944#32) .w) (sp+3924#32) (2164255676#32) .w) (sp+3928#32) (2164258004#32) .w) (sp+3936#32) (2164258944#32) .w) (sp+3940#32) (2164255676#32) .w) (sp+3944#32) (2164258004#32) .w) (sp+3948#32) (832#32) .w) (sp+3952#32) (0#32) .b) (sp+4824#32) (0#32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (h8 : c.get 8=0x80fff814#32) (h10 : c.get 10=1#32) (h11 : c.get 11=0#32) (h22 : c.get 22=1#32)
    (stack : Memory.Block B 0x80ffeb90#32 5232)
    (futureRouter : ramRead ram 0x80fffac4#32 .w=0x80ffebf8#32)
    (futureRequest : ramRead ram 0x80fffac8#32 .w=0x80fff880#32)
    (futureEngine : ramRead ram 0x80fffacc#32 .w=0x80ffebbc#32)
    (futurePayload : ramRead ram 0x80fffad0#32 .w=0x80fff4d4#32)
    (futureCapacity : ramRead ram 0x80fffad4#32 .w=832#32)
    (methodHead : ram 0x80fff9f4#32=1#8) (routeGet : ram 0x80ffec00#32=0#8)
    (hp : c.pc=0x800013d2#32) :
    ∃ d, Quiet.Steps B img 32 ⟨c,ram⟩ ⟨d,memory ram ⟩ ∧ d.pc=0x80001f6e#32 ∧
      d.get 13=0#32 ∧ d.get 10=2164258944#32 ∧ d.get 12=1#32 ∧ d.get 20=832#32 ∧ d.get 11=2164255745#32 ∧ d.get 9=2164255676#32 ∧ d.get 24=2164258004#32 ∧ d.get 1=2147490280#32 ∧ (∀ r : Reg, r≠13 → r≠10 → r≠12 → r≠20 → r≠11 → r≠9 → r≠24 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x800013d6#32
  let c2 := c1.wr 13 (2164255736#32) 0x800013da#32
  let c3 := c2.wr 10 (2164258944#32) 0x800013de#32
  let c4 := c3.wr 12 (1#32) 0x800013e2#32
  let c5 := c4.wr 13 (0#32) 0x800013e6#32
  let c6 := c5.goto 0x800013ea#32
  let c7 := c6.wr 12 0#32 0x800013ee#32
  let c8 := c7.wr 12 0#32 0x800013f0#32
  let c9 := c8.wr 12 1#32 0x800013f4#32
  let c10 := c9.goto 0x800018bc#32
  let r1 := ramWrite ram (sp+3680#32) (0#32) .w
  let c11 := c10.goto 0x800018c0#32
  let r2 := ramWrite r1 (sp+3956#32) (0#32) .b
  let c12 := c11.goto 0x800018c4#32
  let c13 := c12.wr 20 (832#32) 0x800018c8#32
  let c14 := c13.wr 11 (2164255736#32) 0x800018cc#32
  let c15 := c14.wr 10 (2164258944#32) 0x800018d0#32
  let c16 := c15.wr 9 (2164255676#32) 0x800018d4#32
  let c17 := c16.wr 24 (2164258004#32) 0x800018d8#32
  let r3 := ramWrite r2 (sp+3932#32) (832#32) .w
  let c18 := c17.goto 0x800018dc#32
  let c19 := c18.wr 11 (2164255745#32) 0x800018de#32
  let r4 := ramWrite r3 (sp+3916#32) (2164255745#32) .w
  let c20 := c19.goto 0x800018e2#32
  let r5 := ramWrite r4 (sp+3920#32) (2164258944#32) .w
  let c21 := c20.goto 0x800018e6#32
  let r6 := ramWrite r5 (sp+3924#32) (2164255676#32) .w
  let c22 := c21.goto 0x800018ea#32
  let r7 := ramWrite r6 (sp+3928#32) (2164258004#32) .w
  let c23 := c22.goto 0x800018ee#32
  let c24 := c23.goto 0x800019c8#32
  let r8 := ramWrite r7 (sp+3936#32) (2164258944#32) .w
  let c25 := c24.goto 0x800019cc#32
  let r9 := ramWrite r8 (sp+3940#32) (2164255676#32) .w
  let c26 := c25.goto 0x800019d0#32
  let r10 := ramWrite r9 (sp+3944#32) (2164258004#32) .w
  let c27 := c26.goto 0x800019d4#32
  let r11 := ramWrite r10 (sp+3948#32) (832#32) .w
  let c28 := c27.goto 0x800019d8#32
  let r12 := ramWrite r11 (sp+3952#32) (0#32) .b
  let c29 := c28.goto 0x800019dc#32
  let r13 := ramWrite r12 (sp+4824#32) (0#32) .b
  let c30 := c29.goto 0x800019e0#32
  let c31 := c30.wr 1 (2147490272#32) 0x800019e4#32
  let c32 := c31.wr 1 (2147490280#32) 0x80001f6e#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147488722) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v10 : c.get 10=1#32 := by simp [c9,c8,c7,c6,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    have v22 : c.get 22=1#32 := by simp [c9,c8,c7,c6,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_branch,v10,v22,show taken .ne 1#32 1#32=false by decide +kernel]
    rw [hp];rfl
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800013d6#32).getLsbD 0=false;decide) rt2147488726 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_load,v8,show 2164258836#32+688#32=sp+3892#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 973 (by decide +kernel)) (Memory.block_access stack (off := 3892) (by decide) (by decide))]
    have saved : ramRead ram (sp+3892#32) .w=ramRead ram (sp+3892#32) .w := by
      rfl
    change Observed.interp B img o (.done (c1.wr 13 (extend .w true (ramRead ram (sp+3892#32) .w)) (c1.pc+4#32))) ram 0 [] []=_
    rw [saved,show sp+3892#32=2164259524#32 by decide +kernel,futureRouter];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800013da#32).getLsbD 0=false;decide) rt2147488730 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v8 : c2.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_load,v8,show 2164258836#32+692#32=sp+3896#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 974 (by decide +kernel)) (Memory.block_access stack (off := 3896) (by decide) (by decide))]
    have saved : ramRead ram (sp+3896#32) .w=ramRead ram (sp+3896#32) .w := by
      rfl
    change Observed.interp B img o (.done (c2.wr 10 (extend .w true (ramRead ram (sp+3896#32) .w)) (c2.pc+4#32))) ram 0 [] []=_
    rw [saved,show sp+3896#32=2164259528#32 by decide +kernel,futureRequest];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800013de#32).getLsbD 0=false;decide) rt2147488734 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v10 : c3.get 10=2164258944#32 := by simp [c9,c8,c7,c6,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_load,v10,show 2164258944#32+372#32=sp+3684#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3684) (by decide) (by decide))]
    change Observed.interp B img o (.done (c3.wr 12 (extend .b false (BitVec.ofNat 32 (ram 2164259316#32).toNat)) (c3.pc+4#32))) ram 0 [] []=_
    rw [methodHead];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800013e2#32).getLsbD 0=false;decide) rt2147488738 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v13 : c4.get 13=2164255736#32 := by simp [c9,c8,c7,c6,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_load,v13,show 2164255736#32+8#32=sp+112#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 112) (by decide) (by decide))]
    change Observed.interp B img o (.done (c4.wr 13 (extend .b false (BitVec.ofNat 32 (ram 2164255744#32).toNat)) (c4.pc+4#32))) ram 0 [] []=_
    rw [routeGet];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800013e6#32).getLsbD 0=false;decide) rt2147488742 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] []=⟨.ok c6 ram [],[]⟩
    have v13 : c5.get 13=0#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have v12 : c5.get 12=1#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_branch,v13,v12,show taken .eq 0#32 1#32=false by decide +kernel];rfl
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x800013ea#32).getLsbD 0=false;decide) sh2147488746 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] []=⟨.ok c7 ram [],[]⟩
    have v12 : c6.get 12=1#32 := by simp [c9,c8,c7,c6,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_opimm,v12,show alu .xor 1#32 1#32=0#32 by decide +kernel];rfl
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x800013ee#32).getLsbD 0=false;decide) sh2147488750 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] []=⟨.ok c8 ram [],[]⟩
    have v12 : c7.get 12=0#32 := Core.wr_get_self _ _ _ _ (by decide)
    have v13 : c7.get 13=0#32 := by simp [c9,c8,c7,c6,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_op,v12,v13,show alu .or 0#32 0#32=0#32 by decide +kernel];rfl
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x800013f0#32).getLsbD 0=false;decide) sh2147488752 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] []=⟨.ok c9 ram [],[]⟩
    have v12 : c8.get 12=0#32 := Core.wr_get_self _ _ _ _ (by decide)
    rw [exec_opimm,v12,show alu .sltu 0#32 1#32=1#32 by decide +kernel];rfl
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x800013f4#32).getLsbD 0=false;decide) sh2147488756 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] []=⟨.ok c10 ram [],[]⟩
    have v12 : c9.get 12=1#32 := Core.wr_get_self _ _ _ _ (by decide)
    rw [exec_branch,v12,Core.get_zero,show taken .ne 1#32 (0 : Word)=true by decide +kernel,ite_eq_left rfl,
      show c9.pc=0x800013f4#32 from rfl,show 0x800013f4#32+1224#32=0x800018bc#32 by decide +kernel]
    rw [jump_ok _ _ (by decide)];rfl
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,r1⟩ := by
    refine Quiet.step_of (by change (0x800018bc#32).getLsbD 0=false;decide) rt2147489980 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 r1 [],[]⟩
    have v10 : c10.get 10=2164258944#32 := by simp [c9,c8,c7,c6,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    have v11 : c10.get 11=0#32 := by simp [c9,c8,c7,c6,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_store,v10,v11,show 2164258944#32+368#32=sp+3680#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 920 (by decide +kernel)) (Memory.block_access stack (off := 3680) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r1⟩ ⟨c12,r2⟩ := by
    refine Quiet.step_of (by change (0x800018c0#32).getLsbD 0=false;decide) rt2147489984 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r1 0 [] [] = ⟨.ok c12 r2 [],[]⟩
    have v8 : c11.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    have v0 : c11.get 0=0#32 := by simp [c9,c8,c7,c6,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_store,v8,v0,show 2164258836#32+752#32=sp+3956#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3956) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,r2⟩ ⟨c13,r2⟩ := by
    refine Quiet.step_of (by change (0x800018c4#32).getLsbD 0=false;decide) rt2147489988 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r2 0 [] [] = ⟨.ok c13 r2 [],[]⟩
    have v8 : c12.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_load,v8,show 2164258836#32+704#32=sp+3908#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 977 (by decide +kernel)) (Memory.block_access stack (off := 3908) (by decide) (by decide))]
    have saved : ramRead r2 (sp+3908#32) .w=ramRead ram (sp+3908#32) .w := by
      rw [FrameOffsets.word _ sp _ 3908 3956 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ sp _ 3908 3680 .w (by decide) (by decide) (by decide)]
    change Observed.interp B img o (.done (c12.wr 20 (extend .w true (ramRead r2 (sp+3908#32) .w)) (c12.pc+4#32))) r2 0 [] []=_
    rw [saved,show sp+3908#32=2164259540#32 by decide +kernel,futureCapacity];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r2⟩ ⟨c14,r2⟩ := by
    refine Quiet.step_of (by change (0x800018c8#32).getLsbD 0=false;decide) rt2147489992 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r2 0 [] [] = ⟨.ok c14 r2 [],[]⟩
    have v8 : c13.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_load,v8,show 2164258836#32+688#32=sp+3892#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 973 (by decide +kernel)) (Memory.block_access stack (off := 3892) (by decide) (by decide))]
    have saved : ramRead r2 (sp+3892#32) .w=ramRead ram (sp+3892#32) .w := by
      rw [FrameOffsets.word _ sp _ 3892 3956 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ sp _ 3892 3680 .w (by decide) (by decide) (by decide)]
    change Observed.interp B img o (.done (c13.wr 11 (extend .w true (ramRead r2 (sp+3892#32) .w)) (c13.pc+4#32))) r2 0 [] []=_
    rw [saved,show sp+3892#32=2164259524#32 by decide +kernel,futureRouter];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,r2⟩ ⟨c15,r2⟩ := by
    refine Quiet.step_of (by change (0x800018cc#32).getLsbD 0=false;decide) rt2147489996 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) r2 0 [] [] = ⟨.ok c15 r2 [],[]⟩
    have v8 : c14.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_load,v8,show 2164258836#32+692#32=sp+3896#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 974 (by decide +kernel)) (Memory.block_access stack (off := 3896) (by decide) (by decide))]
    have saved : ramRead r2 (sp+3896#32) .w=ramRead ram (sp+3896#32) .w := by
      rw [FrameOffsets.word _ sp _ 3896 3956 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ sp _ 3896 3680 .w (by decide) (by decide) (by decide)]
    change Observed.interp B img o (.done (c14.wr 10 (extend .w true (ramRead r2 (sp+3896#32) .w)) (c14.pc+4#32))) r2 0 [] []=_
    rw [saved,show sp+3896#32=2164259528#32 by decide +kernel,futureRequest];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,r2⟩ ⟨c16,r2⟩ := by
    refine Quiet.step_of (by change (0x800018d0#32).getLsbD 0=false;decide) rt2147490000 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) r2 0 [] [] = ⟨.ok c16 r2 [],[]⟩
    have v8 : c15.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_load,v8,show 2164258836#32+696#32=sp+3900#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 975 (by decide +kernel)) (Memory.block_access stack (off := 3900) (by decide) (by decide))]
    have saved : ramRead r2 (sp+3900#32) .w=ramRead ram (sp+3900#32) .w := by
      rw [FrameOffsets.word _ sp _ 3900 3956 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ sp _ 3900 3680 .w (by decide) (by decide) (by decide)]
    change Observed.interp B img o (.done (c15.wr 9 (extend .w true (ramRead r2 (sp+3900#32) .w)) (c15.pc+4#32))) r2 0 [] []=_
    rw [saved,show sp+3900#32=2164259532#32 by decide +kernel,futureEngine];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,r2⟩ ⟨c17,r2⟩ := by
    refine Quiet.step_of (by change (0x800018d4#32).getLsbD 0=false;decide) rt2147490004 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) r2 0 [] [] = ⟨.ok c17 r2 [],[]⟩
    have v8 : c16.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_load,v8,show 2164258836#32+700#32=sp+3904#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 976 (by decide +kernel)) (Memory.block_access stack (off := 3904) (by decide) (by decide))]
    have saved : ramRead r2 (sp+3904#32) .w=ramRead ram (sp+3904#32) .w := by
      rw [FrameOffsets.word _ sp _ 3904 3956 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ sp _ 3904 3680 .w (by decide) (by decide) (by decide)]
    change Observed.interp B img o (.done (c16.wr 24 (extend .w true (ramRead r2 (sp+3904#32) .w)) (c16.pc+4#32))) r2 0 [] []=_
    rw [saved,show sp+3904#32=2164259536#32 by decide +kernel,futurePayload];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,r2⟩ ⟨c18,r3⟩ := by
    refine Quiet.step_of (by change (0x800018d8#32).getLsbD 0=false;decide) rt2147490008 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) r2 0 [] [] = ⟨.ok c18 r3 [],[]⟩
    have v8 : c17.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    have v20 : c17.get 20=832#32 := by simp [c9,c8,c7,c6,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_store,v8,v20,show 2164258836#32+728#32=sp+3932#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 983 (by decide +kernel)) (Memory.block_access stack (off := 3932) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,r3⟩ ⟨c19,r3⟩ := by
    refine Quiet.step_of (by change (0x800018dc#32).getLsbD 0=false;decide) rt2147490012 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) r3 0 [] [] = ⟨.ok c19 r3 [],[]⟩
    have v11 : c18.get 11=2164255736#32 := by simp [c9,c8,c7,c6,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_opimm,v11,show alu .add 2164255736#32 9#32=2164255745#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,r3⟩ ⟨c20,r4⟩ := by
    refine Quiet.step_of (by change (0x800018de#32).getLsbD 0=false;decide) rt2147490014 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) r3 0 [] [] = ⟨.ok c20 r4 [],[]⟩
    have v8 : c19.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    have v11 : c19.get 11=2164255745#32 := by simp [c9,c8,c7,c6,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_store,v8,v11,show 2164258836#32+712#32=sp+3916#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 979 (by decide +kernel)) (Memory.block_access stack (off := 3916) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,r4⟩ ⟨c21,r5⟩ := by
    refine Quiet.step_of (by change (0x800018e2#32).getLsbD 0=false;decide) rt2147490018 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) r4 0 [] [] = ⟨.ok c21 r5 [],[]⟩
    have v8 : c20.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    have v10 : c20.get 10=2164258944#32 := by simp [c9,c8,c7,c6,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_store,v8,v10,show 2164258836#32+716#32=sp+3920#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 980 (by decide +kernel)) (Memory.block_access stack (off := 3920) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,r5⟩ ⟨c22,r6⟩ := by
    refine Quiet.step_of (by change (0x800018e6#32).getLsbD 0=false;decide) rt2147490022 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) r5 0 [] [] = ⟨.ok c22 r6 [],[]⟩
    have v8 : c21.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    have v9 : c21.get 9=2164255676#32 := by simp [c9,c8,c7,c6,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_store,v8,v9,show 2164258836#32+720#32=sp+3924#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 981 (by decide +kernel)) (Memory.block_access stack (off := 3924) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,r6⟩ ⟨c23,r7⟩ := by
    refine Quiet.step_of (by change (0x800018ea#32).getLsbD 0=false;decide) rt2147490026 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) r6 0 [] [] = ⟨.ok c23 r7 [],[]⟩
    have v8 : c22.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    have v24 : c22.get 24=2164258004#32 := by simp [c9,c8,c7,c6,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_store,v8,v24,show 2164258836#32+724#32=sp+3928#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 982 (by decide +kernel)) (Memory.block_access stack (off := 3928) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t23 : Quiet.Step B img ⟨c23,r7⟩ ⟨c24,r7⟩ := by
    refine Quiet.step_of (by change (0x800018ee#32).getLsbD 0=false;decide) rt2147490030 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) r7 0 [] [] = ⟨.ok c24 r7 [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c23 2147490248#32) r7 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t24 : Quiet.Step B img ⟨c24,r7⟩ ⟨c25,r8⟩ := by
    refine Quiet.step_of (by change (0x800019c8#32).getLsbD 0=false;decide) rt2147490248 fun o => ?_
    change Observed.interp B img o (exec c24 _ _) r7 0 [] [] = ⟨.ok c25 r8 [],[]⟩
    have v8 : c24.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    have v10 : c24.get 10=2164258944#32 := by simp [c9,c8,c7,c6,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_store,v8,v10,show 2164258836#32+732#32=sp+3936#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 984 (by decide +kernel)) (Memory.block_access stack (off := 3936) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t25 : Quiet.Step B img ⟨c25,r8⟩ ⟨c26,r9⟩ := by
    refine Quiet.step_of (by change (0x800019cc#32).getLsbD 0=false;decide) rt2147490252 fun o => ?_
    change Observed.interp B img o (exec c25 _ _) r8 0 [] [] = ⟨.ok c26 r9 [],[]⟩
    have v8 : c25.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    have v9 : c25.get 9=2164255676#32 := by simp [c9,c8,c7,c6,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_store,v8,v9,show 2164258836#32+736#32=sp+3940#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 985 (by decide +kernel)) (Memory.block_access stack (off := 3940) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t26 : Quiet.Step B img ⟨c26,r9⟩ ⟨c27,r10⟩ := by
    refine Quiet.step_of (by change (0x800019d0#32).getLsbD 0=false;decide) rt2147490256 fun o => ?_
    change Observed.interp B img o (exec c26 _ _) r9 0 [] [] = ⟨.ok c27 r10 [],[]⟩
    have v8 : c26.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    have v24 : c26.get 24=2164258004#32 := by simp [c9,c8,c7,c6,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_store,v8,v24,show 2164258836#32+740#32=sp+3944#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 986 (by decide +kernel)) (Memory.block_access stack (off := 3944) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t27 : Quiet.Step B img ⟨c27,r10⟩ ⟨c28,r11⟩ := by
    refine Quiet.step_of (by change (0x800019d4#32).getLsbD 0=false;decide) rt2147490260 fun o => ?_
    change Observed.interp B img o (exec c27 _ _) r10 0 [] [] = ⟨.ok c28 r11 [],[]⟩
    have v8 : c27.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    have v20 : c27.get 20=832#32 := by simp [c9,c8,c7,c6,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_store,v8,v20,show 2164258836#32+744#32=sp+3948#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 987 (by decide +kernel)) (Memory.block_access stack (off := 3948) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t28 : Quiet.Step B img ⟨c28,r11⟩ ⟨c29,r12⟩ := by
    refine Quiet.step_of (by change (0x800019d8#32).getLsbD 0=false;decide) rt2147490264 fun o => ?_
    change Observed.interp B img o (exec c28 _ _) r11 0 [] [] = ⟨.ok c29 r12 [],[]⟩
    have v8 : c28.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    have v0 : c28.get 0=0#32 := by simp [c9,c8,c7,c6,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_store,v8,v0,show 2164258836#32+748#32=sp+3952#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3952) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t29 : Quiet.Step B img ⟨c29,r12⟩ ⟨c30,r13⟩ := by
    refine Quiet.step_of (by change (0x800019dc#32).getLsbD 0=false;decide) rt2147490268 fun o => ?_
    change Observed.interp B img o (exec c29 _ _) r12 0 [] [] = ⟨.ok c30 r13 [],[]⟩
    have v8 : c29.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    have v0 : c29.get 0=0#32 := by simp [c9,c8,c7,c6,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_store,v8,v0,show 2164258836#32+1620#32=sp+4824#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 4824) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t30 : Quiet.Step B img ⟨c30,r13⟩ ⟨c31,r13⟩ := by
    refine Quiet.step_of (by change (0x800019e0#32).getLsbD 0=false;decide) rt2147490272 fun o => ?_
    change Observed.interp B img o (exec c30 _ _) r13 0 [] [] = ⟨.ok c31 r13 [],[]⟩
    rw [exec_auipc];first | rfl | (rw [hp];rfl)
  have t31 : Quiet.Step B img ⟨c31,r13⟩ ⟨c32,r13⟩ := by
    refine Quiet.step_of (by change (0x800019e4#32).getLsbD 0=false;decide) rt2147490276 fun o => ?_
    change Observed.interp B img o (exec c31 _ _) r13 0 [] [] = ⟨.ok c32 r13 [],[]⟩
    have v1 : c31.get 1=2147490272#32 := by simp [c9,c8,c7,c6,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c31.set 1 2147490280#32) 2147491694#32) r13 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c32,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.step t23 (.step t24 (.step t25 (.step t26 (.step t27 (.step t28 (.step t29 (.step t30 (.single t31))))))))))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c9,c8,c7,c6,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
  · simp [c9,c8,c7,c6,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
  · simp [c9,c8,c7,c6,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
  · simp [c9,c8,c7,c6,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
  · simp [c9,c8,c7,c6,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
  · simp [c9,c8,c7,c6,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
  · simp [c9,c8,c7,c6,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
  · simp [c9,c8,c7,c6,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22]
  · intro reg h13 h10 h12 h20 h11 h9 h24 h1;simp [c9,c8,c7,c6,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h22,h13,h10,h12,h20,h11,h9,h24,h1]

/-- Live receive, App, response metadata and Request slices are outside the actual stores. -/
theorem frame (ram : Word → BitVec 8) (off size : Nat) (bound : off+size≤5232)
    (apart : off+size≤3680 ∨ (3684≤off ∧ off+size≤3916) ∨ (3957≤off ∧ off+size≤4824) ∨ 4825≤off) :
    ViewFrame.Region ram (memory ram) (sp+BitVec.ofNat 32 off) size := by
  intro i
  unfold memory
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    exact FrameOffsets.ne sp off 4824 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<1 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<1 at hj;rcases apart with h|h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    exact FrameOffsets.ne sp off 3952 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<1 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<1 at hj;rcases apart with h|h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3948 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3944 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3940 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3936 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3928 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3924 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3920 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3916 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3932 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    exact FrameOffsets.ne sp off 3956 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<1 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<1 at hj;rcases apart with h|h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3680 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h|h <;>omega))]

theorem params_count (ram : Word → BitVec 8) : ramRead (memory ram) (sp+3680#32) .w=0#32 := by
  unfold memory
  rw [FrameOffsets.word _ sp _ 3680 4824 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3952 .b (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3948 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3944 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3940 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3936 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3928 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3924 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3920 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3916 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3932 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3956 .b (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem actor (ram : Word → BitVec 8) : memory ram (sp+4824#32)=0#8 := by
  unfold memory
  change ramPut _ (sp+4824#32) 0#8 (sp+4824#32)=0#8
  exact ramPut_eq _ _ _
end E5R.Thermostat.StateHeadSetup
