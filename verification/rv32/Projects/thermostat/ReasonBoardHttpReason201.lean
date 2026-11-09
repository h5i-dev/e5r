import Projects.thermostat.HttpReason201
import Projects.thermostat.StackBoard
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.ReasonBoardHttpReason201
open E5R E5R.Thermostat HttpReason201
abbrev B := StackBoard.board

theorem contract (c : Core) (ram : Word → BitVec 8) (dst : Word) (h10 : c.get 10=dst) (h11 : c.get 11=192#32) (h12 : c.get 12=13#32) (h13 : c.get 13=201#32) (hm : Memory.Block B dst 192)
    (hp : c.pc=0x80003584#32) :
    ∃ d, Quiet.Steps B img 36 ⟨c,ram⟩ ⟨d,memory ram dst⟩ ∧ d.pc=c.get 1 &&& ~~~1 ∧
      d.get 14=(dst+13#32) ∧ d.get 15=97#32 ∧ d.get 10=1#32 ∧ d.get 11=20#32 ∧ d.get 13=101#32 ∧ d.get 12=20#32 ∧ (∀ r : Reg, r≠14 → r≠15 → r≠10 → r≠11 → r≠13 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (dst) 0x80003586#32
  let c2 := c1.wr 15 (408#32) 0x8000358a#32
  let c3 := c2.wr 10 (1#32) 0x8000358c#32
  let c4 := c3.goto 0x80003590#32
  let c5 := c4.wr 15 (400#32) 0x80003594#32
  let c6 := c5.goto 0x80003726#32
  let c7 := c6.wr 15 (203#32) 0x8000372a#32
  let c8 := c7.goto 0x8000372e#32
  let c9 := c8.wr 15 (200#32) 0x80003732#32
  let c10 := c9.goto 0x80003736#32
  let c11 := c10.wr 15 (201#32) 0x8000373a#32
  let c12 := c11.goto 0x8000373e#32
  let c13 := c12.wr 10 (179#32) 0x80003742#32
  let c14 := c13.wr 11 (0#32) 0x80003746#32
  let c15 := c14.wr 10 (0#32) 0x8000374a#32
  let c16 := c15.wr 10 (0#32) 0x8000374c#32
  let c17 := c16.goto 0x80003750#32
  let c18 := c17.wr 14 ((dst+13#32)) 0x80003752#32
  let c19 := c18.wr 10 (67#32) 0x80003756#32
  let c20 := c19.wr 11 (114#32) 0x8000375a#32
  let c21 := c20.wr 13 (101#32) 0x8000375e#32
  let c22 := c21.wr 15 (97#32) 0x80003762#32
  let r1 := ramWrite ram (dst+13#32) (67#32) .b
  let c23 := c22.goto 0x80003766#32
  let r2 := ramWrite r1 (dst+14#32) (114#32) .b
  let c24 := c23.goto 0x8000376a#32
  let r3 := ramWrite r2 (dst+15#32) (101#32) .b
  let c25 := c24.goto 0x8000376e#32
  let r4 := ramWrite r3 (dst+16#32) (97#32) .b
  let c26 := c25.goto 0x80003772#32
  let c27 := c26.wr 10 (116#32) 0x80003776#32
  let c28 := c27.wr 11 (100#32) 0x8000377a#32
  let r5 := ramWrite r4 (dst+17#32) (116#32) .b
  let c29 := c28.goto 0x8000377e#32
  let r6 := ramWrite r5 (dst+18#32) (101#32) .b
  let c30 := c29.goto 0x80003782#32
  let r7 := ramWrite r6 (dst+19#32) (100#32) .b
  let c31 := c30.goto 0x80003786#32
  let c32 := c31.wr 12 (20#32) 0x80003788#32
  let c33 := c32.goto 0x80003e48#32
  let c34 := c33.wr 10 (1#32) 0x80003e4a#32
  let c35 := c34.wr 11 (20#32) 0x80003e4c#32
  let c36 := c35.goto (c.get 1 &&& ~~~1)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rp2147497348) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v10 : c.get 10=dst := by simp [Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,Core.get_zero,v10]
    rw [hp]
    change Observed.interp B img o (.done (c.wr 14 (alu .add 0#32 dst) 0x80003586#32)) ram 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : alu .add 0#32 dst=dst)];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003586#32).getLsbD 0=false;decide) rp2147497350 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c1.wr 15 (alu .add 0#32 408#32) 0x8000358a#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 408#32=408#32)];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000358a#32).getLsbD 0=false;decide) rp2147497354 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c2.wr 10 (alu .add 0#32 1#32) 0x8000358c#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 1#32=1#32)];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x8000358c#32).getLsbD 0=false;decide) rp2147497356 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v15 : c3.get 15=408#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c3.get 13=201#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by decide +kernel : taken .lt 408#32 201#32=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80003590#32).getLsbD 0=false;decide) rp2147497360 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c4.wr 15 (alu .add 0#32 400#32) 0x80003594#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 400#32=400#32)];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80003594#32).getLsbD 0=false;decide) rp2147497364 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v15 : c5.get 15=400#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c5.get 13=201#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by decide +kernel : taken .ge 400#32 201#32=true)]
    simp only [ite_true]
    rw [show c5.pc=2147497364#32 by rfl,show 2147497364#32+402#32=2147497766#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80003726#32).getLsbD 0=false;decide) rp2147497766 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c6.wr 15 (alu .add 0#32 203#32) 0x8000372a#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 203#32=203#32)];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x8000372a#32).getLsbD 0=false;decide) rp2147497770 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v15 : c7.get 15=203#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c7.get 13=201#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by decide +kernel : taken .lt 203#32 201#32=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x8000372e#32).getLsbD 0=false;decide) rp2147497774 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c8.wr 15 (alu .add 0#32 200#32) 0x80003732#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 200#32=200#32)];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80003732#32).getLsbD 0=false;decide) rp2147497778 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v13 : c9.get 13=201#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c9.get 15=200#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v13,v15,(by decide +kernel : taken .eq 201#32 200#32=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80003736#32).getLsbD 0=false;decide) rp2147497782 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c10.wr 15 (alu .add 0#32 201#32) 0x8000373a#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 201#32=201#32)];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x8000373a#32).getLsbD 0=false;decide) rp2147497786 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v13 : c11.get 13=201#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c11.get 15=201#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v13,v15,(by decide +kernel : taken .ne 201#32 201#32=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x8000373e#32).getLsbD 0=false;decide) rp2147497790 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    have v11 : c12.get 11=192#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c12.get 12=13#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v11,v12]
    change Observed.interp B img o (.done (c12.wr 10 (alu .sub 192#32 13#32) 0x80003742#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .sub 192#32 13#32=179#32)];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine Quiet.step_of (by change (0x80003742#32).getLsbD 0=false;decide) rp2147497794 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 ram [],[]⟩
    have v11 : c13.get 11=192#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c13.get 12=13#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v11,v12]
    change Observed.interp B img o (.done (c13.wr 11 (alu .sltu 192#32 13#32) 0x80003746#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .sltu 192#32 13#32=0#32)];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine Quiet.step_of (by change (0x80003746#32).getLsbD 0=false;decide) rp2147497798 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) ram 0 [] [] = ⟨.ok c15 ram [],[]⟩
    have v10 : c14.get 10=179#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v10]
    change Observed.interp B img o (.done (c14.wr 10 (alu .sltu 179#32 7#32) 0x8000374a#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .sltu 179#32 7#32=0#32)];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,ram⟩ ⟨c16,ram⟩ := by
    refine Quiet.step_of (by change (0x8000374a#32).getLsbD 0=false;decide) rp2147497802 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) ram 0 [] [] = ⟨.ok c16 ram [],[]⟩
    have v10 : c15.get 10=0#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c15.get 11=0#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v10,v11]
    change Observed.interp B img o (.done (c15.wr 10 (alu .or 0#32 0#32) 0x8000374c#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .or 0#32 0#32=0#32)];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,ram⟩ ⟨c17,ram⟩ := by
    refine Quiet.step_of (by change (0x8000374c#32).getLsbD 0=false;decide) rp2147497804 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) ram 0 [] [] = ⟨.ok c17 ram [],[]⟩
    have v10 : c16.get 10=0#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v10,Core.get_zero,(by decide +kernel : taken .ne 0#32 (0 : Word)=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,ram⟩ ⟨c18,ram⟩ := by
    refine Quiet.step_of (by change (0x80003750#32).getLsbD 0=false;decide) rp2147497808 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) ram 0 [] [] = ⟨.ok c18 ram [],[]⟩
    have v14 : c17.get 14=dst := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c17.get 12=13#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v14,v12]
    change Observed.interp B img o (.done (c17.wr 14 (alu .add dst 13#32) 0x80003752#32)) ram 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : alu .add dst 13#32=(dst+13#32))];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,ram⟩ ⟨c19,ram⟩ := by
    refine Quiet.step_of (by change (0x80003752#32).getLsbD 0=false;decide) rp2147497810 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) ram 0 [] [] = ⟨.ok c19 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c18.wr 10 (alu .add 0#32 67#32) 0x80003756#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 67#32=67#32)];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,ram⟩ ⟨c20,ram⟩ := by
    refine Quiet.step_of (by change (0x80003756#32).getLsbD 0=false;decide) rp2147497814 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) ram 0 [] [] = ⟨.ok c20 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c19.wr 11 (alu .add 0#32 114#32) 0x8000375a#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 114#32=114#32)];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,ram⟩ ⟨c21,ram⟩ := by
    refine Quiet.step_of (by change (0x8000375a#32).getLsbD 0=false;decide) rp2147497818 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) ram 0 [] [] = ⟨.ok c21 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c20.wr 13 (alu .add 0#32 101#32) 0x8000375e#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 101#32=101#32)];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,ram⟩ ⟨c22,ram⟩ := by
    refine Quiet.step_of (by change (0x8000375e#32).getLsbD 0=false;decide) rp2147497822 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) ram 0 [] [] = ⟨.ok c22 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c21.wr 15 (alu .add 0#32 97#32) 0x80003762#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 97#32=97#32)];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,ram⟩ ⟨c23,r1⟩ := by
    refine Quiet.step_of (by change (0x80003762#32).getLsbD 0=false;decide) rp2147497826 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) ram 0 [] [] = ⟨.ok c23 r1 [],[]⟩
    have v14 : c22.get 14=(dst+13#32) := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v10 : c22.get 10=67#32 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v10]
    change Observed.interp B img o (.store .b ((dst+13#32)+0#32) 67#32 false (.done (c22.goto 0x80003766#32))) ram 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+0#32=dst+13#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 13) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t23 : Quiet.Step B img ⟨c23,r1⟩ ⟨c24,r2⟩ := by
    refine Quiet.step_of (by change (0x80003766#32).getLsbD 0=false;decide) rp2147497830 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) r1 0 [] [] = ⟨.ok c24 r2 [],[]⟩
    have v14 : c23.get 14=(dst+13#32) := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c23.get 11=114#32 := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v11]
    change Observed.interp B img o (.store .b ((dst+13#32)+1#32) 114#32 false (.done (c23.goto 0x8000376a#32))) r1 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+1#32=dst+14#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 14) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t24 : Quiet.Step B img ⟨c24,r2⟩ ⟨c25,r3⟩ := by
    refine Quiet.step_of (by change (0x8000376a#32).getLsbD 0=false;decide) rp2147497834 fun o => ?_
    change Observed.interp B img o (exec c24 _ _) r2 0 [] [] = ⟨.ok c25 r3 [],[]⟩
    have v14 : c24.get 14=(dst+13#32) := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c24.get 13=101#32 := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+13#32)+2#32) 101#32 false (.done (c24.goto 0x8000376e#32))) r2 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+2#32=dst+15#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 15) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t25 : Quiet.Step B img ⟨c25,r3⟩ ⟨c26,r4⟩ := by
    refine Quiet.step_of (by change (0x8000376e#32).getLsbD 0=false;decide) rp2147497838 fun o => ?_
    change Observed.interp B img o (exec c25 _ _) r3 0 [] [] = ⟨.ok c26 r4 [],[]⟩
    have v14 : c25.get 14=(dst+13#32) := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c25.get 15=97#32 := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v15]
    change Observed.interp B img o (.store .b ((dst+13#32)+3#32) 97#32 false (.done (c25.goto 0x80003772#32))) r3 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+3#32=dst+16#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 16) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t26 : Quiet.Step B img ⟨c26,r4⟩ ⟨c27,r4⟩ := by
    refine Quiet.step_of (by change (0x80003772#32).getLsbD 0=false;decide) rp2147497842 fun o => ?_
    change Observed.interp B img o (exec c26 _ _) r4 0 [] [] = ⟨.ok c27 r4 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c26.wr 10 (alu .add 0#32 116#32) 0x80003776#32)) r4 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 116#32=116#32)];first | rfl | (rw [hp];rfl)
  have t27 : Quiet.Step B img ⟨c27,r4⟩ ⟨c28,r4⟩ := by
    refine Quiet.step_of (by change (0x80003776#32).getLsbD 0=false;decide) rp2147497846 fun o => ?_
    change Observed.interp B img o (exec c27 _ _) r4 0 [] [] = ⟨.ok c28 r4 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c27.wr 11 (alu .add 0#32 100#32) 0x8000377a#32)) r4 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 100#32=100#32)];first | rfl | (rw [hp];rfl)
  have t28 : Quiet.Step B img ⟨c28,r4⟩ ⟨c29,r5⟩ := by
    refine Quiet.step_of (by change (0x8000377a#32).getLsbD 0=false;decide) rp2147497850 fun o => ?_
    change Observed.interp B img o (exec c28 _ _) r4 0 [] [] = ⟨.ok c29 r5 [],[]⟩
    have v14 : c28.get 14=(dst+13#32) := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v10 : c28.get 10=116#32 := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v10]
    change Observed.interp B img o (.store .b ((dst+13#32)+4#32) 116#32 false (.done (c28.goto 0x8000377e#32))) r4 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+4#32=dst+17#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 17) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t29 : Quiet.Step B img ⟨c29,r5⟩ ⟨c30,r6⟩ := by
    refine Quiet.step_of (by change (0x8000377e#32).getLsbD 0=false;decide) rp2147497854 fun o => ?_
    change Observed.interp B img o (exec c29 _ _) r5 0 [] [] = ⟨.ok c30 r6 [],[]⟩
    have v14 : c29.get 14=(dst+13#32) := by simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c29.get 13=101#32 := by simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+13#32)+5#32) 101#32 false (.done (c29.goto 0x80003782#32))) r5 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+5#32=dst+18#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 18) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t30 : Quiet.Step B img ⟨c30,r6⟩ ⟨c31,r7⟩ := by
    refine Quiet.step_of (by change (0x80003782#32).getLsbD 0=false;decide) rp2147497858 fun o => ?_
    change Observed.interp B img o (exec c30 _ _) r6 0 [] [] = ⟨.ok c31 r7 [],[]⟩
    have v14 : c30.get 14=(dst+13#32) := by simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c30.get 11=100#32 := by simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v11]
    change Observed.interp B img o (.store .b ((dst+13#32)+6#32) 100#32 false (.done (c30.goto 0x80003786#32))) r6 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+6#32=dst+19#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 19) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t31 : Quiet.Step B img ⟨c31,r7⟩ ⟨c32,r7⟩ := by
    refine Quiet.step_of (by change (0x80003786#32).getLsbD 0=false;decide) rp2147497862 fun o => ?_
    change Observed.interp B img o (exec c31 _ _) r7 0 [] [] = ⟨.ok c32 r7 [],[]⟩
    have v12 : c31.get 12=13#32 := by simp [c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v12]
    change Observed.interp B img o (.done (c31.wr 12 (alu .add 13#32 7#32) 0x80003788#32)) r7 0 [] [] = _
    rw [(by decide +kernel : alu .add 13#32 7#32=20#32)];first | rfl | (rw [hp];rfl)
  have t32 : Quiet.Step B img ⟨c32,r7⟩ ⟨c33,r7⟩ := by
    refine Quiet.step_of (by change (0x80003788#32).getLsbD 0=false;decide) rp2147497864 fun o => ?_
    change Observed.interp B img o (exec c32 _ _) r7 0 [] [] = ⟨.ok c33 r7 [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c32 (2147497864#32+1728#32)) r7 0 [] [] = _
    rw [show 2147497864#32+1728#32=2147499592#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t33 : Quiet.Step B img ⟨c33,r7⟩ ⟨c34,r7⟩ := by
    refine Quiet.step_of (by change (0x80003e48#32).getLsbD 0=false;decide) rp2147499592 fun o => ?_
    change Observed.interp B img o (exec c33 _ _) r7 0 [] [] = ⟨.ok c34 r7 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c33.wr 10 (alu .add 0#32 1#32) 0x80003e4a#32)) r7 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 1#32=1#32)];first | rfl | (rw [hp];rfl)
  have t34 : Quiet.Step B img ⟨c34,r7⟩ ⟨c35,r7⟩ := by
    refine Quiet.step_of (by change (0x80003e4a#32).getLsbD 0=false;decide) rp2147499594 fun o => ?_
    change Observed.interp B img o (exec c34 _ _) r7 0 [] [] = ⟨.ok c35 r7 [],[]⟩
    have v12 : c34.get 12=20#32 := by simp [c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,Core.get_zero,v12]
    change Observed.interp B img o (.done (c34.wr 11 (alu .add 0#32 20#32) 0x80003e4c#32)) r7 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 20#32=20#32)];first | rfl | (rw [hp];rfl)
  have t35 : Quiet.Step B img ⟨c35,r7⟩ ⟨c36,r7⟩ := by
    refine Quiet.step_of (by change (0x80003e4c#32).getLsbD 0=false;decide) rp2147499596 fun o => ?_
    change Observed.interp B img o (exec c35 _ _) r7 0 [] [] = ⟨.ok c36 r7 [],[]⟩
    have v1 : c35.get 1=c.get 1 := by simp [c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_jalr,v1,BitVec.add_zero]
    change Observed.interp B img o (jump c35 (c.get 1 &&& ~~~1)) r7 0 [] [] = _
    rw [jump_ok _ _ (clear_bit0 _)];first | rfl | (rw [hp];rfl)
  refine ⟨c36,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.step t23 (.step t24 (.step t25 (.step t26 (.step t27 (.step t28 (.step t29 (.step t30 (.step t31 (.step t32 (.step t33 (.step t34 (.single t35))))))))))))))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · intro reg h14 h15 h10 h11 h13 h12;simp [c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15,h10,h11,h13,h12]
end E5R.Thermostat.ReasonBoardHttpReason201
