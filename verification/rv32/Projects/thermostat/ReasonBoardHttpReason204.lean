import Projects.thermostat.HttpReason204
import Projects.thermostat.StackBoard
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.ReasonBoardHttpReason204
open E5R E5R.Thermostat HttpReason204
abbrev B := StackBoard.board

theorem contract (c : Core) (ram : Word → BitVec 8) (dst : Word) (h10 : c.get 10=dst) (h11 : c.get 11=192#32) (h12 : c.get 12=13#32) (h13 : c.get 13=204#32) (hm : Memory.Block B dst 192)
    (hp : c.pc=0x80003584#32) :
    ∃ d, Quiet.Steps B img 38 ⟨c,ram⟩ ⟨d,memory ram dst⟩ ∧ d.pc=c.get 1 &&& ~~~1 ∧
      d.get 14=(dst+13#32) ∧ d.get 15=101#32 ∧ d.get 10=1#32 ∧ d.get 11=23#32 ∧ d.get 13=116#32 ∧ d.get 12=23#32 ∧ (∀ r : Reg, r≠14 → r≠15 → r≠10 → r≠11 → r≠13 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (dst) 0x80003586#32
  let c2 := c1.wr 15 (408#32) 0x8000358a#32
  let c3 := c2.wr 10 (1#32) 0x8000358c#32
  let c4 := c3.goto 0x80003590#32
  let c5 := c4.wr 15 (400#32) 0x80003594#32
  let c6 := c5.goto 0x80003726#32
  let c7 := c6.wr 15 (203#32) 0x8000372a#32
  let c8 := c7.goto 0x8000382a#32
  let c9 := c8.wr 15 (204#32) 0x8000382e#32
  let c10 := c9.goto 0x80003aec#32
  let c11 := c10.wr 10 (179#32) 0x80003af0#32
  let c12 := c11.wr 11 (0#32) 0x80003af4#32
  let c13 := c12.wr 10 (0#32) 0x80003af8#32
  let c14 := c13.wr 10 (0#32) 0x80003afa#32
  let c15 := c14.goto 0x80003afe#32
  let c16 := c15.wr 14 ((dst+13#32)) 0x80003b00#32
  let c17 := c16.wr 10 (78#32) 0x80003b04#32
  let c18 := c17.wr 11 (111#32) 0x80003b08#32
  let c19 := c18.wr 13 (32#32) 0x80003b0c#32
  let c20 := c19.wr 15 (67#32) 0x80003b10#32
  let r1 := ramWrite ram (dst+13#32) (78#32) .b
  let c21 := c20.goto 0x80003b14#32
  let r2 := ramWrite r1 (dst+14#32) (111#32) .b
  let c22 := c21.goto 0x80003b18#32
  let r3 := ramWrite r2 (dst+15#32) (32#32) .b
  let c23 := c22.goto 0x80003b1c#32
  let r4 := ramWrite r3 (dst+16#32) (67#32) .b
  let c24 := c23.goto 0x80003b20#32
  let c25 := c24.wr 10 (110#32) 0x80003b24#32
  let c26 := c25.wr 13 (116#32) 0x80003b28#32
  let c27 := c26.wr 15 (101#32) 0x80003b2c#32
  let r5 := ramWrite r4 (dst+17#32) (111#32) .b
  let c28 := c27.goto 0x80003b30#32
  let r6 := ramWrite r5 (dst+18#32) (110#32) .b
  let c29 := c28.goto 0x80003b34#32
  let r7 := ramWrite r6 (dst+19#32) (116#32) .b
  let c30 := c29.goto 0x80003b38#32
  let r8 := ramWrite r7 (dst+20#32) (101#32) .b
  let c31 := c30.goto 0x80003b3c#32
  let r9 := ramWrite r8 (dst+21#32) (110#32) .b
  let c32 := c31.goto 0x80003b40#32
  let r10 := ramWrite r9 (dst+22#32) (116#32) .b
  let c33 := c32.goto 0x80003b44#32
  let c34 := c33.wr 12 (23#32) 0x80003b46#32
  let c35 := c34.goto 0x80003e48#32
  let c36 := c35.wr 10 (1#32) 0x80003e4a#32
  let c37 := c36.wr 11 (23#32) 0x80003e4c#32
  let c38 := c37.goto (c.get 1 &&& ~~~1)
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
    have v13 : c3.get 13=204#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by decide +kernel : taken .lt 408#32 204#32=false)]
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
    have v13 : c5.get 13=204#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by decide +kernel : taken .ge 400#32 204#32=true)]
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
    have v13 : c7.get 13=204#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by decide +kernel : taken .lt 203#32 204#32=true)]
    simp only [ite_true]
    rw [show c7.pc=2147497770#32 by rfl,show 2147497770#32+256#32=2147498026#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x8000382a#32).getLsbD 0=false;decide) rp2147498026 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c8.wr 15 (alu .add 0#32 204#32) 0x8000382e#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 204#32=204#32)];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x8000382e#32).getLsbD 0=false;decide) rp2147498030 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v13 : c9.get 13=204#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c9.get 15=204#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v13,v15,(by decide +kernel : taken .eq 204#32 204#32=true)]
    simp only [ite_true]
    rw [show c9.pc=2147498030#32 by rfl,show 2147498030#32+702#32=2147498732#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80003aec#32).getLsbD 0=false;decide) rp2147498732 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v11 : c10.get 11=192#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c10.get 12=13#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v11,v12]
    change Observed.interp B img o (.done (c10.wr 10 (alu .sub 192#32 13#32) 0x80003af0#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .sub 192#32 13#32=179#32)];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x80003af0#32).getLsbD 0=false;decide) rp2147498736 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v11 : c11.get 11=192#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c11.get 12=13#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v11,v12]
    change Observed.interp B img o (.done (c11.wr 11 (alu .sltu 192#32 13#32) 0x80003af4#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .sltu 192#32 13#32=0#32)];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x80003af4#32).getLsbD 0=false;decide) rp2147498740 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    have v10 : c12.get 10=179#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v10]
    change Observed.interp B img o (.done (c12.wr 10 (alu .sltu 179#32 10#32) 0x80003af8#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .sltu 179#32 10#32=0#32)];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine Quiet.step_of (by change (0x80003af8#32).getLsbD 0=false;decide) rp2147498744 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 ram [],[]⟩
    have v10 : c13.get 10=0#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c13.get 11=0#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v10,v11]
    change Observed.interp B img o (.done (c13.wr 10 (alu .or 0#32 0#32) 0x80003afa#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .or 0#32 0#32=0#32)];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine Quiet.step_of (by change (0x80003afa#32).getLsbD 0=false;decide) rp2147498746 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) ram 0 [] [] = ⟨.ok c15 ram [],[]⟩
    have v10 : c14.get 10=0#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v10,Core.get_zero,(by decide +kernel : taken .ne 0#32 (0 : Word)=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,ram⟩ ⟨c16,ram⟩ := by
    refine Quiet.step_of (by change (0x80003afe#32).getLsbD 0=false;decide) rp2147498750 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) ram 0 [] [] = ⟨.ok c16 ram [],[]⟩
    have v14 : c15.get 14=dst := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c15.get 12=13#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v14,v12]
    change Observed.interp B img o (.done (c15.wr 14 (alu .add dst 13#32) 0x80003b00#32)) ram 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : alu .add dst 13#32=(dst+13#32))];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,ram⟩ ⟨c17,ram⟩ := by
    refine Quiet.step_of (by change (0x80003b00#32).getLsbD 0=false;decide) rp2147498752 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) ram 0 [] [] = ⟨.ok c17 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c16.wr 10 (alu .add 0#32 78#32) 0x80003b04#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 78#32=78#32)];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,ram⟩ ⟨c18,ram⟩ := by
    refine Quiet.step_of (by change (0x80003b04#32).getLsbD 0=false;decide) rp2147498756 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) ram 0 [] [] = ⟨.ok c18 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c17.wr 11 (alu .add 0#32 111#32) 0x80003b08#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 111#32=111#32)];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,ram⟩ ⟨c19,ram⟩ := by
    refine Quiet.step_of (by change (0x80003b08#32).getLsbD 0=false;decide) rp2147498760 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) ram 0 [] [] = ⟨.ok c19 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c18.wr 13 (alu .add 0#32 32#32) 0x80003b0c#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 32#32=32#32)];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,ram⟩ ⟨c20,ram⟩ := by
    refine Quiet.step_of (by change (0x80003b0c#32).getLsbD 0=false;decide) rp2147498764 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) ram 0 [] [] = ⟨.ok c20 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c19.wr 15 (alu .add 0#32 67#32) 0x80003b10#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 67#32=67#32)];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,ram⟩ ⟨c21,r1⟩ := by
    refine Quiet.step_of (by change (0x80003b10#32).getLsbD 0=false;decide) rp2147498768 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) ram 0 [] [] = ⟨.ok c21 r1 [],[]⟩
    have v14 : c20.get 14=(dst+13#32) := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v10 : c20.get 10=78#32 := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v10]
    change Observed.interp B img o (.store .b ((dst+13#32)+0#32) 78#32 false (.done (c20.goto 0x80003b14#32))) ram 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+0#32=dst+13#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 13) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,r1⟩ ⟨c22,r2⟩ := by
    refine Quiet.step_of (by change (0x80003b14#32).getLsbD 0=false;decide) rp2147498772 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) r1 0 [] [] = ⟨.ok c22 r2 [],[]⟩
    have v14 : c21.get 14=(dst+13#32) := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c21.get 11=111#32 := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v11]
    change Observed.interp B img o (.store .b ((dst+13#32)+1#32) 111#32 false (.done (c21.goto 0x80003b18#32))) r1 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+1#32=dst+14#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 14) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,r2⟩ ⟨c23,r3⟩ := by
    refine Quiet.step_of (by change (0x80003b18#32).getLsbD 0=false;decide) rp2147498776 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) r2 0 [] [] = ⟨.ok c23 r3 [],[]⟩
    have v14 : c22.get 14=(dst+13#32) := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c22.get 13=32#32 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+13#32)+2#32) 32#32 false (.done (c22.goto 0x80003b1c#32))) r2 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+2#32=dst+15#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 15) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t23 : Quiet.Step B img ⟨c23,r3⟩ ⟨c24,r4⟩ := by
    refine Quiet.step_of (by change (0x80003b1c#32).getLsbD 0=false;decide) rp2147498780 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) r3 0 [] [] = ⟨.ok c24 r4 [],[]⟩
    have v14 : c23.get 14=(dst+13#32) := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c23.get 15=67#32 := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v15]
    change Observed.interp B img o (.store .b ((dst+13#32)+3#32) 67#32 false (.done (c23.goto 0x80003b20#32))) r3 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+3#32=dst+16#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 16) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t24 : Quiet.Step B img ⟨c24,r4⟩ ⟨c25,r4⟩ := by
    refine Quiet.step_of (by change (0x80003b20#32).getLsbD 0=false;decide) rp2147498784 fun o => ?_
    change Observed.interp B img o (exec c24 _ _) r4 0 [] [] = ⟨.ok c25 r4 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c24.wr 10 (alu .add 0#32 110#32) 0x80003b24#32)) r4 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 110#32=110#32)];first | rfl | (rw [hp];rfl)
  have t25 : Quiet.Step B img ⟨c25,r4⟩ ⟨c26,r4⟩ := by
    refine Quiet.step_of (by change (0x80003b24#32).getLsbD 0=false;decide) rp2147498788 fun o => ?_
    change Observed.interp B img o (exec c25 _ _) r4 0 [] [] = ⟨.ok c26 r4 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c25.wr 13 (alu .add 0#32 116#32) 0x80003b28#32)) r4 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 116#32=116#32)];first | rfl | (rw [hp];rfl)
  have t26 : Quiet.Step B img ⟨c26,r4⟩ ⟨c27,r4⟩ := by
    refine Quiet.step_of (by change (0x80003b28#32).getLsbD 0=false;decide) rp2147498792 fun o => ?_
    change Observed.interp B img o (exec c26 _ _) r4 0 [] [] = ⟨.ok c27 r4 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c26.wr 15 (alu .add 0#32 101#32) 0x80003b2c#32)) r4 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 101#32=101#32)];first | rfl | (rw [hp];rfl)
  have t27 : Quiet.Step B img ⟨c27,r4⟩ ⟨c28,r5⟩ := by
    refine Quiet.step_of (by change (0x80003b2c#32).getLsbD 0=false;decide) rp2147498796 fun o => ?_
    change Observed.interp B img o (exec c27 _ _) r4 0 [] [] = ⟨.ok c28 r5 [],[]⟩
    have v14 : c27.get 14=(dst+13#32) := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c27.get 11=111#32 := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v11]
    change Observed.interp B img o (.store .b ((dst+13#32)+4#32) 111#32 false (.done (c27.goto 0x80003b30#32))) r4 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+4#32=dst+17#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 17) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t28 : Quiet.Step B img ⟨c28,r5⟩ ⟨c29,r6⟩ := by
    refine Quiet.step_of (by change (0x80003b30#32).getLsbD 0=false;decide) rp2147498800 fun o => ?_
    change Observed.interp B img o (exec c28 _ _) r5 0 [] [] = ⟨.ok c29 r6 [],[]⟩
    have v14 : c28.get 14=(dst+13#32) := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v10 : c28.get 10=110#32 := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v10]
    change Observed.interp B img o (.store .b ((dst+13#32)+5#32) 110#32 false (.done (c28.goto 0x80003b34#32))) r5 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+5#32=dst+18#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 18) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t29 : Quiet.Step B img ⟨c29,r6⟩ ⟨c30,r7⟩ := by
    refine Quiet.step_of (by change (0x80003b34#32).getLsbD 0=false;decide) rp2147498804 fun o => ?_
    change Observed.interp B img o (exec c29 _ _) r6 0 [] [] = ⟨.ok c30 r7 [],[]⟩
    have v14 : c29.get 14=(dst+13#32) := by simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c29.get 13=116#32 := by simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+13#32)+6#32) 116#32 false (.done (c29.goto 0x80003b38#32))) r6 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+6#32=dst+19#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 19) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t30 : Quiet.Step B img ⟨c30,r7⟩ ⟨c31,r8⟩ := by
    refine Quiet.step_of (by change (0x80003b38#32).getLsbD 0=false;decide) rp2147498808 fun o => ?_
    change Observed.interp B img o (exec c30 _ _) r7 0 [] [] = ⟨.ok c31 r8 [],[]⟩
    have v14 : c30.get 14=(dst+13#32) := by simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c30.get 15=101#32 := by simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v15]
    change Observed.interp B img o (.store .b ((dst+13#32)+7#32) 101#32 false (.done (c30.goto 0x80003b3c#32))) r7 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+7#32=dst+20#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 20) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t31 : Quiet.Step B img ⟨c31,r8⟩ ⟨c32,r9⟩ := by
    refine Quiet.step_of (by change (0x80003b3c#32).getLsbD 0=false;decide) rp2147498812 fun o => ?_
    change Observed.interp B img o (exec c31 _ _) r8 0 [] [] = ⟨.ok c32 r9 [],[]⟩
    have v14 : c31.get 14=(dst+13#32) := by simp [c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v10 : c31.get 10=110#32 := by simp [c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v10]
    change Observed.interp B img o (.store .b ((dst+13#32)+8#32) 110#32 false (.done (c31.goto 0x80003b40#32))) r8 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+8#32=dst+21#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 21) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t32 : Quiet.Step B img ⟨c32,r9⟩ ⟨c33,r10⟩ := by
    refine Quiet.step_of (by change (0x80003b40#32).getLsbD 0=false;decide) rp2147498816 fun o => ?_
    change Observed.interp B img o (exec c32 _ _) r9 0 [] [] = ⟨.ok c33 r10 [],[]⟩
    have v14 : c32.get 14=(dst+13#32) := by simp [c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c32.get 13=116#32 := by simp [c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+13#32)+9#32) 116#32 false (.done (c32.goto 0x80003b44#32))) r9 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+9#32=dst+22#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 22) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t33 : Quiet.Step B img ⟨c33,r10⟩ ⟨c34,r10⟩ := by
    refine Quiet.step_of (by change (0x80003b44#32).getLsbD 0=false;decide) rp2147498820 fun o => ?_
    change Observed.interp B img o (exec c33 _ _) r10 0 [] [] = ⟨.ok c34 r10 [],[]⟩
    have v12 : c33.get 12=13#32 := by simp [c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v12]
    change Observed.interp B img o (.done (c33.wr 12 (alu .add 13#32 10#32) 0x80003b46#32)) r10 0 [] [] = _
    rw [(by decide +kernel : alu .add 13#32 10#32=23#32)];first | rfl | (rw [hp];rfl)
  have t34 : Quiet.Step B img ⟨c34,r10⟩ ⟨c35,r10⟩ := by
    refine Quiet.step_of (by change (0x80003b46#32).getLsbD 0=false;decide) rp2147498822 fun o => ?_
    change Observed.interp B img o (exec c34 _ _) r10 0 [] [] = ⟨.ok c35 r10 [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c34 (2147498822#32+770#32)) r10 0 [] [] = _
    rw [show 2147498822#32+770#32=2147499592#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t35 : Quiet.Step B img ⟨c35,r10⟩ ⟨c36,r10⟩ := by
    refine Quiet.step_of (by change (0x80003e48#32).getLsbD 0=false;decide) rp2147499592 fun o => ?_
    change Observed.interp B img o (exec c35 _ _) r10 0 [] [] = ⟨.ok c36 r10 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c35.wr 10 (alu .add 0#32 1#32) 0x80003e4a#32)) r10 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 1#32=1#32)];first | rfl | (rw [hp];rfl)
  have t36 : Quiet.Step B img ⟨c36,r10⟩ ⟨c37,r10⟩ := by
    refine Quiet.step_of (by change (0x80003e4a#32).getLsbD 0=false;decide) rp2147499594 fun o => ?_
    change Observed.interp B img o (exec c36 _ _) r10 0 [] [] = ⟨.ok c37 r10 [],[]⟩
    have v12 : c36.get 12=23#32 := by simp [c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,Core.get_zero,v12]
    change Observed.interp B img o (.done (c36.wr 11 (alu .add 0#32 23#32) 0x80003e4c#32)) r10 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 23#32=23#32)];first | rfl | (rw [hp];rfl)
  have t37 : Quiet.Step B img ⟨c37,r10⟩ ⟨c38,r10⟩ := by
    refine Quiet.step_of (by change (0x80003e4c#32).getLsbD 0=false;decide) rp2147499596 fun o => ?_
    change Observed.interp B img o (exec c37 _ _) r10 0 [] [] = ⟨.ok c38 r10 [],[]⟩
    have v1 : c37.get 1=c.get 1 := by simp [c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_jalr,v1,BitVec.add_zero]
    change Observed.interp B img o (jump c37 (c.get 1 &&& ~~~1)) r10 0 [] [] = _
    rw [jump_ok _ _ (clear_bit0 _)];first | rfl | (rw [hp];rfl)
  refine ⟨c38,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.step t23 (.step t24 (.step t25 (.step t26 (.step t27 (.step t28 (.step t29 (.step t30 (.step t31 (.step t32 (.step t33 (.step t34 (.step t35 (.step t36 (.single t37))))))))))))))))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · intro reg h14 h15 h10 h11 h13 h12;simp [c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15,h10,h11,h13,h12]
end E5R.Thermostat.ReasonBoardHttpReason204
