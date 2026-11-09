import Projects.thermostat.HttpReason501
import Projects.thermostat.StackBoard
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.ReasonBoardHttpReason501
open E5R E5R.Thermostat HttpReason501
abbrev B := StackBoard.board

theorem contract (c : Core) (ram : Word → BitVec 8) (dst : Word) (h10 : c.get 10=dst) (h11 : c.get 11=192#32) (h12 : c.get 12=13#32) (h13 : c.get 13=501#32) (hm : Memory.Block B dst 192)
    (hp : c.pc=0x80003584#32) :
    ∃ d, Quiet.Steps B img 47 ⟨c,ram⟩ ⟨d,memory ram dst⟩ ∧ d.pc=c.get 1 &&& ~~~1 ∧
      d.get 14=(dst+13#32) ∧ d.get 15=110#32 ∧ d.get 10=1#32 ∧ d.get 11=28#32 ∧ d.get 13=116#32 ∧ d.get 16=108#32 ∧ d.get 12=28#32 ∧ (∀ r : Reg, r≠14 → r≠15 → r≠10 → r≠11 → r≠13 → r≠16 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (dst) 0x80003586#32
  let c2 := c1.wr 15 (408#32) 0x8000358a#32
  let c3 := c2.wr 10 (1#32) 0x8000358c#32
  let c4 := c3.goto 0x8000363a#32
  let c5 := c4.wr 15 (430#32) 0x8000363e#32
  let c6 := c5.goto 0x80003642#32
  let c7 := c6.wr 15 (500#32) 0x80003646#32
  let c8 := c7.goto 0x8000364a#32
  let c9 := c8.wr 15 (501#32) 0x8000364e#32
  let c10 := c9.goto 0x80003d1e#32
  let c11 := c10.wr 10 (179#32) 0x80003d22#32
  let c12 := c11.wr 11 (0#32) 0x80003d26#32
  let c13 := c12.wr 10 (0#32) 0x80003d2a#32
  let c14 := c13.wr 10 (0#32) 0x80003d2c#32
  let c15 := c14.goto 0x80003d2e#32
  let c16 := c15.wr 14 ((dst+13#32)) 0x80003d30#32
  let c17 := c16.wr 10 (78#32) 0x80003d34#32
  let c18 := c17.wr 11 (111#32) 0x80003d38#32
  let c19 := c18.wr 13 (116#32) 0x80003d3c#32
  let c20 := c19.wr 15 (32#32) 0x80003d40#32
  let r1 := ramWrite ram (dst+13#32) (78#32) .b
  let c21 := c20.goto 0x80003d44#32
  let r2 := ramWrite r1 (dst+14#32) (111#32) .b
  let c22 := c21.goto 0x80003d48#32
  let r3 := ramWrite r2 (dst+15#32) (116#32) .b
  let c23 := c22.goto 0x80003d4c#32
  let r4 := ramWrite r3 (dst+16#32) (32#32) .b
  let c24 := c23.goto 0x80003d50#32
  let c25 := c24.wr 10 (73#32) 0x80003d54#32
  let c26 := c25.wr 11 (109#32) 0x80003d58#32
  let c27 := c26.wr 15 (112#32) 0x80003d5c#32
  let c28 := c27.wr 16 (108#32) 0x80003d60#32
  let r5 := ramWrite r4 (dst+17#32) (73#32) .b
  let c29 := c28.goto 0x80003d64#32
  let r6 := ramWrite r5 (dst+18#32) (109#32) .b
  let c30 := c29.goto 0x80003d68#32
  let r7 := ramWrite r6 (dst+19#32) (112#32) .b
  let c31 := c30.goto 0x80003d6c#32
  let r8 := ramWrite r7 (dst+20#32) (108#32) .b
  let c32 := c31.goto 0x80003d70#32
  let c33 := c32.wr 10 (101#32) 0x80003d74#32
  let c34 := c33.wr 15 (110#32) 0x80003d78#32
  let r9 := ramWrite r8 (dst+21#32) (101#32) .b
  let c35 := c34.goto 0x80003d7c#32
  let r10 := ramWrite r9 (dst+22#32) (109#32) .b
  let c36 := c35.goto 0x80003d80#32
  let r11 := ramWrite r10 (dst+23#32) (101#32) .b
  let c37 := c36.goto 0x80003d84#32
  let r12 := ramWrite r11 (dst+24#32) (110#32) .b
  let c38 := c37.goto 0x80003d88#32
  let c39 := c38.wr 11 (100#32) 0x80003d8c#32
  let r13 := ramWrite r12 (dst+25#32) (116#32) .b
  let c40 := c39.goto 0x80003d90#32
  let r14 := ramWrite r13 (dst+26#32) (101#32) .b
  let c41 := c40.goto 0x80003d94#32
  let r15 := ramWrite r14 (dst+27#32) (100#32) .b
  let c42 := c41.goto 0x80003d98#32
  let c43 := c42.wr 12 (28#32) 0x80003d9a#32
  let c44 := c43.goto 0x80003e48#32
  let c45 := c44.wr 10 (1#32) 0x80003e4a#32
  let c46 := c45.wr 11 (28#32) 0x80003e4c#32
  let c47 := c46.goto (c.get 1 &&& ~~~1)
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
    have v13 : c3.get 13=501#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by decide +kernel : taken .lt 408#32 501#32=true)]
    simp only [ite_true]
    rw [show c3.pc=2147497356#32 by rfl,show 2147497356#32+174#32=2147497530#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x8000363a#32).getLsbD 0=false;decide) rp2147497530 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c4.wr 15 (alu .add 0#32 430#32) 0x8000363e#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 430#32=430#32)];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x8000363e#32).getLsbD 0=false;decide) rp2147497534 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v15 : c5.get 15=430#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c5.get 13=501#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by decide +kernel : taken .ge 430#32 501#32=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80003642#32).getLsbD 0=false;decide) rp2147497538 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c6.wr 15 (alu .add 0#32 500#32) 0x80003646#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 500#32=500#32)];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80003646#32).getLsbD 0=false;decide) rp2147497542 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v15 : c7.get 15=500#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c7.get 13=501#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by decide +kernel : taken .ge 500#32 501#32=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x8000364a#32).getLsbD 0=false;decide) rp2147497546 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c8.wr 15 (alu .add 0#32 501#32) 0x8000364e#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 501#32=501#32)];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x8000364e#32).getLsbD 0=false;decide) rp2147497550 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v13 : c9.get 13=501#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c9.get 15=501#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v13,v15,(by decide +kernel : taken .eq 501#32 501#32=true)]
    simp only [ite_true]
    rw [show c9.pc=2147497550#32 by rfl,show 2147497550#32+1744#32=2147499294#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80003d1e#32).getLsbD 0=false;decide) rp2147499294 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v11 : c10.get 11=192#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c10.get 12=13#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v11,v12]
    change Observed.interp B img o (.done (c10.wr 10 (alu .sub 192#32 13#32) 0x80003d22#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .sub 192#32 13#32=179#32)];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x80003d22#32).getLsbD 0=false;decide) rp2147499298 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v11 : c11.get 11=192#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c11.get 12=13#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v11,v12]
    change Observed.interp B img o (.done (c11.wr 11 (alu .sltu 192#32 13#32) 0x80003d26#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .sltu 192#32 13#32=0#32)];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x80003d26#32).getLsbD 0=false;decide) rp2147499302 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    have v10 : c12.get 10=179#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v10]
    change Observed.interp B img o (.done (c12.wr 10 (alu .sltu 179#32 15#32) 0x80003d2a#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .sltu 179#32 15#32=0#32)];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine Quiet.step_of (by change (0x80003d2a#32).getLsbD 0=false;decide) rp2147499306 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 ram [],[]⟩
    have v10 : c13.get 10=0#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c13.get 11=0#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v10,v11]
    change Observed.interp B img o (.done (c13.wr 10 (alu .or 0#32 0#32) 0x80003d2c#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .or 0#32 0#32=0#32)];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine Quiet.step_of (by change (0x80003d2c#32).getLsbD 0=false;decide) rp2147499308 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) ram 0 [] [] = ⟨.ok c15 ram [],[]⟩
    have v10 : c14.get 10=0#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v10,Core.get_zero,(by decide +kernel : taken .ne 0#32 (0 : Word)=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,ram⟩ ⟨c16,ram⟩ := by
    refine Quiet.step_of (by change (0x80003d2e#32).getLsbD 0=false;decide) rp2147499310 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) ram 0 [] [] = ⟨.ok c16 ram [],[]⟩
    have v14 : c15.get 14=dst := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c15.get 12=13#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v14,v12]
    change Observed.interp B img o (.done (c15.wr 14 (alu .add dst 13#32) 0x80003d30#32)) ram 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : alu .add dst 13#32=(dst+13#32))];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,ram⟩ ⟨c17,ram⟩ := by
    refine Quiet.step_of (by change (0x80003d30#32).getLsbD 0=false;decide) rp2147499312 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) ram 0 [] [] = ⟨.ok c17 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c16.wr 10 (alu .add 0#32 78#32) 0x80003d34#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 78#32=78#32)];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,ram⟩ ⟨c18,ram⟩ := by
    refine Quiet.step_of (by change (0x80003d34#32).getLsbD 0=false;decide) rp2147499316 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) ram 0 [] [] = ⟨.ok c18 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c17.wr 11 (alu .add 0#32 111#32) 0x80003d38#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 111#32=111#32)];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,ram⟩ ⟨c19,ram⟩ := by
    refine Quiet.step_of (by change (0x80003d38#32).getLsbD 0=false;decide) rp2147499320 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) ram 0 [] [] = ⟨.ok c19 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c18.wr 13 (alu .add 0#32 116#32) 0x80003d3c#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 116#32=116#32)];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,ram⟩ ⟨c20,ram⟩ := by
    refine Quiet.step_of (by change (0x80003d3c#32).getLsbD 0=false;decide) rp2147499324 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) ram 0 [] [] = ⟨.ok c20 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c19.wr 15 (alu .add 0#32 32#32) 0x80003d40#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 32#32=32#32)];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,ram⟩ ⟨c21,r1⟩ := by
    refine Quiet.step_of (by change (0x80003d40#32).getLsbD 0=false;decide) rp2147499328 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) ram 0 [] [] = ⟨.ok c21 r1 [],[]⟩
    have v14 : c20.get 14=(dst+13#32) := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v10 : c20.get 10=78#32 := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v10]
    change Observed.interp B img o (.store .b ((dst+13#32)+0#32) 78#32 false (.done (c20.goto 0x80003d44#32))) ram 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+0#32=dst+13#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 13) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,r1⟩ ⟨c22,r2⟩ := by
    refine Quiet.step_of (by change (0x80003d44#32).getLsbD 0=false;decide) rp2147499332 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) r1 0 [] [] = ⟨.ok c22 r2 [],[]⟩
    have v14 : c21.get 14=(dst+13#32) := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c21.get 11=111#32 := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v11]
    change Observed.interp B img o (.store .b ((dst+13#32)+1#32) 111#32 false (.done (c21.goto 0x80003d48#32))) r1 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+1#32=dst+14#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 14) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,r2⟩ ⟨c23,r3⟩ := by
    refine Quiet.step_of (by change (0x80003d48#32).getLsbD 0=false;decide) rp2147499336 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) r2 0 [] [] = ⟨.ok c23 r3 [],[]⟩
    have v14 : c22.get 14=(dst+13#32) := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c22.get 13=116#32 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+13#32)+2#32) 116#32 false (.done (c22.goto 0x80003d4c#32))) r2 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+2#32=dst+15#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 15) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t23 : Quiet.Step B img ⟨c23,r3⟩ ⟨c24,r4⟩ := by
    refine Quiet.step_of (by change (0x80003d4c#32).getLsbD 0=false;decide) rp2147499340 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) r3 0 [] [] = ⟨.ok c24 r4 [],[]⟩
    have v14 : c23.get 14=(dst+13#32) := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c23.get 15=32#32 := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v15]
    change Observed.interp B img o (.store .b ((dst+13#32)+3#32) 32#32 false (.done (c23.goto 0x80003d50#32))) r3 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+3#32=dst+16#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 16) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t24 : Quiet.Step B img ⟨c24,r4⟩ ⟨c25,r4⟩ := by
    refine Quiet.step_of (by change (0x80003d50#32).getLsbD 0=false;decide) rp2147499344 fun o => ?_
    change Observed.interp B img o (exec c24 _ _) r4 0 [] [] = ⟨.ok c25 r4 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c24.wr 10 (alu .add 0#32 73#32) 0x80003d54#32)) r4 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 73#32=73#32)];first | rfl | (rw [hp];rfl)
  have t25 : Quiet.Step B img ⟨c25,r4⟩ ⟨c26,r4⟩ := by
    refine Quiet.step_of (by change (0x80003d54#32).getLsbD 0=false;decide) rp2147499348 fun o => ?_
    change Observed.interp B img o (exec c25 _ _) r4 0 [] [] = ⟨.ok c26 r4 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c25.wr 11 (alu .add 0#32 109#32) 0x80003d58#32)) r4 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 109#32=109#32)];first | rfl | (rw [hp];rfl)
  have t26 : Quiet.Step B img ⟨c26,r4⟩ ⟨c27,r4⟩ := by
    refine Quiet.step_of (by change (0x80003d58#32).getLsbD 0=false;decide) rp2147499352 fun o => ?_
    change Observed.interp B img o (exec c26 _ _) r4 0 [] [] = ⟨.ok c27 r4 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c26.wr 15 (alu .add 0#32 112#32) 0x80003d5c#32)) r4 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 112#32=112#32)];first | rfl | (rw [hp];rfl)
  have t27 : Quiet.Step B img ⟨c27,r4⟩ ⟨c28,r4⟩ := by
    refine Quiet.step_of (by change (0x80003d5c#32).getLsbD 0=false;decide) rp2147499356 fun o => ?_
    change Observed.interp B img o (exec c27 _ _) r4 0 [] [] = ⟨.ok c28 r4 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c27.wr 16 (alu .add 0#32 108#32) 0x80003d60#32)) r4 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 108#32=108#32)];first | rfl | (rw [hp];rfl)
  have t28 : Quiet.Step B img ⟨c28,r4⟩ ⟨c29,r5⟩ := by
    refine Quiet.step_of (by change (0x80003d60#32).getLsbD 0=false;decide) rp2147499360 fun o => ?_
    change Observed.interp B img o (exec c28 _ _) r4 0 [] [] = ⟨.ok c29 r5 [],[]⟩
    have v14 : c28.get 14=(dst+13#32) := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v10 : c28.get 10=73#32 := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v10]
    change Observed.interp B img o (.store .b ((dst+13#32)+4#32) 73#32 false (.done (c28.goto 0x80003d64#32))) r4 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+4#32=dst+17#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 17) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t29 : Quiet.Step B img ⟨c29,r5⟩ ⟨c30,r6⟩ := by
    refine Quiet.step_of (by change (0x80003d64#32).getLsbD 0=false;decide) rp2147499364 fun o => ?_
    change Observed.interp B img o (exec c29 _ _) r5 0 [] [] = ⟨.ok c30 r6 [],[]⟩
    have v14 : c29.get 14=(dst+13#32) := by simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c29.get 11=109#32 := by simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v11]
    change Observed.interp B img o (.store .b ((dst+13#32)+5#32) 109#32 false (.done (c29.goto 0x80003d68#32))) r5 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+5#32=dst+18#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 18) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t30 : Quiet.Step B img ⟨c30,r6⟩ ⟨c31,r7⟩ := by
    refine Quiet.step_of (by change (0x80003d68#32).getLsbD 0=false;decide) rp2147499368 fun o => ?_
    change Observed.interp B img o (exec c30 _ _) r6 0 [] [] = ⟨.ok c31 r7 [],[]⟩
    have v14 : c30.get 14=(dst+13#32) := by simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c30.get 15=112#32 := by simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v15]
    change Observed.interp B img o (.store .b ((dst+13#32)+6#32) 112#32 false (.done (c30.goto 0x80003d6c#32))) r6 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+6#32=dst+19#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 19) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t31 : Quiet.Step B img ⟨c31,r7⟩ ⟨c32,r8⟩ := by
    refine Quiet.step_of (by change (0x80003d6c#32).getLsbD 0=false;decide) rp2147499372 fun o => ?_
    change Observed.interp B img o (exec c31 _ _) r7 0 [] [] = ⟨.ok c32 r8 [],[]⟩
    have v14 : c31.get 14=(dst+13#32) := by simp [c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v16 : c31.get 16=108#32 := by simp [c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v16]
    change Observed.interp B img o (.store .b ((dst+13#32)+7#32) 108#32 false (.done (c31.goto 0x80003d70#32))) r7 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+7#32=dst+20#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 20) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t32 : Quiet.Step B img ⟨c32,r8⟩ ⟨c33,r8⟩ := by
    refine Quiet.step_of (by change (0x80003d70#32).getLsbD 0=false;decide) rp2147499376 fun o => ?_
    change Observed.interp B img o (exec c32 _ _) r8 0 [] [] = ⟨.ok c33 r8 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c32.wr 10 (alu .add 0#32 101#32) 0x80003d74#32)) r8 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 101#32=101#32)];first | rfl | (rw [hp];rfl)
  have t33 : Quiet.Step B img ⟨c33,r8⟩ ⟨c34,r8⟩ := by
    refine Quiet.step_of (by change (0x80003d74#32).getLsbD 0=false;decide) rp2147499380 fun o => ?_
    change Observed.interp B img o (exec c33 _ _) r8 0 [] [] = ⟨.ok c34 r8 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c33.wr 15 (alu .add 0#32 110#32) 0x80003d78#32)) r8 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 110#32=110#32)];first | rfl | (rw [hp];rfl)
  have t34 : Quiet.Step B img ⟨c34,r8⟩ ⟨c35,r9⟩ := by
    refine Quiet.step_of (by change (0x80003d78#32).getLsbD 0=false;decide) rp2147499384 fun o => ?_
    change Observed.interp B img o (exec c34 _ _) r8 0 [] [] = ⟨.ok c35 r9 [],[]⟩
    have v14 : c34.get 14=(dst+13#32) := by simp [c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v10 : c34.get 10=101#32 := by simp [c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v10]
    change Observed.interp B img o (.store .b ((dst+13#32)+8#32) 101#32 false (.done (c34.goto 0x80003d7c#32))) r8 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+8#32=dst+21#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 21) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t35 : Quiet.Step B img ⟨c35,r9⟩ ⟨c36,r10⟩ := by
    refine Quiet.step_of (by change (0x80003d7c#32).getLsbD 0=false;decide) rp2147499388 fun o => ?_
    change Observed.interp B img o (exec c35 _ _) r9 0 [] [] = ⟨.ok c36 r10 [],[]⟩
    have v14 : c35.get 14=(dst+13#32) := by simp [c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c35.get 11=109#32 := by simp [c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v11]
    change Observed.interp B img o (.store .b ((dst+13#32)+9#32) 109#32 false (.done (c35.goto 0x80003d80#32))) r9 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+9#32=dst+22#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 22) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t36 : Quiet.Step B img ⟨c36,r10⟩ ⟨c37,r11⟩ := by
    refine Quiet.step_of (by change (0x80003d80#32).getLsbD 0=false;decide) rp2147499392 fun o => ?_
    change Observed.interp B img o (exec c36 _ _) r10 0 [] [] = ⟨.ok c37 r11 [],[]⟩
    have v14 : c36.get 14=(dst+13#32) := by simp [c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v10 : c36.get 10=101#32 := by simp [c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v10]
    change Observed.interp B img o (.store .b ((dst+13#32)+10#32) 101#32 false (.done (c36.goto 0x80003d84#32))) r10 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+10#32=dst+23#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 23) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t37 : Quiet.Step B img ⟨c37,r11⟩ ⟨c38,r12⟩ := by
    refine Quiet.step_of (by change (0x80003d84#32).getLsbD 0=false;decide) rp2147499396 fun o => ?_
    change Observed.interp B img o (exec c37 _ _) r11 0 [] [] = ⟨.ok c38 r12 [],[]⟩
    have v14 : c37.get 14=(dst+13#32) := by simp [c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c37.get 15=110#32 := by simp [c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v15]
    change Observed.interp B img o (.store .b ((dst+13#32)+11#32) 110#32 false (.done (c37.goto 0x80003d88#32))) r11 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+11#32=dst+24#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 24) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t38 : Quiet.Step B img ⟨c38,r12⟩ ⟨c39,r12⟩ := by
    refine Quiet.step_of (by change (0x80003d88#32).getLsbD 0=false;decide) rp2147499400 fun o => ?_
    change Observed.interp B img o (exec c38 _ _) r12 0 [] [] = ⟨.ok c39 r12 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c38.wr 11 (alu .add 0#32 100#32) 0x80003d8c#32)) r12 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 100#32=100#32)];first | rfl | (rw [hp];rfl)
  have t39 : Quiet.Step B img ⟨c39,r12⟩ ⟨c40,r13⟩ := by
    refine Quiet.step_of (by change (0x80003d8c#32).getLsbD 0=false;decide) rp2147499404 fun o => ?_
    change Observed.interp B img o (exec c39 _ _) r12 0 [] [] = ⟨.ok c40 r13 [],[]⟩
    have v14 : c39.get 14=(dst+13#32) := by simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c39.get 13=116#32 := by simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+13#32)+12#32) 116#32 false (.done (c39.goto 0x80003d90#32))) r12 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+12#32=dst+25#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 25) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t40 : Quiet.Step B img ⟨c40,r13⟩ ⟨c41,r14⟩ := by
    refine Quiet.step_of (by change (0x80003d90#32).getLsbD 0=false;decide) rp2147499408 fun o => ?_
    change Observed.interp B img o (exec c40 _ _) r13 0 [] [] = ⟨.ok c41 r14 [],[]⟩
    have v14 : c40.get 14=(dst+13#32) := by simp [c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v10 : c40.get 10=101#32 := by simp [c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v10]
    change Observed.interp B img o (.store .b ((dst+13#32)+13#32) 101#32 false (.done (c40.goto 0x80003d94#32))) r13 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+13#32=dst+26#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 26) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t41 : Quiet.Step B img ⟨c41,r14⟩ ⟨c42,r15⟩ := by
    refine Quiet.step_of (by change (0x80003d94#32).getLsbD 0=false;decide) rp2147499412 fun o => ?_
    change Observed.interp B img o (exec c41 _ _) r14 0 [] [] = ⟨.ok c42 r15 [],[]⟩
    have v14 : c41.get 14=(dst+13#32) := by simp [c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c41.get 11=100#32 := by simp [c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v11]
    change Observed.interp B img o (.store .b ((dst+13#32)+14#32) 100#32 false (.done (c41.goto 0x80003d98#32))) r14 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+14#32=dst+27#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 27) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t42 : Quiet.Step B img ⟨c42,r15⟩ ⟨c43,r15⟩ := by
    refine Quiet.step_of (by change (0x80003d98#32).getLsbD 0=false;decide) rp2147499416 fun o => ?_
    change Observed.interp B img o (exec c42 _ _) r15 0 [] [] = ⟨.ok c43 r15 [],[]⟩
    have v12 : c42.get 12=13#32 := by simp [c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v12]
    change Observed.interp B img o (.done (c42.wr 12 (alu .add 13#32 15#32) 0x80003d9a#32)) r15 0 [] [] = _
    rw [(by decide +kernel : alu .add 13#32 15#32=28#32)];first | rfl | (rw [hp];rfl)
  have t43 : Quiet.Step B img ⟨c43,r15⟩ ⟨c44,r15⟩ := by
    refine Quiet.step_of (by change (0x80003d9a#32).getLsbD 0=false;decide) rp2147499418 fun o => ?_
    change Observed.interp B img o (exec c43 _ _) r15 0 [] [] = ⟨.ok c44 r15 [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c43 (2147499418#32+174#32)) r15 0 [] [] = _
    rw [show 2147499418#32+174#32=2147499592#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t44 : Quiet.Step B img ⟨c44,r15⟩ ⟨c45,r15⟩ := by
    refine Quiet.step_of (by change (0x80003e48#32).getLsbD 0=false;decide) rp2147499592 fun o => ?_
    change Observed.interp B img o (exec c44 _ _) r15 0 [] [] = ⟨.ok c45 r15 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c44.wr 10 (alu .add 0#32 1#32) 0x80003e4a#32)) r15 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 1#32=1#32)];first | rfl | (rw [hp];rfl)
  have t45 : Quiet.Step B img ⟨c45,r15⟩ ⟨c46,r15⟩ := by
    refine Quiet.step_of (by change (0x80003e4a#32).getLsbD 0=false;decide) rp2147499594 fun o => ?_
    change Observed.interp B img o (exec c45 _ _) r15 0 [] [] = ⟨.ok c46 r15 [],[]⟩
    have v12 : c45.get 12=28#32 := by simp [c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,Core.get_zero,v12]
    change Observed.interp B img o (.done (c45.wr 11 (alu .add 0#32 28#32) 0x80003e4c#32)) r15 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 28#32=28#32)];first | rfl | (rw [hp];rfl)
  have t46 : Quiet.Step B img ⟨c46,r15⟩ ⟨c47,r15⟩ := by
    refine Quiet.step_of (by change (0x80003e4c#32).getLsbD 0=false;decide) rp2147499596 fun o => ?_
    change Observed.interp B img o (exec c46 _ _) r15 0 [] [] = ⟨.ok c47 r15 [],[]⟩
    have v1 : c46.get 1=c.get 1 := by simp [c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_jalr,v1,BitVec.add_zero]
    change Observed.interp B img o (jump c46 (c.get 1 &&& ~~~1)) r15 0 [] [] = _
    rw [jump_ok _ _ (clear_bit0 _)];first | rfl | (rw [hp];rfl)
  refine ⟨c47,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.step t23 (.step t24 (.step t25 (.step t26 (.step t27 (.step t28 (.step t29 (.step t30 (.step t31 (.step t32 (.step t33 (.step t34 (.step t35 (.step t36 (.step t37 (.step t38 (.step t39 (.step t40 (.step t41 (.step t42 (.step t43 (.step t44 (.step t45 (.single t46)))))))))))))))))))))))))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · intro reg h14 h15 h10 h11 h13 h16 h12;simp [c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15,h10,h11,h13,h16,h12]
end E5R.Thermostat.ReasonBoardHttpReason501
