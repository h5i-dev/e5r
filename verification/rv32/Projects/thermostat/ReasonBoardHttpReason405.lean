import Projects.thermostat.HttpReason405
import Projects.thermostat.StackBoard
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.ReasonBoardHttpReason405
open E5R E5R.Thermostat HttpReason405
abbrev B := StackBoard.board

theorem contract (c : Core) (ram : Word → BitVec 8) (dst : Word) (h10 : c.get 10=dst) (h11 : c.get 11=192#32) (h12 : c.get 12=13#32) (h13 : c.get 13=405#32) (hm : Memory.Block B dst 192)
    (hp : c.pc=0x80003584#32) :
    ∃ d, Quiet.Steps B img 52 ⟨c,ram⟩ ⟨d,memory ram dst⟩ ∧ d.pc=c.get 1 &&& ~~~1 ∧
      d.get 14=(dst+13#32) ∧ d.get 15=100#32 ∧ d.get 10=1#32 ∧ d.get 11=31#32 ∧ d.get 13=108#32 ∧ d.get 16=119#32 ∧ d.get 17=65#32 ∧ d.get 12=31#32 ∧ (∀ r : Reg, r≠14 → r≠15 → r≠10 → r≠11 → r≠13 → r≠16 → r≠17 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (dst) 0x80003586#32
  let c2 := c1.wr 15 (408#32) 0x8000358a#32
  let c3 := c2.wr 10 (1#32) 0x8000358c#32
  let c4 := c3.goto 0x80003590#32
  let c5 := c4.wr 15 (400#32) 0x80003594#32
  let c6 := c5.goto 0x80003598#32
  let c7 := c6.wr 15 (403#32) 0x8000359c#32
  let c8 := c7.goto 0x800035a0#32
  let c9 := c8.wr 15 (404#32) 0x800035a4#32
  let c10 := c9.goto 0x800035a8#32
  let c11 := c10.wr 15 (405#32) 0x800035ac#32
  let c12 := c11.goto 0x80003ba2#32
  let c13 := c12.wr 10 (179#32) 0x80003ba6#32
  let c14 := c13.wr 11 (0#32) 0x80003baa#32
  let c15 := c14.wr 10 (0#32) 0x80003bae#32
  let c16 := c15.wr 10 (0#32) 0x80003bb0#32
  let c17 := c16.goto 0x80003bb4#32
  let c18 := c17.wr 14 ((dst+13#32)) 0x80003bb6#32
  let c19 := c18.wr 10 (77#32) 0x80003bba#32
  let c20 := c19.wr 11 (101#32) 0x80003bbe#32
  let c21 := c20.wr 13 (116#32) 0x80003bc2#32
  let c22 := c21.wr 15 (104#32) 0x80003bc6#32
  let r1 := ramWrite ram (dst+13#32) (77#32) .b
  let c23 := c22.goto 0x80003bca#32
  let r2 := ramWrite r1 (dst+14#32) (101#32) .b
  let c24 := c23.goto 0x80003bce#32
  let r3 := ramWrite r2 (dst+15#32) (116#32) .b
  let c25 := c24.goto 0x80003bd2#32
  let r4 := ramWrite r3 (dst+16#32) (104#32) .b
  let c26 := c25.goto 0x80003bd6#32
  let c27 := c26.wr 10 (111#32) 0x80003bda#32
  let c28 := c27.wr 15 (100#32) 0x80003bde#32
  let c29 := c28.wr 16 (32#32) 0x80003be2#32
  let c30 := c29.wr 17 (78#32) 0x80003be6#32
  let r5 := ramWrite r4 (dst+17#32) (111#32) .b
  let c31 := c30.goto 0x80003bea#32
  let r6 := ramWrite r5 (dst+18#32) (100#32) .b
  let c32 := c31.goto 0x80003bee#32
  let r7 := ramWrite r6 (dst+19#32) (32#32) .b
  let c33 := c32.goto 0x80003bf2#32
  let r8 := ramWrite r7 (dst+20#32) (78#32) .b
  let c34 := c33.goto 0x80003bf6#32
  let c35 := c34.wr 17 (65#32) 0x80003bfa#32
  let r9 := ramWrite r8 (dst+21#32) (111#32) .b
  let c36 := c35.goto 0x80003bfe#32
  let r10 := ramWrite r9 (dst+22#32) (116#32) .b
  let c37 := c36.goto 0x80003c02#32
  let r11 := ramWrite r10 (dst+23#32) (32#32) .b
  let c38 := c37.goto 0x80003c06#32
  let r12 := ramWrite r11 (dst+24#32) (65#32) .b
  let c39 := c38.goto 0x80003c0a#32
  let c40 := c39.wr 13 (108#32) 0x80003c0e#32
  let c41 := c40.wr 16 (119#32) 0x80003c12#32
  let r13 := ramWrite r12 (dst+25#32) (108#32) .b
  let c42 := c41.goto 0x80003c16#32
  let r14 := ramWrite r13 (dst+26#32) (108#32) .b
  let c43 := c42.goto 0x80003c1a#32
  let r15 := ramWrite r14 (dst+27#32) (111#32) .b
  let c44 := c43.goto 0x80003c1e#32
  let r16 := ramWrite r15 (dst+28#32) (119#32) .b
  let c45 := c44.goto 0x80003c22#32
  let r17 := ramWrite r16 (dst+29#32) (101#32) .b
  let c46 := c45.goto 0x80003c26#32
  let r18 := ramWrite r17 (dst+30#32) (100#32) .b
  let c47 := c46.goto 0x80003c2a#32
  let c48 := c47.wr 12 (31#32) 0x80003c2c#32
  let c49 := c48.goto 0x80003e48#32
  let c50 := c49.wr 10 (1#32) 0x80003e4a#32
  let c51 := c50.wr 11 (31#32) 0x80003e4c#32
  let c52 := c51.goto (c.get 1 &&& ~~~1)
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
    have v13 : c3.get 13=405#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by decide +kernel : taken .lt 408#32 405#32=false)]
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
    have v13 : c5.get 13=405#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by decide +kernel : taken .ge 400#32 405#32=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80003598#32).getLsbD 0=false;decide) rp2147497368 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c6.wr 15 (alu .add 0#32 403#32) 0x8000359c#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 403#32=403#32)];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x8000359c#32).getLsbD 0=false;decide) rp2147497372 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v15 : c7.get 15=403#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c7.get 13=405#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by decide +kernel : taken .ge 403#32 405#32=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x800035a0#32).getLsbD 0=false;decide) rp2147497376 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c8.wr 15 (alu .add 0#32 404#32) 0x800035a4#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 404#32=404#32)];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x800035a4#32).getLsbD 0=false;decide) rp2147497380 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v13 : c9.get 13=405#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c9.get 15=404#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v13,v15,(by decide +kernel : taken .eq 405#32 404#32=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x800035a8#32).getLsbD 0=false;decide) rp2147497384 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c10.wr 15 (alu .add 0#32 405#32) 0x800035ac#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 405#32=405#32)];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x800035ac#32).getLsbD 0=false;decide) rp2147497388 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v13 : c11.get 13=405#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c11.get 15=405#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v13,v15,(by decide +kernel : taken .eq 405#32 405#32=true)]
    simp only [ite_true]
    rw [show c11.pc=2147497388#32 by rfl,show 2147497388#32+1526#32=2147498914#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x80003ba2#32).getLsbD 0=false;decide) rp2147498914 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    have v11 : c12.get 11=192#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c12.get 12=13#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v11,v12]
    change Observed.interp B img o (.done (c12.wr 10 (alu .sub 192#32 13#32) 0x80003ba6#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .sub 192#32 13#32=179#32)];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine Quiet.step_of (by change (0x80003ba6#32).getLsbD 0=false;decide) rp2147498918 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 ram [],[]⟩
    have v11 : c13.get 11=192#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c13.get 12=13#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v11,v12]
    change Observed.interp B img o (.done (c13.wr 11 (alu .sltu 192#32 13#32) 0x80003baa#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .sltu 192#32 13#32=0#32)];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine Quiet.step_of (by change (0x80003baa#32).getLsbD 0=false;decide) rp2147498922 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) ram 0 [] [] = ⟨.ok c15 ram [],[]⟩
    have v10 : c14.get 10=179#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v10]
    change Observed.interp B img o (.done (c14.wr 10 (alu .sltu 179#32 18#32) 0x80003bae#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .sltu 179#32 18#32=0#32)];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,ram⟩ ⟨c16,ram⟩ := by
    refine Quiet.step_of (by change (0x80003bae#32).getLsbD 0=false;decide) rp2147498926 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) ram 0 [] [] = ⟨.ok c16 ram [],[]⟩
    have v10 : c15.get 10=0#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c15.get 11=0#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v10,v11]
    change Observed.interp B img o (.done (c15.wr 10 (alu .or 0#32 0#32) 0x80003bb0#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .or 0#32 0#32=0#32)];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,ram⟩ ⟨c17,ram⟩ := by
    refine Quiet.step_of (by change (0x80003bb0#32).getLsbD 0=false;decide) rp2147498928 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) ram 0 [] [] = ⟨.ok c17 ram [],[]⟩
    have v10 : c16.get 10=0#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v10,Core.get_zero,(by decide +kernel : taken .ne 0#32 (0 : Word)=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,ram⟩ ⟨c18,ram⟩ := by
    refine Quiet.step_of (by change (0x80003bb4#32).getLsbD 0=false;decide) rp2147498932 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) ram 0 [] [] = ⟨.ok c18 ram [],[]⟩
    have v14 : c17.get 14=dst := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c17.get 12=13#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v14,v12]
    change Observed.interp B img o (.done (c17.wr 14 (alu .add dst 13#32) 0x80003bb6#32)) ram 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : alu .add dst 13#32=(dst+13#32))];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,ram⟩ ⟨c19,ram⟩ := by
    refine Quiet.step_of (by change (0x80003bb6#32).getLsbD 0=false;decide) rp2147498934 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) ram 0 [] [] = ⟨.ok c19 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c18.wr 10 (alu .add 0#32 77#32) 0x80003bba#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 77#32=77#32)];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,ram⟩ ⟨c20,ram⟩ := by
    refine Quiet.step_of (by change (0x80003bba#32).getLsbD 0=false;decide) rp2147498938 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) ram 0 [] [] = ⟨.ok c20 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c19.wr 11 (alu .add 0#32 101#32) 0x80003bbe#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 101#32=101#32)];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,ram⟩ ⟨c21,ram⟩ := by
    refine Quiet.step_of (by change (0x80003bbe#32).getLsbD 0=false;decide) rp2147498942 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) ram 0 [] [] = ⟨.ok c21 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c20.wr 13 (alu .add 0#32 116#32) 0x80003bc2#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 116#32=116#32)];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,ram⟩ ⟨c22,ram⟩ := by
    refine Quiet.step_of (by change (0x80003bc2#32).getLsbD 0=false;decide) rp2147498946 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) ram 0 [] [] = ⟨.ok c22 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c21.wr 15 (alu .add 0#32 104#32) 0x80003bc6#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 104#32=104#32)];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,ram⟩ ⟨c23,r1⟩ := by
    refine Quiet.step_of (by change (0x80003bc6#32).getLsbD 0=false;decide) rp2147498950 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) ram 0 [] [] = ⟨.ok c23 r1 [],[]⟩
    have v14 : c22.get 14=(dst+13#32) := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v10 : c22.get 10=77#32 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v10]
    change Observed.interp B img o (.store .b ((dst+13#32)+0#32) 77#32 false (.done (c22.goto 0x80003bca#32))) ram 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+0#32=dst+13#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 13) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t23 : Quiet.Step B img ⟨c23,r1⟩ ⟨c24,r2⟩ := by
    refine Quiet.step_of (by change (0x80003bca#32).getLsbD 0=false;decide) rp2147498954 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) r1 0 [] [] = ⟨.ok c24 r2 [],[]⟩
    have v14 : c23.get 14=(dst+13#32) := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c23.get 11=101#32 := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v11]
    change Observed.interp B img o (.store .b ((dst+13#32)+1#32) 101#32 false (.done (c23.goto 0x80003bce#32))) r1 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+1#32=dst+14#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 14) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t24 : Quiet.Step B img ⟨c24,r2⟩ ⟨c25,r3⟩ := by
    refine Quiet.step_of (by change (0x80003bce#32).getLsbD 0=false;decide) rp2147498958 fun o => ?_
    change Observed.interp B img o (exec c24 _ _) r2 0 [] [] = ⟨.ok c25 r3 [],[]⟩
    have v14 : c24.get 14=(dst+13#32) := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c24.get 13=116#32 := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+13#32)+2#32) 116#32 false (.done (c24.goto 0x80003bd2#32))) r2 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+2#32=dst+15#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 15) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t25 : Quiet.Step B img ⟨c25,r3⟩ ⟨c26,r4⟩ := by
    refine Quiet.step_of (by change (0x80003bd2#32).getLsbD 0=false;decide) rp2147498962 fun o => ?_
    change Observed.interp B img o (exec c25 _ _) r3 0 [] [] = ⟨.ok c26 r4 [],[]⟩
    have v14 : c25.get 14=(dst+13#32) := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c25.get 15=104#32 := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v15]
    change Observed.interp B img o (.store .b ((dst+13#32)+3#32) 104#32 false (.done (c25.goto 0x80003bd6#32))) r3 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+3#32=dst+16#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 16) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t26 : Quiet.Step B img ⟨c26,r4⟩ ⟨c27,r4⟩ := by
    refine Quiet.step_of (by change (0x80003bd6#32).getLsbD 0=false;decide) rp2147498966 fun o => ?_
    change Observed.interp B img o (exec c26 _ _) r4 0 [] [] = ⟨.ok c27 r4 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c26.wr 10 (alu .add 0#32 111#32) 0x80003bda#32)) r4 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 111#32=111#32)];first | rfl | (rw [hp];rfl)
  have t27 : Quiet.Step B img ⟨c27,r4⟩ ⟨c28,r4⟩ := by
    refine Quiet.step_of (by change (0x80003bda#32).getLsbD 0=false;decide) rp2147498970 fun o => ?_
    change Observed.interp B img o (exec c27 _ _) r4 0 [] [] = ⟨.ok c28 r4 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c27.wr 15 (alu .add 0#32 100#32) 0x80003bde#32)) r4 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 100#32=100#32)];first | rfl | (rw [hp];rfl)
  have t28 : Quiet.Step B img ⟨c28,r4⟩ ⟨c29,r4⟩ := by
    refine Quiet.step_of (by change (0x80003bde#32).getLsbD 0=false;decide) rp2147498974 fun o => ?_
    change Observed.interp B img o (exec c28 _ _) r4 0 [] [] = ⟨.ok c29 r4 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c28.wr 16 (alu .add 0#32 32#32) 0x80003be2#32)) r4 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 32#32=32#32)];first | rfl | (rw [hp];rfl)
  have t29 : Quiet.Step B img ⟨c29,r4⟩ ⟨c30,r4⟩ := by
    refine Quiet.step_of (by change (0x80003be2#32).getLsbD 0=false;decide) rp2147498978 fun o => ?_
    change Observed.interp B img o (exec c29 _ _) r4 0 [] [] = ⟨.ok c30 r4 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c29.wr 17 (alu .add 0#32 78#32) 0x80003be6#32)) r4 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 78#32=78#32)];first | rfl | (rw [hp];rfl)
  have t30 : Quiet.Step B img ⟨c30,r4⟩ ⟨c31,r5⟩ := by
    refine Quiet.step_of (by change (0x80003be6#32).getLsbD 0=false;decide) rp2147498982 fun o => ?_
    change Observed.interp B img o (exec c30 _ _) r4 0 [] [] = ⟨.ok c31 r5 [],[]⟩
    have v14 : c30.get 14=(dst+13#32) := by simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v10 : c30.get 10=111#32 := by simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v10]
    change Observed.interp B img o (.store .b ((dst+13#32)+4#32) 111#32 false (.done (c30.goto 0x80003bea#32))) r4 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+4#32=dst+17#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 17) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t31 : Quiet.Step B img ⟨c31,r5⟩ ⟨c32,r6⟩ := by
    refine Quiet.step_of (by change (0x80003bea#32).getLsbD 0=false;decide) rp2147498986 fun o => ?_
    change Observed.interp B img o (exec c31 _ _) r5 0 [] [] = ⟨.ok c32 r6 [],[]⟩
    have v14 : c31.get 14=(dst+13#32) := by simp [c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c31.get 15=100#32 := by simp [c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v15]
    change Observed.interp B img o (.store .b ((dst+13#32)+5#32) 100#32 false (.done (c31.goto 0x80003bee#32))) r5 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+5#32=dst+18#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 18) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t32 : Quiet.Step B img ⟨c32,r6⟩ ⟨c33,r7⟩ := by
    refine Quiet.step_of (by change (0x80003bee#32).getLsbD 0=false;decide) rp2147498990 fun o => ?_
    change Observed.interp B img o (exec c32 _ _) r6 0 [] [] = ⟨.ok c33 r7 [],[]⟩
    have v14 : c32.get 14=(dst+13#32) := by simp [c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v16 : c32.get 16=32#32 := by simp [c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v16]
    change Observed.interp B img o (.store .b ((dst+13#32)+6#32) 32#32 false (.done (c32.goto 0x80003bf2#32))) r6 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+6#32=dst+19#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 19) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t33 : Quiet.Step B img ⟨c33,r7⟩ ⟨c34,r8⟩ := by
    refine Quiet.step_of (by change (0x80003bf2#32).getLsbD 0=false;decide) rp2147498994 fun o => ?_
    change Observed.interp B img o (exec c33 _ _) r7 0 [] [] = ⟨.ok c34 r8 [],[]⟩
    have v14 : c33.get 14=(dst+13#32) := by simp [c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v17 : c33.get 17=78#32 := by simp [c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v17]
    change Observed.interp B img o (.store .b ((dst+13#32)+7#32) 78#32 false (.done (c33.goto 0x80003bf6#32))) r7 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+7#32=dst+20#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 20) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t34 : Quiet.Step B img ⟨c34,r8⟩ ⟨c35,r8⟩ := by
    refine Quiet.step_of (by change (0x80003bf6#32).getLsbD 0=false;decide) rp2147498998 fun o => ?_
    change Observed.interp B img o (exec c34 _ _) r8 0 [] [] = ⟨.ok c35 r8 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c34.wr 17 (alu .add 0#32 65#32) 0x80003bfa#32)) r8 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 65#32=65#32)];first | rfl | (rw [hp];rfl)
  have t35 : Quiet.Step B img ⟨c35,r8⟩ ⟨c36,r9⟩ := by
    refine Quiet.step_of (by change (0x80003bfa#32).getLsbD 0=false;decide) rp2147499002 fun o => ?_
    change Observed.interp B img o (exec c35 _ _) r8 0 [] [] = ⟨.ok c36 r9 [],[]⟩
    have v14 : c35.get 14=(dst+13#32) := by simp [c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v10 : c35.get 10=111#32 := by simp [c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v10]
    change Observed.interp B img o (.store .b ((dst+13#32)+8#32) 111#32 false (.done (c35.goto 0x80003bfe#32))) r8 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+8#32=dst+21#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 21) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t36 : Quiet.Step B img ⟨c36,r9⟩ ⟨c37,r10⟩ := by
    refine Quiet.step_of (by change (0x80003bfe#32).getLsbD 0=false;decide) rp2147499006 fun o => ?_
    change Observed.interp B img o (exec c36 _ _) r9 0 [] [] = ⟨.ok c37 r10 [],[]⟩
    have v14 : c36.get 14=(dst+13#32) := by simp [c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c36.get 13=116#32 := by simp [c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+13#32)+9#32) 116#32 false (.done (c36.goto 0x80003c02#32))) r9 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+9#32=dst+22#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 22) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t37 : Quiet.Step B img ⟨c37,r10⟩ ⟨c38,r11⟩ := by
    refine Quiet.step_of (by change (0x80003c02#32).getLsbD 0=false;decide) rp2147499010 fun o => ?_
    change Observed.interp B img o (exec c37 _ _) r10 0 [] [] = ⟨.ok c38 r11 [],[]⟩
    have v14 : c37.get 14=(dst+13#32) := by simp [c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v16 : c37.get 16=32#32 := by simp [c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v16]
    change Observed.interp B img o (.store .b ((dst+13#32)+10#32) 32#32 false (.done (c37.goto 0x80003c06#32))) r10 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+10#32=dst+23#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 23) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t38 : Quiet.Step B img ⟨c38,r11⟩ ⟨c39,r12⟩ := by
    refine Quiet.step_of (by change (0x80003c06#32).getLsbD 0=false;decide) rp2147499014 fun o => ?_
    change Observed.interp B img o (exec c38 _ _) r11 0 [] [] = ⟨.ok c39 r12 [],[]⟩
    have v14 : c38.get 14=(dst+13#32) := by simp [c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v17 : c38.get 17=65#32 := by simp [c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v17]
    change Observed.interp B img o (.store .b ((dst+13#32)+11#32) 65#32 false (.done (c38.goto 0x80003c0a#32))) r11 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+11#32=dst+24#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 24) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t39 : Quiet.Step B img ⟨c39,r12⟩ ⟨c40,r12⟩ := by
    refine Quiet.step_of (by change (0x80003c0a#32).getLsbD 0=false;decide) rp2147499018 fun o => ?_
    change Observed.interp B img o (exec c39 _ _) r12 0 [] [] = ⟨.ok c40 r12 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c39.wr 13 (alu .add 0#32 108#32) 0x80003c0e#32)) r12 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 108#32=108#32)];first | rfl | (rw [hp];rfl)
  have t40 : Quiet.Step B img ⟨c40,r12⟩ ⟨c41,r12⟩ := by
    refine Quiet.step_of (by change (0x80003c0e#32).getLsbD 0=false;decide) rp2147499022 fun o => ?_
    change Observed.interp B img o (exec c40 _ _) r12 0 [] [] = ⟨.ok c41 r12 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c40.wr 16 (alu .add 0#32 119#32) 0x80003c12#32)) r12 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 119#32=119#32)];first | rfl | (rw [hp];rfl)
  have t41 : Quiet.Step B img ⟨c41,r12⟩ ⟨c42,r13⟩ := by
    refine Quiet.step_of (by change (0x80003c12#32).getLsbD 0=false;decide) rp2147499026 fun o => ?_
    change Observed.interp B img o (exec c41 _ _) r12 0 [] [] = ⟨.ok c42 r13 [],[]⟩
    have v14 : c41.get 14=(dst+13#32) := by simp [c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c41.get 13=108#32 := by simp [c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+13#32)+12#32) 108#32 false (.done (c41.goto 0x80003c16#32))) r12 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+12#32=dst+25#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 25) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t42 : Quiet.Step B img ⟨c42,r13⟩ ⟨c43,r14⟩ := by
    refine Quiet.step_of (by change (0x80003c16#32).getLsbD 0=false;decide) rp2147499030 fun o => ?_
    change Observed.interp B img o (exec c42 _ _) r13 0 [] [] = ⟨.ok c43 r14 [],[]⟩
    have v14 : c42.get 14=(dst+13#32) := by simp [c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c42.get 13=108#32 := by simp [c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+13#32)+13#32) 108#32 false (.done (c42.goto 0x80003c1a#32))) r13 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+13#32=dst+26#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 26) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t43 : Quiet.Step B img ⟨c43,r14⟩ ⟨c44,r15⟩ := by
    refine Quiet.step_of (by change (0x80003c1a#32).getLsbD 0=false;decide) rp2147499034 fun o => ?_
    change Observed.interp B img o (exec c43 _ _) r14 0 [] [] = ⟨.ok c44 r15 [],[]⟩
    have v14 : c43.get 14=(dst+13#32) := by simp [c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v10 : c43.get 10=111#32 := by simp [c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v10]
    change Observed.interp B img o (.store .b ((dst+13#32)+14#32) 111#32 false (.done (c43.goto 0x80003c1e#32))) r14 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+14#32=dst+27#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 27) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t44 : Quiet.Step B img ⟨c44,r15⟩ ⟨c45,r16⟩ := by
    refine Quiet.step_of (by change (0x80003c1e#32).getLsbD 0=false;decide) rp2147499038 fun o => ?_
    change Observed.interp B img o (exec c44 _ _) r15 0 [] [] = ⟨.ok c45 r16 [],[]⟩
    have v14 : c44.get 14=(dst+13#32) := by simp [c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v16 : c44.get 16=119#32 := by simp [c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v16]
    change Observed.interp B img o (.store .b ((dst+13#32)+15#32) 119#32 false (.done (c44.goto 0x80003c22#32))) r15 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+15#32=dst+28#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 28) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t45 : Quiet.Step B img ⟨c45,r16⟩ ⟨c46,r17⟩ := by
    refine Quiet.step_of (by change (0x80003c22#32).getLsbD 0=false;decide) rp2147499042 fun o => ?_
    change Observed.interp B img o (exec c45 _ _) r16 0 [] [] = ⟨.ok c46 r17 [],[]⟩
    have v14 : c45.get 14=(dst+13#32) := by simp [c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c45.get 11=101#32 := by simp [c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v11]
    change Observed.interp B img o (.store .b ((dst+13#32)+16#32) 101#32 false (.done (c45.goto 0x80003c26#32))) r16 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+16#32=dst+29#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 29) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t46 : Quiet.Step B img ⟨c46,r17⟩ ⟨c47,r18⟩ := by
    refine Quiet.step_of (by change (0x80003c26#32).getLsbD 0=false;decide) rp2147499046 fun o => ?_
    change Observed.interp B img o (exec c46 _ _) r17 0 [] [] = ⟨.ok c47 r18 [],[]⟩
    have v14 : c46.get 14=(dst+13#32) := by simp [c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c46.get 15=100#32 := by simp [c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v15]
    change Observed.interp B img o (.store .b ((dst+13#32)+17#32) 100#32 false (.done (c46.goto 0x80003c2a#32))) r17 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+17#32=dst+30#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 30) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t47 : Quiet.Step B img ⟨c47,r18⟩ ⟨c48,r18⟩ := by
    refine Quiet.step_of (by change (0x80003c2a#32).getLsbD 0=false;decide) rp2147499050 fun o => ?_
    change Observed.interp B img o (exec c47 _ _) r18 0 [] [] = ⟨.ok c48 r18 [],[]⟩
    have v12 : c47.get 12=13#32 := by simp [c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v12]
    change Observed.interp B img o (.done (c47.wr 12 (alu .add 13#32 18#32) 0x80003c2c#32)) r18 0 [] [] = _
    rw [(by decide +kernel : alu .add 13#32 18#32=31#32)];first | rfl | (rw [hp];rfl)
  have t48 : Quiet.Step B img ⟨c48,r18⟩ ⟨c49,r18⟩ := by
    refine Quiet.step_of (by change (0x80003c2c#32).getLsbD 0=false;decide) rp2147499052 fun o => ?_
    change Observed.interp B img o (exec c48 _ _) r18 0 [] [] = ⟨.ok c49 r18 [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c48 (2147499052#32+540#32)) r18 0 [] [] = _
    rw [show 2147499052#32+540#32=2147499592#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t49 : Quiet.Step B img ⟨c49,r18⟩ ⟨c50,r18⟩ := by
    refine Quiet.step_of (by change (0x80003e48#32).getLsbD 0=false;decide) rp2147499592 fun o => ?_
    change Observed.interp B img o (exec c49 _ _) r18 0 [] [] = ⟨.ok c50 r18 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c49.wr 10 (alu .add 0#32 1#32) 0x80003e4a#32)) r18 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 1#32=1#32)];first | rfl | (rw [hp];rfl)
  have t50 : Quiet.Step B img ⟨c50,r18⟩ ⟨c51,r18⟩ := by
    refine Quiet.step_of (by change (0x80003e4a#32).getLsbD 0=false;decide) rp2147499594 fun o => ?_
    change Observed.interp B img o (exec c50 _ _) r18 0 [] [] = ⟨.ok c51 r18 [],[]⟩
    have v12 : c50.get 12=31#32 := by simp [c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,Core.get_zero,v12]
    change Observed.interp B img o (.done (c50.wr 11 (alu .add 0#32 31#32) 0x80003e4c#32)) r18 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 31#32=31#32)];first | rfl | (rw [hp];rfl)
  have t51 : Quiet.Step B img ⟨c51,r18⟩ ⟨c52,r18⟩ := by
    refine Quiet.step_of (by change (0x80003e4c#32).getLsbD 0=false;decide) rp2147499596 fun o => ?_
    change Observed.interp B img o (exec c51 _ _) r18 0 [] [] = ⟨.ok c52 r18 [],[]⟩
    have v1 : c51.get 1=c.get 1 := by simp [c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_jalr,v1,BitVec.add_zero]
    change Observed.interp B img o (jump c51 (c.get 1 &&& ~~~1)) r18 0 [] [] = _
    rw [jump_ok _ _ (clear_bit0 _)];first | rfl | (rw [hp];rfl)
  refine ⟨c52,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.step t23 (.step t24 (.step t25 (.step t26 (.step t27 (.step t28 (.step t29 (.step t30 (.step t31 (.step t32 (.step t33 (.step t34 (.step t35 (.step t36 (.step t37 (.step t38 (.step t39 (.step t40 (.step t41 (.step t42 (.step t43 (.step t44 (.step t45 (.step t46 (.step t47 (.step t48 (.step t49 (.step t50 (.single t51))))))))))))))))))))))))))))))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · intro reg h14 h15 h10 h11 h13 h16 h17 h12;simp [c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15,h10,h11,h13,h16,h17,h12]
end E5R.Thermostat.ReasonBoardHttpReason405
