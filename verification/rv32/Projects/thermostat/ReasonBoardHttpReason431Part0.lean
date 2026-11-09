import Projects.thermostat.HttpReason431Part0
import Projects.thermostat.StackBoard
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.ReasonBoardHttpReason431Part0
open E5R E5R.Thermostat HttpReason431Part0
abbrev B := StackBoard.board

theorem contract (c : Core) (ram : Word → BitVec 8) (dst : Word) (h10 : c.get 10=dst) (h11 : c.get 11=192#32) (h12 : c.get 12=13#32) (h13 : c.get 13=431#32) (hm : Memory.Block B dst 192)
    (hp : c.pc=0x80003584#32) :
    ∃ d, Quiet.Steps B img 30 ⟨c,ram⟩ ⟨d,memory ram dst⟩ ∧ d.pc=0x80003e3a#32 ∧
      d.get 14=(dst+15#32) ∧ d.get 15=431#32 ∧ d.get 10=(dst+44#32) ∧ d.get 11=2147507438#32 ∧ d.get 13=113#32 ∧ (∀ r : Reg, r≠14 → r≠15 → r≠10 → r≠11 → r≠13 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (dst) 0x80003586#32
  let c2 := c1.wr 15 (408#32) 0x8000358a#32
  let c3 := c2.wr 10 (1#32) 0x8000358c#32
  let c4 := c3.goto 0x8000363a#32
  let c5 := c4.wr 15 (430#32) 0x8000363e#32
  let c6 := c5.goto 0x80003642#32
  let c7 := c6.wr 15 (500#32) 0x80003646#32
  let c8 := c7.goto 0x800039c0#32
  let c9 := c8.wr 15 (431#32) 0x800039c4#32
  let c10 := c9.goto 0x80003e12#32
  let c11 := c10.wr 10 (179#32) 0x80003e16#32
  let c12 := c11.wr 11 (0#32) 0x80003e1a#32
  let c13 := c12.wr 10 (0#32) 0x80003e1e#32
  let c14 := c13.wr 10 (0#32) 0x80003e20#32
  let c15 := c14.goto 0x80003e28#32
  let c16 := c15.wr 14 ((dst+13#32)) 0x80003e2a#32
  let c17 := c16.wr 10 ((dst+44#32)) 0x80003e2e#32
  let c18 := c17.wr 11 (2147508224#32) 0x80003e32#32
  let c19 := c18.wr 11 (2147507436#32) 0x80003e36#32
  let c20 := c19.wr 13 (82#32) 0x80003e3a#32
  let r1 := ramWrite ram (dst+13#32) (82#32) .b
  let c21 := c20.goto 0x80003e3e#32
  let c22 := c21.wr 14 ((dst+14#32)) 0x80003e40#32
  let c23 := c22.wr 11 (2147507437#32) 0x80003e42#32
  let c24 := c23.goto 0x80003e36#32
  let c25 := c24.wr 13 (101#32) 0x80003e3a#32
  let r2 := ramWrite r1 (dst+14#32) (101#32) .b
  let c26 := c25.goto 0x80003e3e#32
  let c27 := c26.wr 14 ((dst+15#32)) 0x80003e40#32
  let c28 := c27.wr 11 (2147507438#32) 0x80003e42#32
  let c29 := c28.goto 0x80003e36#32
  let c30 := c29.wr 13 (113#32) 0x80003e3a#32
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
    have v13 : c3.get 13=431#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by decide +kernel : taken .lt 408#32 431#32=true)]
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
    have v13 : c5.get 13=431#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by decide +kernel : taken .ge 430#32 431#32=false)]
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
    have v13 : c7.get 13=431#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by decide +kernel : taken .ge 500#32 431#32=true)]
    simp only [ite_true]
    rw [show c7.pc=2147497542#32 by rfl,show 2147497542#32+890#32=2147498432#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x800039c0#32).getLsbD 0=false;decide) rp2147498432 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c8.wr 15 (alu .add 0#32 431#32) 0x800039c4#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 431#32=431#32)];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x800039c4#32).getLsbD 0=false;decide) rp2147498436 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v13 : c9.get 13=431#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c9.get 15=431#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v13,v15,(by decide +kernel : taken .eq 431#32 431#32=true)]
    simp only [ite_true]
    rw [show c9.pc=2147498436#32 by rfl,show 2147498436#32+1102#32=2147499538#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e12#32).getLsbD 0=false;decide) rp2147499538 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v11 : c10.get 11=192#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c10.get 12=13#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v11,v12]
    change Observed.interp B img o (.done (c10.wr 10 (alu .sub 192#32 13#32) 0x80003e16#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .sub 192#32 13#32=179#32)];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e16#32).getLsbD 0=false;decide) rp2147499542 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v11 : c11.get 11=192#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c11.get 12=13#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v11,v12]
    change Observed.interp B img o (.done (c11.wr 11 (alu .sltu 192#32 13#32) 0x80003e1a#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .sltu 192#32 13#32=0#32)];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e1a#32).getLsbD 0=false;decide) rp2147499546 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    have v10 : c12.get 10=179#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v10]
    change Observed.interp B img o (.done (c12.wr 10 (alu .sltu 179#32 31#32) 0x80003e1e#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .sltu 179#32 31#32=0#32)];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e1e#32).getLsbD 0=false;decide) rp2147499550 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 ram [],[]⟩
    have v10 : c13.get 10=0#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c13.get 11=0#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v10,v11]
    change Observed.interp B img o (.done (c13.wr 10 (alu .or 0#32 0#32) 0x80003e20#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .or 0#32 0#32=0#32)];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e20#32).getLsbD 0=false;decide) rp2147499552 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) ram 0 [] [] = ⟨.ok c15 ram [],[]⟩
    have v10 : c14.get 10=0#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v10,Core.get_zero,(by decide +kernel : taken .eq 0#32 (0 : Word)=true)]
    simp only [ite_true]
    rw [show c14.pc=2147499552#32 by rfl,show 2147499552#32+8#32=2147499560#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,ram⟩ ⟨c16,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e28#32).getLsbD 0=false;decide) rp2147499560 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) ram 0 [] [] = ⟨.ok c16 ram [],[]⟩
    have v14 : c15.get 14=dst := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c15.get 12=13#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v14,v12]
    change Observed.interp B img o (.done (c15.wr 14 (alu .add dst 13#32) 0x80003e2a#32)) ram 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : alu .add dst 13#32=(dst+13#32))];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,ram⟩ ⟨c17,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e2a#32).getLsbD 0=false;decide) rp2147499562 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) ram 0 [] [] = ⟨.ok c17 ram [],[]⟩
    have v14 : c16.get 14=(dst+13#32) := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c16.wr 10 (alu .add (dst+13#32) 31#32) 0x80003e2e#32)) ram 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : alu .add (dst+13#32) 31#32=(dst+44#32))];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,ram⟩ ⟨c18,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e2e#32).getLsbD 0=false;decide) rp2147499566 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) ram 0 [] [] = ⟨.ok c18 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,ram⟩ ⟨c19,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e32#32).getLsbD 0=false;decide) rp2147499570 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) ram 0 [] [] = ⟨.ok c19 ram [],[]⟩
    have v11 : c18.get 11=2147508224#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v11]
    change Observed.interp B img o (.done (c18.wr 11 (alu .add 2147508224#32 4294966508#32) 0x80003e36#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 2147508224#32 4294966508#32=2147507436#32)];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,ram⟩ ⟨c20,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e36#32).getLsbD 0=false;decide) rp2147499574 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) ram 0 [] [] = ⟨.ok c20 ram [],[]⟩
    have v11 : c19.get 11=2147507436#32 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have hb : ReadBytes.Byte B img ram 2147507436#32 82#8 := .rom (by unfold B StackBoard.board;decide +kernel) (by rw [PackedData.read_byte _ (by decide) (by decide)];exact congrArg some (by decide +kernel))
    rw [exec_load,v11]
    change Observed.interp B img o (.load .b 2147507436#32 false _) ram 0 [] [] = _
    rw [ObservedByte.load hb o _ 0 [] []];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,ram⟩ ⟨c21,r1⟩ := by
    refine Quiet.step_of (by change (0x80003e3a#32).getLsbD 0=false;decide) rp2147499578 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) ram 0 [] [] = ⟨.ok c21 r1 [],[]⟩
    have v14 : c20.get 14=(dst+13#32) := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c20.get 13=82#32 := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+13#32)+0#32) 82#32 false (.done (c20.goto 0x80003e3e#32))) ram 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+0#32=dst+13#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 13) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,r1⟩ ⟨c22,r1⟩ := by
    refine Quiet.step_of (by change (0x80003e3e#32).getLsbD 0=false;decide) rp2147499582 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) r1 0 [] [] = ⟨.ok c22 r1 [],[]⟩
    have v14 : c21.get 14=(dst+13#32) := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c21.wr 14 (alu .add (dst+13#32) 1#32) 0x80003e40#32)) r1 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : alu .add (dst+13#32) 1#32=(dst+14#32))];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,r1⟩ ⟨c23,r1⟩ := by
    refine Quiet.step_of (by change (0x80003e40#32).getLsbD 0=false;decide) rp2147499584 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) r1 0 [] [] = ⟨.ok c23 r1 [],[]⟩
    have v11 : c22.get 11=2147507436#32 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v11]
    change Observed.interp B img o (.done (c22.wr 11 (alu .add 2147507436#32 1#32) 0x80003e42#32)) r1 0 [] [] = _
    rw [(by decide +kernel : alu .add 2147507436#32 1#32=2147507437#32)];first | rfl | (rw [hp];rfl)
  have t23 : Quiet.Step B img ⟨c23,r1⟩ ⟨c24,r1⟩ := by
    refine Quiet.step_of (by change (0x80003e42#32).getLsbD 0=false;decide) rp2147499586 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) r1 0 [] [] = ⟨.ok c24 r1 [],[]⟩
    have v14 : c23.get 14=(dst+14#32) := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v10 : c23.get 10=(dst+44#32) := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v14,v10,(by simp [taken,BitVec.add_right_inj] : taken .ne (dst+14#32) (dst+44#32)=true)]
    simp only [ite_true]
    rw [show c23.pc=2147499586#32 by rfl,show 2147499586#32+4294967284#32=2147499574#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t24 : Quiet.Step B img ⟨c24,r1⟩ ⟨c25,r1⟩ := by
    refine Quiet.step_of (by change (0x80003e36#32).getLsbD 0=false;decide) rp2147499574 fun o => ?_
    change Observed.interp B img o (exec c24 _ _) r1 0 [] [] = ⟨.ok c25 r1 [],[]⟩
    have v11 : c24.get 11=2147507437#32 := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have hb : ReadBytes.Byte B img r1 2147507437#32 101#8 := .rom (by unfold B StackBoard.board;decide +kernel) (by rw [PackedData.read_byte _ (by decide) (by decide)];exact congrArg some (by decide +kernel))
    rw [exec_load,v11]
    change Observed.interp B img o (.load .b 2147507437#32 false _) r1 0 [] [] = _
    rw [ObservedByte.load hb o _ 0 [] []];first | rfl | (rw [hp];rfl)
  have t25 : Quiet.Step B img ⟨c25,r1⟩ ⟨c26,r2⟩ := by
    refine Quiet.step_of (by change (0x80003e3a#32).getLsbD 0=false;decide) rp2147499578 fun o => ?_
    change Observed.interp B img o (exec c25 _ _) r1 0 [] [] = ⟨.ok c26 r2 [],[]⟩
    have v14 : c25.get 14=(dst+14#32) := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c25.get 13=101#32 := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+14#32)+0#32) 101#32 false (.done (c25.goto 0x80003e3e#32))) r1 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+14#32)+0#32=dst+14#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 14) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t26 : Quiet.Step B img ⟨c26,r2⟩ ⟨c27,r2⟩ := by
    refine Quiet.step_of (by change (0x80003e3e#32).getLsbD 0=false;decide) rp2147499582 fun o => ?_
    change Observed.interp B img o (exec c26 _ _) r2 0 [] [] = ⟨.ok c27 r2 [],[]⟩
    have v14 : c26.get 14=(dst+14#32) := by simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c26.wr 14 (alu .add (dst+14#32) 1#32) 0x80003e40#32)) r2 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : alu .add (dst+14#32) 1#32=(dst+15#32))];first | rfl | (rw [hp];rfl)
  have t27 : Quiet.Step B img ⟨c27,r2⟩ ⟨c28,r2⟩ := by
    refine Quiet.step_of (by change (0x80003e40#32).getLsbD 0=false;decide) rp2147499584 fun o => ?_
    change Observed.interp B img o (exec c27 _ _) r2 0 [] [] = ⟨.ok c28 r2 [],[]⟩
    have v11 : c27.get 11=2147507437#32 := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v11]
    change Observed.interp B img o (.done (c27.wr 11 (alu .add 2147507437#32 1#32) 0x80003e42#32)) r2 0 [] [] = _
    rw [(by decide +kernel : alu .add 2147507437#32 1#32=2147507438#32)];first | rfl | (rw [hp];rfl)
  have t28 : Quiet.Step B img ⟨c28,r2⟩ ⟨c29,r2⟩ := by
    refine Quiet.step_of (by change (0x80003e42#32).getLsbD 0=false;decide) rp2147499586 fun o => ?_
    change Observed.interp B img o (exec c28 _ _) r2 0 [] [] = ⟨.ok c29 r2 [],[]⟩
    have v14 : c28.get 14=(dst+15#32) := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v10 : c28.get 10=(dst+44#32) := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v14,v10,(by simp [taken,BitVec.add_right_inj] : taken .ne (dst+15#32) (dst+44#32)=true)]
    simp only [ite_true]
    rw [show c28.pc=2147499586#32 by rfl,show 2147499586#32+4294967284#32=2147499574#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t29 : Quiet.Step B img ⟨c29,r2⟩ ⟨c30,r2⟩ := by
    refine Quiet.step_of (by change (0x80003e36#32).getLsbD 0=false;decide) rp2147499574 fun o => ?_
    change Observed.interp B img o (exec c29 _ _) r2 0 [] [] = ⟨.ok c30 r2 [],[]⟩
    have v11 : c29.get 11=2147507438#32 := by simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have hb : ReadBytes.Byte B img r2 2147507438#32 113#8 := .rom (by unfold B StackBoard.board;decide +kernel) (by rw [PackedData.read_byte _ (by decide) (by decide)];exact congrArg some (by decide +kernel))
    rw [exec_load,v11]
    change Observed.interp B img o (.load .b 2147507438#32 false _) r2 0 [] [] = _
    rw [ObservedByte.load hb o _ 0 [] []];first | rfl | (rw [hp];rfl)
  refine ⟨c30,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.step t23 (.step t24 (.step t25 (.step t26 (.step t27 (.step t28 (.single t29))))))))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · intro reg h14 h15 h10 h11 h13;simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15,h10,h11,h13]
end E5R.Thermostat.ReasonBoardHttpReason431Part0
