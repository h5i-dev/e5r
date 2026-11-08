import Projects.thermostat.HttpReasonCode
import Projects.thermostat.QuietRam
import Projects.thermostat.ObservedByte
import Projects.thermostat.PackedData
import Projects.thermostat.UartPlatform
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HttpReason408
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def memory (ram : Word → BitVec 8) (dst : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (dst+13#32) (82#32) .b) (dst+14#32) (101#32) .b) (dst+15#32) (113#32) .b) (dst+16#32) (117#32) .b) (dst+17#32) (101#32) .b) (dst+18#32) (115#32) .b) (dst+19#32) (116#32) .b) (dst+20#32) (32#32) .b) (dst+21#32) (84#32) .b) (dst+22#32) (105#32) .b) (dst+23#32) (109#32) .b) (dst+24#32) (101#32) .b) (dst+25#32) (111#32) .b) (dst+26#32) (117#32) .b) (dst+27#32) (116#32) .b

theorem contract (c : Core) (ram : Word → BitVec 8) (dst : Word) (h10 : c.get 10=dst) (h11 : c.get 11=192#32) (h12 : c.get 12=13#32) (h13 : c.get 13=408#32) (hm : Memory.Block B dst 192)
    (hp : c.pc=0x80003584#32) :
    ∃ d, Quiet.Steps B img 51 ⟨c,ram⟩ ⟨d,memory ram dst⟩ ∧ d.pc=c.get 1 &&& ~~~1 ∧
      d.get 14=(dst+13#32) ∧ d.get 15=117#32 ∧ d.get 10=1#32 ∧ d.get 11=28#32 ∧ d.get 13=116#32 ∧ d.get 16=105#32 ∧ d.get 17=109#32 ∧ d.get 5=111#32 ∧ d.get 12=28#32 ∧ (∀ r : Reg, r≠14 → r≠15 → r≠10 → r≠11 → r≠13 → r≠16 → r≠17 → r≠5 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
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
  let c12 := c11.goto 0x800035b0#32
  let c13 := c12.wr 15 (408#32) 0x800035b4#32
  let c14 := c13.goto 0x800035b8#32
  let c15 := c14.wr 10 (179#32) 0x800035bc#32
  let c16 := c15.wr 11 (0#32) 0x800035c0#32
  let c17 := c16.wr 10 (0#32) 0x800035c4#32
  let c18 := c17.wr 10 (0#32) 0x800035c6#32
  let c19 := c18.goto 0x800035ca#32
  let c20 := c19.wr 14 ((dst+13#32)) 0x800035cc#32
  let c21 := c20.wr 10 (82#32) 0x800035d0#32
  let c22 := c21.wr 11 (101#32) 0x800035d4#32
  let c23 := c22.wr 13 (113#32) 0x800035d8#32
  let c24 := c23.wr 15 (117#32) 0x800035dc#32
  let r1 := ramWrite ram (dst+13#32) (82#32) .b
  let c25 := c24.goto 0x800035e0#32
  let r2 := ramWrite r1 (dst+14#32) (101#32) .b
  let c26 := c25.goto 0x800035e4#32
  let r3 := ramWrite r2 (dst+15#32) (113#32) .b
  let c27 := c26.goto 0x800035e8#32
  let r4 := ramWrite r3 (dst+16#32) (117#32) .b
  let c28 := c27.goto 0x800035ec#32
  let c29 := c28.wr 10 (115#32) 0x800035f0#32
  let c30 := c29.wr 13 (116#32) 0x800035f4#32
  let c31 := c30.wr 16 (32#32) 0x800035f8#32
  let r5 := ramWrite r4 (dst+17#32) (101#32) .b
  let c32 := c31.goto 0x800035fc#32
  let r6 := ramWrite r5 (dst+18#32) (115#32) .b
  let c33 := c32.goto 0x80003600#32
  let r7 := ramWrite r6 (dst+19#32) (116#32) .b
  let c34 := c33.goto 0x80003604#32
  let r8 := ramWrite r7 (dst+20#32) (32#32) .b
  let c35 := c34.goto 0x80003608#32
  let c36 := c35.wr 10 (84#32) 0x8000360c#32
  let c37 := c36.wr 16 (105#32) 0x80003610#32
  let c38 := c37.wr 17 (109#32) 0x80003614#32
  let c39 := c38.wr 5 (111#32) 0x80003618#32
  let r9 := ramWrite r8 (dst+21#32) (84#32) .b
  let c40 := c39.goto 0x8000361c#32
  let r10 := ramWrite r9 (dst+22#32) (105#32) .b
  let c41 := c40.goto 0x80003620#32
  let r11 := ramWrite r10 (dst+23#32) (109#32) .b
  let c42 := c41.goto 0x80003624#32
  let r12 := ramWrite r11 (dst+24#32) (101#32) .b
  let c43 := c42.goto 0x80003628#32
  let r13 := ramWrite r12 (dst+25#32) (111#32) .b
  let c44 := c43.goto 0x8000362c#32
  let r14 := ramWrite r13 (dst+26#32) (117#32) .b
  let c45 := c44.goto 0x80003630#32
  let r15 := ramWrite r14 (dst+27#32) (116#32) .b
  let c46 := c45.goto 0x80003634#32
  let c47 := c46.wr 12 (28#32) 0x80003636#32
  let c48 := c47.goto 0x80003e48#32
  let c49 := c48.wr 10 (1#32) 0x80003e4a#32
  let c50 := c49.wr 11 (28#32) 0x80003e4c#32
  let c51 := c50.goto (c.get 1 &&& ~~~1)
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
    have v13 : c3.get 13=408#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by decide +kernel : taken .lt 408#32 408#32=false)]
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
    have v13 : c5.get 13=408#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by decide +kernel : taken .ge 400#32 408#32=false)]
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
    have v13 : c7.get 13=408#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by decide +kernel : taken .ge 403#32 408#32=false)]
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
    have v13 : c9.get 13=408#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c9.get 15=404#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v13,v15,(by decide +kernel : taken .eq 408#32 404#32=false)]
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
    have v13 : c11.get 13=408#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c11.get 15=405#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v13,v15,(by decide +kernel : taken .eq 408#32 405#32=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x800035b0#32).getLsbD 0=false;decide) rp2147497392 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c12.wr 15 (alu .add 0#32 408#32) 0x800035b4#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 408#32=408#32)];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine Quiet.step_of (by change (0x800035b4#32).getLsbD 0=false;decide) rp2147497396 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 ram [],[]⟩
    have v13 : c13.get 13=408#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c13.get 15=408#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v13,v15,(by decide +kernel : taken .ne 408#32 408#32=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine Quiet.step_of (by change (0x800035b8#32).getLsbD 0=false;decide) rp2147497400 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) ram 0 [] [] = ⟨.ok c15 ram [],[]⟩
    have v11 : c14.get 11=192#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c14.get 12=13#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v11,v12]
    change Observed.interp B img o (.done (c14.wr 10 (alu .sub 192#32 13#32) 0x800035bc#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .sub 192#32 13#32=179#32)];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,ram⟩ ⟨c16,ram⟩ := by
    refine Quiet.step_of (by change (0x800035bc#32).getLsbD 0=false;decide) rp2147497404 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) ram 0 [] [] = ⟨.ok c16 ram [],[]⟩
    have v11 : c15.get 11=192#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c15.get 12=13#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v11,v12]
    change Observed.interp B img o (.done (c15.wr 11 (alu .sltu 192#32 13#32) 0x800035c0#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .sltu 192#32 13#32=0#32)];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,ram⟩ ⟨c17,ram⟩ := by
    refine Quiet.step_of (by change (0x800035c0#32).getLsbD 0=false;decide) rp2147497408 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) ram 0 [] [] = ⟨.ok c17 ram [],[]⟩
    have v10 : c16.get 10=179#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v10]
    change Observed.interp B img o (.done (c16.wr 10 (alu .sltu 179#32 15#32) 0x800035c4#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .sltu 179#32 15#32=0#32)];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,ram⟩ ⟨c18,ram⟩ := by
    refine Quiet.step_of (by change (0x800035c4#32).getLsbD 0=false;decide) rp2147497412 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) ram 0 [] [] = ⟨.ok c18 ram [],[]⟩
    have v10 : c17.get 10=0#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c17.get 11=0#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v10,v11]
    change Observed.interp B img o (.done (c17.wr 10 (alu .or 0#32 0#32) 0x800035c6#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .or 0#32 0#32=0#32)];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,ram⟩ ⟨c19,ram⟩ := by
    refine Quiet.step_of (by change (0x800035c6#32).getLsbD 0=false;decide) rp2147497414 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) ram 0 [] [] = ⟨.ok c19 ram [],[]⟩
    have v10 : c18.get 10=0#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v10,Core.get_zero,(by decide +kernel : taken .ne 0#32 (0 : Word)=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,ram⟩ ⟨c20,ram⟩ := by
    refine Quiet.step_of (by change (0x800035ca#32).getLsbD 0=false;decide) rp2147497418 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) ram 0 [] [] = ⟨.ok c20 ram [],[]⟩
    have v14 : c19.get 14=dst := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c19.get 12=13#32 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v14,v12]
    change Observed.interp B img o (.done (c19.wr 14 (alu .add dst 13#32) 0x800035cc#32)) ram 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : alu .add dst 13#32=(dst+13#32))];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,ram⟩ ⟨c21,ram⟩ := by
    refine Quiet.step_of (by change (0x800035cc#32).getLsbD 0=false;decide) rp2147497420 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) ram 0 [] [] = ⟨.ok c21 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c20.wr 10 (alu .add 0#32 82#32) 0x800035d0#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 82#32=82#32)];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,ram⟩ ⟨c22,ram⟩ := by
    refine Quiet.step_of (by change (0x800035d0#32).getLsbD 0=false;decide) rp2147497424 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) ram 0 [] [] = ⟨.ok c22 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c21.wr 11 (alu .add 0#32 101#32) 0x800035d4#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 101#32=101#32)];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,ram⟩ ⟨c23,ram⟩ := by
    refine Quiet.step_of (by change (0x800035d4#32).getLsbD 0=false;decide) rp2147497428 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) ram 0 [] [] = ⟨.ok c23 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c22.wr 13 (alu .add 0#32 113#32) 0x800035d8#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 113#32=113#32)];first | rfl | (rw [hp];rfl)
  have t23 : Quiet.Step B img ⟨c23,ram⟩ ⟨c24,ram⟩ := by
    refine Quiet.step_of (by change (0x800035d8#32).getLsbD 0=false;decide) rp2147497432 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) ram 0 [] [] = ⟨.ok c24 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c23.wr 15 (alu .add 0#32 117#32) 0x800035dc#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 117#32=117#32)];first | rfl | (rw [hp];rfl)
  have t24 : Quiet.Step B img ⟨c24,ram⟩ ⟨c25,r1⟩ := by
    refine Quiet.step_of (by change (0x800035dc#32).getLsbD 0=false;decide) rp2147497436 fun o => ?_
    change Observed.interp B img o (exec c24 _ _) ram 0 [] [] = ⟨.ok c25 r1 [],[]⟩
    have v14 : c24.get 14=(dst+13#32) := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v10 : c24.get 10=82#32 := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v10]
    change Observed.interp B img o (.store .b ((dst+13#32)+0#32) 82#32 false (.done (c24.goto 0x800035e0#32))) ram 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+0#32=dst+13#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 13) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t25 : Quiet.Step B img ⟨c25,r1⟩ ⟨c26,r2⟩ := by
    refine Quiet.step_of (by change (0x800035e0#32).getLsbD 0=false;decide) rp2147497440 fun o => ?_
    change Observed.interp B img o (exec c25 _ _) r1 0 [] [] = ⟨.ok c26 r2 [],[]⟩
    have v14 : c25.get 14=(dst+13#32) := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c25.get 11=101#32 := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v11]
    change Observed.interp B img o (.store .b ((dst+13#32)+1#32) 101#32 false (.done (c25.goto 0x800035e4#32))) r1 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+1#32=dst+14#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 14) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t26 : Quiet.Step B img ⟨c26,r2⟩ ⟨c27,r3⟩ := by
    refine Quiet.step_of (by change (0x800035e4#32).getLsbD 0=false;decide) rp2147497444 fun o => ?_
    change Observed.interp B img o (exec c26 _ _) r2 0 [] [] = ⟨.ok c27 r3 [],[]⟩
    have v14 : c26.get 14=(dst+13#32) := by simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c26.get 13=113#32 := by simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+13#32)+2#32) 113#32 false (.done (c26.goto 0x800035e8#32))) r2 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+2#32=dst+15#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 15) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t27 : Quiet.Step B img ⟨c27,r3⟩ ⟨c28,r4⟩ := by
    refine Quiet.step_of (by change (0x800035e8#32).getLsbD 0=false;decide) rp2147497448 fun o => ?_
    change Observed.interp B img o (exec c27 _ _) r3 0 [] [] = ⟨.ok c28 r4 [],[]⟩
    have v14 : c27.get 14=(dst+13#32) := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c27.get 15=117#32 := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v15]
    change Observed.interp B img o (.store .b ((dst+13#32)+3#32) 117#32 false (.done (c27.goto 0x800035ec#32))) r3 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+3#32=dst+16#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 16) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t28 : Quiet.Step B img ⟨c28,r4⟩ ⟨c29,r4⟩ := by
    refine Quiet.step_of (by change (0x800035ec#32).getLsbD 0=false;decide) rp2147497452 fun o => ?_
    change Observed.interp B img o (exec c28 _ _) r4 0 [] [] = ⟨.ok c29 r4 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c28.wr 10 (alu .add 0#32 115#32) 0x800035f0#32)) r4 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 115#32=115#32)];first | rfl | (rw [hp];rfl)
  have t29 : Quiet.Step B img ⟨c29,r4⟩ ⟨c30,r4⟩ := by
    refine Quiet.step_of (by change (0x800035f0#32).getLsbD 0=false;decide) rp2147497456 fun o => ?_
    change Observed.interp B img o (exec c29 _ _) r4 0 [] [] = ⟨.ok c30 r4 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c29.wr 13 (alu .add 0#32 116#32) 0x800035f4#32)) r4 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 116#32=116#32)];first | rfl | (rw [hp];rfl)
  have t30 : Quiet.Step B img ⟨c30,r4⟩ ⟨c31,r4⟩ := by
    refine Quiet.step_of (by change (0x800035f4#32).getLsbD 0=false;decide) rp2147497460 fun o => ?_
    change Observed.interp B img o (exec c30 _ _) r4 0 [] [] = ⟨.ok c31 r4 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c30.wr 16 (alu .add 0#32 32#32) 0x800035f8#32)) r4 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 32#32=32#32)];first | rfl | (rw [hp];rfl)
  have t31 : Quiet.Step B img ⟨c31,r4⟩ ⟨c32,r5⟩ := by
    refine Quiet.step_of (by change (0x800035f8#32).getLsbD 0=false;decide) rp2147497464 fun o => ?_
    change Observed.interp B img o (exec c31 _ _) r4 0 [] [] = ⟨.ok c32 r5 [],[]⟩
    have v14 : c31.get 14=(dst+13#32) := by simp [c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c31.get 11=101#32 := by simp [c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v11]
    change Observed.interp B img o (.store .b ((dst+13#32)+4#32) 101#32 false (.done (c31.goto 0x800035fc#32))) r4 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+4#32=dst+17#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 17) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t32 : Quiet.Step B img ⟨c32,r5⟩ ⟨c33,r6⟩ := by
    refine Quiet.step_of (by change (0x800035fc#32).getLsbD 0=false;decide) rp2147497468 fun o => ?_
    change Observed.interp B img o (exec c32 _ _) r5 0 [] [] = ⟨.ok c33 r6 [],[]⟩
    have v14 : c32.get 14=(dst+13#32) := by simp [c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v10 : c32.get 10=115#32 := by simp [c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v10]
    change Observed.interp B img o (.store .b ((dst+13#32)+5#32) 115#32 false (.done (c32.goto 0x80003600#32))) r5 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+5#32=dst+18#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 18) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t33 : Quiet.Step B img ⟨c33,r6⟩ ⟨c34,r7⟩ := by
    refine Quiet.step_of (by change (0x80003600#32).getLsbD 0=false;decide) rp2147497472 fun o => ?_
    change Observed.interp B img o (exec c33 _ _) r6 0 [] [] = ⟨.ok c34 r7 [],[]⟩
    have v14 : c33.get 14=(dst+13#32) := by simp [c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c33.get 13=116#32 := by simp [c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+13#32)+6#32) 116#32 false (.done (c33.goto 0x80003604#32))) r6 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+6#32=dst+19#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 19) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t34 : Quiet.Step B img ⟨c34,r7⟩ ⟨c35,r8⟩ := by
    refine Quiet.step_of (by change (0x80003604#32).getLsbD 0=false;decide) rp2147497476 fun o => ?_
    change Observed.interp B img o (exec c34 _ _) r7 0 [] [] = ⟨.ok c35 r8 [],[]⟩
    have v14 : c34.get 14=(dst+13#32) := by simp [c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v16 : c34.get 16=32#32 := by simp [c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v16]
    change Observed.interp B img o (.store .b ((dst+13#32)+7#32) 32#32 false (.done (c34.goto 0x80003608#32))) r7 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+7#32=dst+20#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 20) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t35 : Quiet.Step B img ⟨c35,r8⟩ ⟨c36,r8⟩ := by
    refine Quiet.step_of (by change (0x80003608#32).getLsbD 0=false;decide) rp2147497480 fun o => ?_
    change Observed.interp B img o (exec c35 _ _) r8 0 [] [] = ⟨.ok c36 r8 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c35.wr 10 (alu .add 0#32 84#32) 0x8000360c#32)) r8 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 84#32=84#32)];first | rfl | (rw [hp];rfl)
  have t36 : Quiet.Step B img ⟨c36,r8⟩ ⟨c37,r8⟩ := by
    refine Quiet.step_of (by change (0x8000360c#32).getLsbD 0=false;decide) rp2147497484 fun o => ?_
    change Observed.interp B img o (exec c36 _ _) r8 0 [] [] = ⟨.ok c37 r8 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c36.wr 16 (alu .add 0#32 105#32) 0x80003610#32)) r8 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 105#32=105#32)];first | rfl | (rw [hp];rfl)
  have t37 : Quiet.Step B img ⟨c37,r8⟩ ⟨c38,r8⟩ := by
    refine Quiet.step_of (by change (0x80003610#32).getLsbD 0=false;decide) rp2147497488 fun o => ?_
    change Observed.interp B img o (exec c37 _ _) r8 0 [] [] = ⟨.ok c38 r8 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c37.wr 17 (alu .add 0#32 109#32) 0x80003614#32)) r8 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 109#32=109#32)];first | rfl | (rw [hp];rfl)
  have t38 : Quiet.Step B img ⟨c38,r8⟩ ⟨c39,r8⟩ := by
    refine Quiet.step_of (by change (0x80003614#32).getLsbD 0=false;decide) rp2147497492 fun o => ?_
    change Observed.interp B img o (exec c38 _ _) r8 0 [] [] = ⟨.ok c39 r8 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c38.wr 5 (alu .add 0#32 111#32) 0x80003618#32)) r8 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 111#32=111#32)];first | rfl | (rw [hp];rfl)
  have t39 : Quiet.Step B img ⟨c39,r8⟩ ⟨c40,r9⟩ := by
    refine Quiet.step_of (by change (0x80003618#32).getLsbD 0=false;decide) rp2147497496 fun o => ?_
    change Observed.interp B img o (exec c39 _ _) r8 0 [] [] = ⟨.ok c40 r9 [],[]⟩
    have v14 : c39.get 14=(dst+13#32) := by simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v10 : c39.get 10=84#32 := by simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v10]
    change Observed.interp B img o (.store .b ((dst+13#32)+8#32) 84#32 false (.done (c39.goto 0x8000361c#32))) r8 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+8#32=dst+21#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 21) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t40 : Quiet.Step B img ⟨c40,r9⟩ ⟨c41,r10⟩ := by
    refine Quiet.step_of (by change (0x8000361c#32).getLsbD 0=false;decide) rp2147497500 fun o => ?_
    change Observed.interp B img o (exec c40 _ _) r9 0 [] [] = ⟨.ok c41 r10 [],[]⟩
    have v14 : c40.get 14=(dst+13#32) := by simp [c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v16 : c40.get 16=105#32 := by simp [c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v16]
    change Observed.interp B img o (.store .b ((dst+13#32)+9#32) 105#32 false (.done (c40.goto 0x80003620#32))) r9 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+9#32=dst+22#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 22) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t41 : Quiet.Step B img ⟨c41,r10⟩ ⟨c42,r11⟩ := by
    refine Quiet.step_of (by change (0x80003620#32).getLsbD 0=false;decide) rp2147497504 fun o => ?_
    change Observed.interp B img o (exec c41 _ _) r10 0 [] [] = ⟨.ok c42 r11 [],[]⟩
    have v14 : c41.get 14=(dst+13#32) := by simp [c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v17 : c41.get 17=109#32 := by simp [c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v17]
    change Observed.interp B img o (.store .b ((dst+13#32)+10#32) 109#32 false (.done (c41.goto 0x80003624#32))) r10 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+10#32=dst+23#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 23) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t42 : Quiet.Step B img ⟨c42,r11⟩ ⟨c43,r12⟩ := by
    refine Quiet.step_of (by change (0x80003624#32).getLsbD 0=false;decide) rp2147497508 fun o => ?_
    change Observed.interp B img o (exec c42 _ _) r11 0 [] [] = ⟨.ok c43 r12 [],[]⟩
    have v14 : c42.get 14=(dst+13#32) := by simp [c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c42.get 11=101#32 := by simp [c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v11]
    change Observed.interp B img o (.store .b ((dst+13#32)+11#32) 101#32 false (.done (c42.goto 0x80003628#32))) r11 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+11#32=dst+24#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 24) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t43 : Quiet.Step B img ⟨c43,r12⟩ ⟨c44,r13⟩ := by
    refine Quiet.step_of (by change (0x80003628#32).getLsbD 0=false;decide) rp2147497512 fun o => ?_
    change Observed.interp B img o (exec c43 _ _) r12 0 [] [] = ⟨.ok c44 r13 [],[]⟩
    have v14 : c43.get 14=(dst+13#32) := by simp [c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v5 : c43.get 5=111#32 := by simp [c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v5]
    change Observed.interp B img o (.store .b ((dst+13#32)+12#32) 111#32 false (.done (c43.goto 0x8000362c#32))) r12 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+12#32=dst+25#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 25) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t44 : Quiet.Step B img ⟨c44,r13⟩ ⟨c45,r14⟩ := by
    refine Quiet.step_of (by change (0x8000362c#32).getLsbD 0=false;decide) rp2147497516 fun o => ?_
    change Observed.interp B img o (exec c44 _ _) r13 0 [] [] = ⟨.ok c45 r14 [],[]⟩
    have v14 : c44.get 14=(dst+13#32) := by simp [c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c44.get 15=117#32 := by simp [c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v15]
    change Observed.interp B img o (.store .b ((dst+13#32)+13#32) 117#32 false (.done (c44.goto 0x80003630#32))) r13 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+13#32=dst+26#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 26) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t45 : Quiet.Step B img ⟨c45,r14⟩ ⟨c46,r15⟩ := by
    refine Quiet.step_of (by change (0x80003630#32).getLsbD 0=false;decide) rp2147497520 fun o => ?_
    change Observed.interp B img o (exec c45 _ _) r14 0 [] [] = ⟨.ok c46 r15 [],[]⟩
    have v14 : c45.get 14=(dst+13#32) := by simp [c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c45.get 13=116#32 := by simp [c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+13#32)+14#32) 116#32 false (.done (c45.goto 0x80003634#32))) r14 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+13#32)+14#32=dst+27#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 27) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t46 : Quiet.Step B img ⟨c46,r15⟩ ⟨c47,r15⟩ := by
    refine Quiet.step_of (by change (0x80003634#32).getLsbD 0=false;decide) rp2147497524 fun o => ?_
    change Observed.interp B img o (exec c46 _ _) r15 0 [] [] = ⟨.ok c47 r15 [],[]⟩
    have v12 : c46.get 12=13#32 := by simp [c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v12]
    change Observed.interp B img o (.done (c46.wr 12 (alu .add 13#32 15#32) 0x80003636#32)) r15 0 [] [] = _
    rw [(by decide +kernel : alu .add 13#32 15#32=28#32)];first | rfl | (rw [hp];rfl)
  have t47 : Quiet.Step B img ⟨c47,r15⟩ ⟨c48,r15⟩ := by
    refine Quiet.step_of (by change (0x80003636#32).getLsbD 0=false;decide) rp2147497526 fun o => ?_
    change Observed.interp B img o (exec c47 _ _) r15 0 [] [] = ⟨.ok c48 r15 [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c47 (2147497526#32+2066#32)) r15 0 [] [] = _
    rw [show 2147497526#32+2066#32=2147499592#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t48 : Quiet.Step B img ⟨c48,r15⟩ ⟨c49,r15⟩ := by
    refine Quiet.step_of (by change (0x80003e48#32).getLsbD 0=false;decide) rp2147499592 fun o => ?_
    change Observed.interp B img o (exec c48 _ _) r15 0 [] [] = ⟨.ok c49 r15 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c48.wr 10 (alu .add 0#32 1#32) 0x80003e4a#32)) r15 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 1#32=1#32)];first | rfl | (rw [hp];rfl)
  have t49 : Quiet.Step B img ⟨c49,r15⟩ ⟨c50,r15⟩ := by
    refine Quiet.step_of (by change (0x80003e4a#32).getLsbD 0=false;decide) rp2147499594 fun o => ?_
    change Observed.interp B img o (exec c49 _ _) r15 0 [] [] = ⟨.ok c50 r15 [],[]⟩
    have v12 : c49.get 12=28#32 := by simp [c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,Core.get_zero,v12]
    change Observed.interp B img o (.done (c49.wr 11 (alu .add 0#32 28#32) 0x80003e4c#32)) r15 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 28#32=28#32)];first | rfl | (rw [hp];rfl)
  have t50 : Quiet.Step B img ⟨c50,r15⟩ ⟨c51,r15⟩ := by
    refine Quiet.step_of (by change (0x80003e4c#32).getLsbD 0=false;decide) rp2147499596 fun o => ?_
    change Observed.interp B img o (exec c50 _ _) r15 0 [] [] = ⟨.ok c51 r15 [],[]⟩
    have v1 : c50.get 1=c.get 1 := by simp [c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_jalr,v1,BitVec.add_zero]
    change Observed.interp B img o (jump c50 (c.get 1 &&& ~~~1)) r15 0 [] [] = _
    rw [jump_ok _ _ (clear_bit0 _)];first | rfl | (rw [hp];rfl)
  refine ⟨c51,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.step t23 (.step t24 (.step t25 (.step t26 (.step t27 (.step t28 (.step t29 (.step t30 (.step t31 (.step t32 (.step t33 (.step t34 (.step t35 (.step t36 (.step t37 (.step t38 (.step t39 (.step t40 (.step t41 (.step t42 (.step t43 (.step t44 (.step t45 (.step t46 (.step t47 (.step t48 (.step t49 (.single t50)))))))))))))))))))))))))))))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · intro reg h14 h15 h10 h11 h13 h16 h17 h5 h12;simp [c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15,h10,h11,h13,h16,h17,h5,h12]
end E5R.Thermostat.HttpReason408
