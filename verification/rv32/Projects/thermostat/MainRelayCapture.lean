import Projects.thermostat.MainRouterCode
import Projects.thermostat.QuietRam
import Projects.thermostat.QuietDet
import Projects.thermostat.ReadBytes
import Projects.thermostat.WireSpec
import Projects.thermostat.MemcmpCode
import Projects.thermostat.Memory
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainRelayCapture
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (params pathSize : Word) :=
  ramWrite (ramWrite (ram) (params) (7#32) .w) ((params+4#32)) (pathSize) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (params pathSize : Word) (h9 : c.get 9=pathSize) (h18 : c.get 18=10#32) (h22 : c.get 22=10#32) (h11 : c.get 11=7#32)
    (h23 : c.get 23=pathSize) (h10 : c.get 10=7#32) (h21 : c.get 21=0x80005b9c#32) (h25 : c.get 25=1#32)
    (h26 : c.get 26=123#32) (h27 : c.get 27=125#32) (h8 : c.get 8=0#32) (h19 : c.get 19=params) (hsize : 8≤pathSize.toNat)
    (block : Memory.Block B params 8) (ha : params.toNat%4=0)
    (patternBytes : ReadBytes.Span B img ram 0x80005b9c#32 (WireSpec.ascii "/relay/{i}"))
    (hp : c.pc=0x800028a8#32) :
    ∃ d, Quiet.Steps B img 29 ⟨c,ram⟩ ⟨d,memory ram params pathSize⟩ ∧ d.pc=0x8000293a#32 ∧
      d.get 12=4#32 ∧ d.get 13=2147507107#32 ∧ d.get 11=1#32 ∧ d.get 8=1#32 ∧ d.get 10=1#32 ∧ (∀ r : Reg, r≠12 → r≠13 → r≠11 → r≠8 → r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x800028ac#32
  let c2 := c1.goto 0x800028b0#32
  let c3 := c2.goto 0x800028b4#32
  let c4 := c3.goto 0x800028b8#32
  let c5 := c4.wr 12 (3#32) 0x800028bc#32
  let c6 := c5.wr 13 (2147507107#32) 0x800028c0#32
  let c7 := c6.goto 0x800028c4#32
  let c8 := c7.wr 11 (123#32) 0x800028c8#32
  let c9 := c8.goto 0x800028cc#32
  let c10 := c9.wr 11 (2147507110#32) 0x800028d0#32
  let c11 := c10.wr 11 (125#32) 0x800028d4#32
  let c12 := c11.goto 0x800028d8#32
  let c13 := c12.wr 11 (0#32) 0x800028da#32
  let c14 := c13.goto 0x800028de#32
  let c15 := c14.wr 12 (4#32) 0x800028e0#32
  let c16 := c15.goto 0x800028e4#32
  let c17 := c16.wr 11 (3#32) 0x800028e6#32
  let c18 := c17.goto 0x800028ea#32
  let c19 := c18.wr 11 (0#32) 0x800028ee#32
  let c20 := c19.wr 8 (1#32) 0x800028f0#32
  let c21 := c20.wr 11 (params) 0x800028f2#32
  let r1 := ramWrite ram (params) (7#32) .w
  let c22 := c21.goto 0x800028f4#32
  let r2 := ramWrite r1 ((params+4#32)) (pathSize) .w
  let c23 := c22.goto 0x800028f8#32
  let c24 := c23.goto 0x80002912#32
  let c25 := c24.goto 0x8000292e#32
  let c26 := c25.wr 10 (0#32) 0x80002932#32
  let c27 := c26.wr 11 (1#32) 0x80002936#32
  let c28 := c27.wr 10 (1#32) 0x80002938#32
  let c29 := c28.wr 11 (1#32) 0x8000293a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147494056) fun o => ?_
    change interp B img o (exec c _ _) ram 0 [] = .ok c1 ram []
    have v22 : c.get 22=10#32 := by simp [Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have v11 : c.get 11=7#32 := by simp [Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_branch,v22,v11,(show taken .ltu 10#32 7#32=false by decide +kernel),hp]
    rfl
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028ac#32).getLsbD 0=false;decide) rt2147494060 fun o => ?_
    change interp B img o (exec c1 _ _) ram 0 [] = .ok c2 ram []
    have v18 : c1.get 18=10#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have v22 : c1.get 22=10#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_branch,v18,v22,(show taken .ltu 10#32 10#32=false by decide +kernel)]
    rfl
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028b0#32).getLsbD 0=false;decide) rt2147494064 fun o => ?_
    change interp B img o (exec c2 _ _) ram 0 [] = .ok c3 ram []
    have v23 : c2.get 23=pathSize := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have v10 : c2.get 10=7#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_branch,v23,v10,(show taken .ltu pathSize 7#32=false by
      have numeric : ¬pathSize.toNat<7 := (by omega)
      simp [taken,BitVec.ult,numeric])]
    rfl
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028b4#32).getLsbD 0=false;decide) rt2147494068 fun o => ?_
    change interp B img o (exec c3 _ _) ram 0 [] = .ok c4 ram []
    have v9 : c3.get 9=pathSize := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have v23 : c3.get 23=pathSize := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_branch,v9,v23,(show taken .ltu pathSize pathSize=false by simp [taken,BitVec.ult])]
    rfl
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028b8#32).getLsbD 0=false;decide) rt2147494072 fun o => ?_
    change interp B img o (exec c4 _ _) ram 0 [] = .ok c5 ram []
    have v22 : c4.get 22=10#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have v11 : c4.get 11=7#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_op,v22,v11,(show alu .sub 10#32 7#32=3#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028bc#32).getLsbD 0=false;decide) rt2147494076 fun o => ?_
    change interp B img o (exec c5 _ _) ram 0 [] = .ok c6 ram []
    have v21 : c5.get 21=2147507100#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have v11 : c5.get 11=7#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_op,v21,v11,(show alu .add 2147507100#32 7#32=2147507107#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028c0#32).getLsbD 0=false;decide) rt2147494080 fun o => ?_
    change interp B img o (exec c6 _ _) ram 0 [] = .ok c7 ram []
    have v25 : c6.get 25=1#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have v12 : c6.get 12=3#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_branch,v25,v12,(show taken .geu 1#32 3#32=false by decide +kernel)]
    rfl
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028c4#32).getLsbD 0=false;decide) rt2147494084 fun o => ?_
    change interp B img o (exec c7 _ _) ram 0 [] = .ok c8 ram []
    have v13 : c7.get 13=2147507107#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have byte : ReadBytes.Byte B img ram 2147507107#32 123#8 := by
      have data := patternBytes.bytes ⟨7,by first | decide +kernel | (change 7<7+param.length;omega)⟩
      change ReadBytes.Byte B img ram (0x80005b9c#32+7#32) 123#8 at data
      simpa only [show 0x80005b9c#32+7#32=2147507107#32 by decide +kernel] using data
    rw [exec_load,v13,(show 2147507107#32+0#32=2147507107#32 by decide +kernel),ReadBytes.load byte,ReadBytes.extend_byte];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028c8#32).getLsbD 0=false;decide) rt2147494088 fun o => ?_
    change interp B img o (exec c8 _ _) ram 0 [] = .ok c9 ram []
    have v11 : c8.get 11=123#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have v26 : c8.get 26=123#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_branch,v11,v26,(show taken .ne 123#32 123#32=false by decide +kernel)]
    rfl
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028cc#32).getLsbD 0=false;decide) rt2147494092 fun o => ?_
    change interp B img o (exec c9 _ _) ram 0 [] = .ok c10 ram []
    have v21 : c9.get 21=2147507100#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have v22 : c9.get 22=10#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_op,v21,v22,(show alu .add 2147507100#32 10#32=2147507110#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028d0#32).getLsbD 0=false;decide) rt2147494096 fun o => ?_
    change interp B img o (exec c10 _ _) ram 0 [] = .ok c11 ram []
    have v11 : c10.get 11=2147507110#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have byte : ReadBytes.Byte B img ram 2147507109#32 125#8 := by
      have data := patternBytes.bytes ⟨9,by first | decide +kernel | (change 9<7+param.length;omega)⟩
      change ReadBytes.Byte B img ram (0x80005b9c#32+9#32) 125#8 at data
      simpa only [show 0x80005b9c#32+9#32=2147507109#32 by decide +kernel] using data
    rw [exec_load,v11,(show 2147507110#32+4294967295#32=2147507109#32 by decide +kernel),ReadBytes.load byte,ReadBytes.extend_byte];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028d4#32).getLsbD 0=false;decide) rt2147494100 fun o => ?_
    change interp B img o (exec c11 _ _) ram 0 [] = .ok c12 ram []
    have v11 : c11.get 11=125#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have v27 : c11.get 27=125#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_branch,v11,v27,(show taken .ne 125#32 125#32=false by decide +kernel)]
    rfl
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028d8#32).getLsbD 0=false;decide) rt2147494104 fun o => ?_
    change interp B img o (exec c12 _ _) ram 0 [] = .ok c13 ram []
    have v0 : c12.get 0=0#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_opimm,v0,(show alu .add 0#32 0#32=0#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028da#32).getLsbD 0=false;decide) rt2147494106 fun o => ?_
    change interp B img o (exec c13 _ _) ram 0 [] = .ok c14 ram []
    have v23 : c13.get 23=pathSize := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have v10 : c13.get 10=7#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_branch,v23,v10,(show taken .eq pathSize 7#32=false by
      have neq : pathSize≠7#32 := by
        intro equal
        have eqn := congrArg BitVec.toNat equal
        change pathSize.toNat=7 at eqn
        omega
      simp [taken,neq,Ne.symm neq])]
    rfl
  have t14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028de#32).getLsbD 0=false;decide) rt2147494110 fun o => ?_
    change interp B img o (exec c14 _ _) ram 0 [] = .ok c15 ram []
    have v0 : c14.get 0=0#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_opimm,v0,(show alu .add 0#32 4#32=4#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,ram⟩ ⟨c16,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028e0#32).getLsbD 0=false;decide) rt2147494112 fun o => ?_
    change interp B img o (exec c15 _ _) ram 0 [] = .ok c16 ram []
    have v8 : c15.get 8=0#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have v12 : c15.get 12=4#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_branch,v8,v12,(show taken .eq 0#32 4#32=false by decide +kernel)]
    rfl
  have t16 : Quiet.Step B img ⟨c16,ram⟩ ⟨c17,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028e4#32).getLsbD 0=false;decide) rt2147494116 fun o => ?_
    change interp B img o (exec c16 _ _) ram 0 [] = .ok c17 ram []
    have v0 : c16.get 0=0#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_opimm,v0,(show alu .add 0#32 3#32=3#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,ram⟩ ⟨c18,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028e6#32).getLsbD 0=false;decide) rt2147494118 fun o => ?_
    change interp B img o (exec c17 _ _) ram 0 [] = .ok c18 ram []
    have v11 : c17.get 11=3#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have v8 : c17.get 8=0#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_branch,v11,v8,(show taken .ltu 3#32 0#32=false by decide +kernel)]
    rfl
  have t18 : Quiet.Step B img ⟨c18,ram⟩ ⟨c19,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028ea#32).getLsbD 0=false;decide) rt2147494122 fun o => ?_
    change interp B img o (exec c18 _ _) ram 0 [] = .ok c19 ram []
    have v8 : c18.get 8=0#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_opimm,v8,(show alu .sll 0#32 3#32=0#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,ram⟩ ⟨c20,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028ee#32).getLsbD 0=false;decide) rt2147494126 fun o => ?_
    change interp B img o (exec c19 _ _) ram 0 [] = .ok c20 ram []
    have v8 : c19.get 8=0#32 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_opimm,v8,(show alu .add 0#32 1#32=1#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,ram⟩ ⟨c21,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028f0#32).getLsbD 0=false;decide) rt2147494128 fun o => ?_
    change interp B img o (exec c20 _ _) ram 0 [] = .ok c21 ram []
    have v11 : c20.get 11=0#32 := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have v19 : c20.get 19=params := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_op,v11,v19,(show alu .add 0#32 params=params by simp only [alu,BitVec.zero_add,BitVec.add_zero])];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,ram⟩ ⟨c22,r1⟩ := by
    refine QuietDet.step_of (by change (0x800028f2#32).getLsbD 0=false;decide) rt2147494130 fun o => ?_
    change interp B img o (exec c21 _ _) ram 0 [] = .ok c22 r1 []
    have v11 : c21.get 11=params := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have v10 : c21.get 10=7#32 := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_store,v11,v10,(show params+0#32=params by first | rfl | simp only [BitVec.add_zero]),interp_store_ram (B := B) (img := img) (w := .w) o ha (by simpa only [BitVec.add_zero] using Memory.block_access block (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,r1⟩ ⟨c23,r2⟩ := by
    refine QuietDet.step_of (by change (0x800028f4#32).getLsbD 0=false;decide) rt2147494132 fun o => ?_
    change interp B img o (exec c22 _ _) r1 0 [] = .ok c23 r2 []
    have v11 : c22.get 11=params := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have v23 : c22.get 23=pathSize := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_store,v11,v23,(show params+4#32=(params+4#32) by first | rfl | simp only [BitVec.add_zero]),interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned params 1 ha) (by simpa only [BitVec.add_zero] using Memory.block_access block (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t23 : Quiet.Step B img ⟨c23,r2⟩ ⟨c24,r2⟩ := by
    refine QuietDet.step_of (by change (0x800028f8#32).getLsbD 0=false;decide) rt2147494136 fun o => ?_
    change interp B img o (exec c23 _ _) r2 0 [] = .ok c24 r2 []
    rw [exec_jal]
    change interp B img o (jump c23 2147494162#32) r2 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t24 : Quiet.Step B img ⟨c24,r2⟩ ⟨c25,r2⟩ := by
    refine QuietDet.step_of (by change (0x80002912#32).getLsbD 0=false;decide) rt2147494162 fun o => ?_
    change interp B img o (exec c24 _ _) r2 0 [] = .ok c25 r2 []
    have v22 : c24.get 22=10#32 := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have v18 : c24.get 18=10#32 := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_branch,v22,v18,(show taken .eq 10#32 10#32=true by decide +kernel)]
    rw [ite_eq_left rfl,show c24.pc=2147494162#32 from rfl,show 2147494162#32+28#32=2147494190#32 by decide +kernel]
    change interp B img o (jump c24 2147494190#32) r2 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t25 : Quiet.Step B img ⟨c25,r2⟩ ⟨c26,r2⟩ := by
    refine QuietDet.step_of (by change (0x8000292e#32).getLsbD 0=false;decide) rt2147494190 fun o => ?_
    change interp B img o (exec c25 _ _) r2 0 [] = .ok c26 r2 []
    have v23 : c25.get 23=pathSize := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have v9 : c25.get 9=pathSize := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_op,v23,v9,(show alu .xor pathSize pathSize=0#32 by simp only [alu,BitVec.xor_self])];first | rfl | (rw [hp];rfl)
  have t26 : Quiet.Step B img ⟨c26,r2⟩ ⟨c27,r2⟩ := by
    refine QuietDet.step_of (by change (0x80002932#32).getLsbD 0=false;decide) rt2147494194 fun o => ?_
    change interp B img o (exec c26 _ _) r2 0 [] = .ok c27 r2 []
    have v10 : c26.get 10=0#32 := by simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_opimm,v10,(show alu .sltu 0#32 1#32=1#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t27 : Quiet.Step B img ⟨c27,r2⟩ ⟨c28,r2⟩ := by
    refine QuietDet.step_of (by change (0x80002936#32).getLsbD 0=false;decide) rt2147494198 fun o => ?_
    change interp B img o (exec c27 _ _) r2 0 [] = .ok c28 r2 []
    have v0 : c27.get 0=0#32 := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have v11 : c27.get 11=1#32 := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_op,v0,v11,(show alu .add 0#32 1#32=1#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t28 : Quiet.Step B img ⟨c28,r2⟩ ⟨c29,r2⟩ := by
    refine QuietDet.step_of (by change (0x80002938#32).getLsbD 0=false;decide) rt2147494200 fun o => ?_
    change interp B img o (exec c28 _ _) r2 0 [] = .ok c29 r2 []
    have v0 : c28.get 0=0#32 := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    have v8 : c28.get 8=1#32 := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
    rw [exec_op,v0,v8,(show alu .add 0#32 1#32=1#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  refine ⟨c29,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.step t23 (.step t24 (.step t25 (.step t26 (.step t27 (.single t28)))))))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
  · simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
  · simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
  · simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
  · simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize]
  · intro reg h12 h13 h11 h8 h10;simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,h19,hsize,h12,h13,h11,h8,h10]
end E5R.Thermostat.MainRelayCapture
