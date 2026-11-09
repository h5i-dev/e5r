import Projects.thermostat.MainRelayCapture
import Projects.thermostat.RouteResult
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.RelayCaptureEmpty
open E5R E5R.Thermostat
/-- Empty parameter takes the actual refusal branch without writing capture RAM. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (full : Word)
    (h9 : c.get 9=full) (h18 : c.get 18=10#32) (h22 : c.get 22=10#32) (h11 : c.get 11=7#32)
    (h23 : c.get 23=7#32) (h10 : c.get 10=7#32) (h21 : c.get 21=0x80005b9c#32) (h25 : c.get 25=1#32)
    (h26 : c.get 26=123#32) (h27 : c.get 27=125#32) (h8 : c.get 8=0#32) (hsize : 7≤full.toNat)
    (patternBytes : ReadBytes.Span B img ram 0x80005b9c#32 (WireSpec.ascii "/relay/{i}"))
    (hp : c.pc=0x800028a8#32) :
    ∃ d, Quiet.Steps B img 17 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000293a#32 ∧
      d.get 10=0#32 ∧ d.get 11=0#32 ∧
      (∀ r : Reg,r≠12 → r≠13 → r≠11 → r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
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
  let c14 := c13.goto 0x80002958#32
  let c15 := c14.goto 0x80002936#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147494056) fun o => ?_
    change interp B img o (exec c _ _) ram 0 [] = .ok c1 ram []
    have v22 : c.get 22=10#32 := by simp [Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    have v11 : c.get 11=7#32 := by simp [Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    rw [exec_branch,v22,v11,(show taken .ltu 10#32 7#32=false by decide +kernel),hp]
    rfl
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028ac#32).getLsbD 0=false;decide) rt2147494060 fun o => ?_
    change interp B img o (exec c1 _ _) ram 0 [] = .ok c2 ram []
    have v18 : c1.get 18=10#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    have v22 : c1.get 22=10#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    rw [exec_branch,v18,v22,(show taken .ltu 10#32 10#32=false by decide +kernel)]
    rfl
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028b0#32).getLsbD 0=false;decide) rt2147494064 fun o => ?_
    change interp B img o (exec c2 _ _) ram 0 [] = .ok c3 ram []
    have v23 : c2.get 23=7#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    have v10 : c2.get 10=7#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    rw [exec_branch,v23,v10,(show taken .ltu 7#32 7#32=false by decide +kernel)]
    rfl
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028b4#32).getLsbD 0=false;decide) rt2147494068 fun o => ?_
    change interp B img o (exec c3 _ _) ram 0 [] = .ok c4 ram []
    have v9 : c3.get 9=full := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    have v23 : c3.get 23=7#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    rw [exec_branch,v9,v23,(show taken .ltu full 7#32=false by
      change decide (full.toNat<7)=false
      exact decide_eq_false (by omega))]
    rfl
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028b8#32).getLsbD 0=false;decide) rt2147494072 fun o => ?_
    change interp B img o (exec c4 _ _) ram 0 [] = .ok c5 ram []
    have v22 : c4.get 22=10#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    have v11 : c4.get 11=7#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    rw [exec_op,v22,v11,(show alu .sub 10#32 7#32=3#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028bc#32).getLsbD 0=false;decide) rt2147494076 fun o => ?_
    change interp B img o (exec c5 _ _) ram 0 [] = .ok c6 ram []
    have v21 : c5.get 21=2147507100#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    have v11 : c5.get 11=7#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    rw [exec_op,v21,v11,(show alu .add 2147507100#32 7#32=2147507107#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028c0#32).getLsbD 0=false;decide) rt2147494080 fun o => ?_
    change interp B img o (exec c6 _ _) ram 0 [] = .ok c7 ram []
    have v25 : c6.get 25=1#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    have v12 : c6.get 12=3#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    rw [exec_branch,v25,v12,(show taken .geu 1#32 3#32=false by decide +kernel)]
    rfl
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028c4#32).getLsbD 0=false;decide) rt2147494084 fun o => ?_
    change interp B img o (exec c7 _ _) ram 0 [] = .ok c8 ram []
    have v13 : c7.get 13=2147507107#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    have byte : ReadBytes.Byte B img ram 2147507107#32 123#8 := by
      have data := patternBytes.bytes ⟨7,by first | decide +kernel | (change 7<7+param.length;omega)⟩
      change ReadBytes.Byte B img ram (0x80005b9c#32+7#32) 123#8 at data
      simpa only [show 0x80005b9c#32+7#32=2147507107#32 by decide +kernel] using data
    rw [exec_load,v13,(show 2147507107#32+0#32=2147507107#32 by decide +kernel),ReadBytes.load byte,ReadBytes.extend_byte];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028c8#32).getLsbD 0=false;decide) rt2147494088 fun o => ?_
    change interp B img o (exec c8 _ _) ram 0 [] = .ok c9 ram []
    have v11 : c8.get 11=123#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    have v26 : c8.get 26=123#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    rw [exec_branch,v11,v26,(show taken .ne 123#32 123#32=false by decide +kernel)]
    rfl
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028cc#32).getLsbD 0=false;decide) rt2147494092 fun o => ?_
    change interp B img o (exec c9 _ _) ram 0 [] = .ok c10 ram []
    have v21 : c9.get 21=2147507100#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    have v22 : c9.get 22=10#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    rw [exec_op,v21,v22,(show alu .add 2147507100#32 10#32=2147507110#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028d0#32).getLsbD 0=false;decide) rt2147494096 fun o => ?_
    change interp B img o (exec c10 _ _) ram 0 [] = .ok c11 ram []
    have v11 : c10.get 11=2147507110#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    have byte : ReadBytes.Byte B img ram 2147507109#32 125#8 := by
      have data := patternBytes.bytes ⟨9,by first | decide +kernel | (change 9<7+param.length;omega)⟩
      change ReadBytes.Byte B img ram (0x80005b9c#32+9#32) 125#8 at data
      simpa only [show 0x80005b9c#32+9#32=2147507109#32 by decide +kernel] using data
    rw [exec_load,v11,(show 2147507110#32+4294967295#32=2147507109#32 by decide +kernel),ReadBytes.load byte,ReadBytes.extend_byte];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028d4#32).getLsbD 0=false;decide) rt2147494100 fun o => ?_
    change interp B img o (exec c11 _ _) ram 0 [] = .ok c12 ram []
    have v11 : c11.get 11=125#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    have v27 : c11.get 27=125#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    rw [exec_branch,v11,v27,(show taken .ne 125#32 125#32=false by decide +kernel)]
    rfl
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028d8#32).getLsbD 0=false;decide) rt2147494104 fun o => ?_
    change interp B img o (exec c12 _ _) ram 0 [] = .ok c13 ram []
    have v0 : c12.get 0=0#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    rw [exec_opimm,v0,(show alu .add 0#32 0#32=0#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028da#32).getLsbD 0=false;decide) rt2147494106 fun o => ?_
    change interp B img o (exec c13 _ _) ram 0 [] = .ok c14 ram []
    have v23 : c13.get 23=7#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    have v10 : c13.get 10=7#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h18,h22,h11,h23,h10,h21,h25,h26,h27,h8,hsize]
    rw [exec_branch,v23,v10,(show taken .eq 7#32 7#32=true by decide +kernel)]
    simp only [ite_true,show c13.pc=0x800028da#32 by rfl,show 0x800028da#32+126#32=0x80002958#32 by decide +kernel]
    rw [jump_ok _ _ (by decide)];rfl
  have t14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002958#32).getLsbD 0=false;decide) rt2147494232 fun o => ?_
    change interp B img o (exec c14 _ _) ram 0 [] = .ok c15 ram []
    rw [exec_jal,show c14.pc=0x80002958#32 by rfl]
    change interp B img o (jump (c14.set 0 0x8000295a#32) 0x80002936#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];rfl
  have p11 : c15.get 11=0#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  have p8 : c15.get 8=0#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  obtain ⟨d,td,pd,d10,d11,dr,dc⟩ := RouteResult.contract B c15 ram 0#32 0#32 p11 p8 rfl
  have before : Quiet.Steps B img 15 ⟨c,ram⟩ ⟨c15,ram⟩ := .step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.single t14))))))))))))))
  refine ⟨d,before.trans td,pd,d10,d11,?_,?_⟩
  · intro reg n12 n13 n11 n10
    rw [dr reg n10 n11]
    simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,n12,n13,n11]
  · exact dc.trans (by rfl)
end E5R.Thermostat.RelayCaptureEmpty
