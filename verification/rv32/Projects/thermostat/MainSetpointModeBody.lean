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
namespace E5R.Thermostat.MainSetpointModeBody
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (path params : Word) (h10 : c.get 10=0x80005b89#32) (h11 : c.get 11=9#32) (h12 : c.get 12=path) (h13 : c.get 13=5#32) (h14 : c.get 14=params)
    (patternBytes : ReadBytes.Span B img ram 0x80005b89#32 (WireSpec.ascii "/setpoint"))
    (pathBytes : ReadBytes.Span B img ram path (WireSpec.ascii "/mode"))
    (hp : c.pc=0x80002856#32) :
    ∃ d, Quiet.Steps B img 124 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000293a#32 ∧
      d.get 19=params ∧ d.get 9=5#32 ∧ d.get 20=path ∧ d.get 18=9#32 ∧ d.get 21=2147507081#32 ∧ d.get 8=0#32 ∧ d.get 10=0#32 ∧ d.get 11=0#32 ∧ d.get 24=47#32 ∧ d.get 25=1#32 ∧ d.get 26=123#32 ∧ d.get 27=125#32 ∧ d.get 22=9#32 ∧ d.get 12=8#32 ∧ d.get 23=5#32 ∧ d.get 13=2147507082#32 ∧ d.get 1=2147494160#32 ∧ (∀ r : Reg, r≠19 → r≠9 → r≠20 → r≠18 → r≠21 → r≠8 → r≠10 → r≠11 → r≠24 → r≠25 → r≠26 → r≠27 → r≠22 → r≠12 → r≠23 → r≠13 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 19 (params) 0x80002858#32
  let c2 := c1.wr 9 (5#32) 0x8000285a#32
  let c3 := c2.wr 20 (path) 0x8000285c#32
  let c4 := c3.wr 18 (9#32) 0x8000285e#32
  let c5 := c4.wr 21 (2147507081#32) 0x80002860#32
  let c6 := c5.wr 8 (0#32) 0x80002862#32
  let c7 := c6.wr 10 (0#32) 0x80002864#32
  let c8 := c7.wr 11 (0#32) 0x80002866#32
  let c9 := c8.wr 24 (47#32) 0x8000286a#32
  let c10 := c9.wr 25 (1#32) 0x8000286c#32
  let c11 := c10.wr 26 (123#32) 0x80002870#32
  let c12 := c11.wr 27 (125#32) 0x80002874#32
  let c13 := c12.wr 22 (0#32) 0x80002876#32
  let c14 := c13.goto 0x8000287a#32
  let c15 := c14.wr 12 (2147507081#32) 0x8000287e#32
  let c16 := c15.wr 12 (47#32) 0x80002882#32
  let c17 := c16.goto 0x8000288e#32
  let c18 := c17.wr 23 (0#32) 0x80002890#32
  let c19 := c18.goto 0x80002894#32
  let c20 := c19.wr 12 (path) 0x80002898#32
  let c21 := c20.wr 12 (47#32) 0x8000289c#32
  let c22 := c21.goto 0x800028a8#32
  let c23 := c22.goto 0x800028ac#32
  let c24 := c23.goto 0x800028b0#32
  let c25 := c24.goto 0x800028b4#32
  let c26 := c25.goto 0x800028b8#32
  let c27 := c26.wr 12 (0#32) 0x800028bc#32
  let c28 := c27.wr 13 (2147507081#32) 0x800028c0#32
  let c29 := c28.goto 0x800028fa#32
  let c30 := c29.wr 11 (0#32) 0x800028fe#32
  let c31 := c30.goto 0x80002902#32
  let c32 := c31.wr 11 (path) 0x80002906#32
  let c33 := c32.wr 10 (2147507081#32) 0x80002908#32
  let c34 := c33.wr 1 (2147506440#32) 0x8000290c#32
  let c35 := c34.wr 1 (2147494160#32) 0x80005162#32
  let c36 := c35.goto 0x80005178#32
  let c37 := c36.wr 10 (0#32) 0x8000517a#32
  let c38 := c37.goto 0x80002910#32
  let c39 := c38.goto 0x80002912#32
  let c40 := c39.goto 0x80002916#32
  let c41 := c40.goto 0x8000291a#32
  let c42 := c41.wr 11 (1#32) 0x8000291e#32
  let c43 := c42.wr 10 (1#32) 0x80002922#32
  let c44 := c43.wr 22 (1#32) 0x80002924#32
  let c45 := c44.goto 0x8000287a#32
  let c46 := c45.wr 12 (2147507082#32) 0x8000287e#32
  let c47 := c46.wr 12 (115#32) 0x80002882#32
  let c48 := c47.goto 0x80002886#32
  let c49 := c48.wr 22 (2#32) 0x80002888#32
  let c50 := c49.goto 0x8000287a#32
  let c51 := c50.wr 12 (2147507083#32) 0x8000287e#32
  let c52 := c51.wr 12 (101#32) 0x80002882#32
  let c53 := c52.goto 0x80002886#32
  let c54 := c53.wr 22 (3#32) 0x80002888#32
  let c55 := c54.goto 0x8000287a#32
  let c56 := c55.wr 12 (2147507084#32) 0x8000287e#32
  let c57 := c56.wr 12 (116#32) 0x80002882#32
  let c58 := c57.goto 0x80002886#32
  let c59 := c58.wr 22 (4#32) 0x80002888#32
  let c60 := c59.goto 0x8000287a#32
  let c61 := c60.wr 12 (2147507085#32) 0x8000287e#32
  let c62 := c61.wr 12 (112#32) 0x80002882#32
  let c63 := c62.goto 0x80002886#32
  let c64 := c63.wr 22 (5#32) 0x80002888#32
  let c65 := c64.goto 0x8000287a#32
  let c66 := c65.wr 12 (2147507086#32) 0x8000287e#32
  let c67 := c66.wr 12 (111#32) 0x80002882#32
  let c68 := c67.goto 0x80002886#32
  let c69 := c68.wr 22 (6#32) 0x80002888#32
  let c70 := c69.goto 0x8000287a#32
  let c71 := c70.wr 12 (2147507087#32) 0x8000287e#32
  let c72 := c71.wr 12 (105#32) 0x80002882#32
  let c73 := c72.goto 0x80002886#32
  let c74 := c73.wr 22 (7#32) 0x80002888#32
  let c75 := c74.goto 0x8000287a#32
  let c76 := c75.wr 12 (2147507088#32) 0x8000287e#32
  let c77 := c76.wr 12 (110#32) 0x80002882#32
  let c78 := c77.goto 0x80002886#32
  let c79 := c78.wr 22 (8#32) 0x80002888#32
  let c80 := c79.goto 0x8000287a#32
  let c81 := c80.wr 12 (2147507089#32) 0x8000287e#32
  let c82 := c81.wr 12 (116#32) 0x80002882#32
  let c83 := c82.goto 0x80002886#32
  let c84 := c83.wr 22 (9#32) 0x80002888#32
  let c85 := c84.goto 0x8000288c#32
  let c86 := c85.wr 22 (9#32) 0x8000288e#32
  let c87 := c86.wr 23 (1#32) 0x80002890#32
  let c88 := c87.goto 0x80002894#32
  let c89 := c88.wr 12 ((path+1#32)) 0x80002898#32
  let c90 := c89.wr 12 (109#32) 0x8000289c#32
  let c91 := c90.goto 0x800028a0#32
  let c92 := c91.wr 23 (2#32) 0x800028a2#32
  let c93 := c92.goto 0x80002894#32
  let c94 := c93.wr 12 ((path+2#32)) 0x80002898#32
  let c95 := c94.wr 12 (111#32) 0x8000289c#32
  let c96 := c95.goto 0x800028a0#32
  let c97 := c96.wr 23 (3#32) 0x800028a2#32
  let c98 := c97.goto 0x80002894#32
  let c99 := c98.wr 12 ((path+3#32)) 0x80002898#32
  let c100 := c99.wr 12 (100#32) 0x8000289c#32
  let c101 := c100.goto 0x800028a0#32
  let c102 := c101.wr 23 (4#32) 0x800028a2#32
  let c103 := c102.goto 0x80002894#32
  let c104 := c103.wr 12 ((path+4#32)) 0x80002898#32
  let c105 := c104.wr 12 (101#32) 0x8000289c#32
  let c106 := c105.goto 0x800028a0#32
  let c107 := c106.wr 23 (5#32) 0x800028a2#32
  let c108 := c107.goto 0x800028a6#32
  let c109 := c108.wr 23 (5#32) 0x800028a8#32
  let c110 := c109.goto 0x800028ac#32
  let c111 := c110.goto 0x800028b0#32
  let c112 := c111.goto 0x800028b4#32
  let c113 := c112.goto 0x800028b8#32
  let c114 := c113.wr 12 (8#32) 0x800028bc#32
  let c115 := c114.wr 13 (2147507082#32) 0x800028c0#32
  let c116 := c115.goto 0x800028c4#32
  let c117 := c116.wr 11 (115#32) 0x800028c8#32
  let c118 := c117.goto 0x800028fa#32
  let c119 := c118.wr 11 (4#32) 0x800028fe#32
  let c120 := c119.goto 0x8000292a#32
  let c121 := c120.wr 11 (0#32) 0x8000292c#32
  let c122 := c121.goto 0x80002936#32
  let c123 := c122.wr 10 (0#32) 0x80002938#32
  let c124 := c123.wr 11 (0#32) 0x8000293a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147493974) fun o => ?_
    change interp B img o (exec c _ _) ram 0 [] = .ok c1 ram []
    have v0 : c.get 0=0#32 := by simp [Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v14 : c.get 14=params := by simp [Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v0,v14,(show alu .add 0#32 params=params by simp only [alu,BitVec.zero_add,BitVec.add_zero])];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002858#32).getLsbD 0=false;decide) rt2147493976 fun o => ?_
    change interp B img o (exec c1 _ _) ram 0 [] = .ok c2 ram []
    have v0 : c1.get 0=0#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v13 : c1.get 13=5#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v0,v13,(show alu .add 0#32 5#32=5#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000285a#32).getLsbD 0=false;decide) rt2147493978 fun o => ?_
    change interp B img o (exec c2 _ _) ram 0 [] = .ok c3 ram []
    have v0 : c2.get 0=0#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v12 : c2.get 12=path := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v0,v12,(show alu .add 0#32 path=path by simp only [alu,BitVec.zero_add,BitVec.add_zero])];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000285c#32).getLsbD 0=false;decide) rt2147493980 fun o => ?_
    change interp B img o (exec c3 _ _) ram 0 [] = .ok c4 ram []
    have v0 : c3.get 0=0#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v11 : c3.get 11=9#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v0,v11,(show alu .add 0#32 9#32=9#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000285e#32).getLsbD 0=false;decide) rt2147493982 fun o => ?_
    change interp B img o (exec c4 _ _) ram 0 [] = .ok c5 ram []
    have v0 : c4.get 0=0#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v10 : c4.get 10=2147507081#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v0,v10,(show alu .add 0#32 2147507081#32=2147507081#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002860#32).getLsbD 0=false;decide) rt2147493984 fun o => ?_
    change interp B img o (exec c5 _ _) ram 0 [] = .ok c6 ram []
    have v0 : c5.get 0=0#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v0,(show alu .add 0#32 0#32=0#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002862#32).getLsbD 0=false;decide) rt2147493986 fun o => ?_
    change interp B img o (exec c6 _ _) ram 0 [] = .ok c7 ram []
    have v0 : c6.get 0=0#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v0,(show alu .add 0#32 0#32=0#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002864#32).getLsbD 0=false;decide) rt2147493988 fun o => ?_
    change interp B img o (exec c7 _ _) ram 0 [] = .ok c8 ram []
    have v0 : c7.get 0=0#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v0,(show alu .add 0#32 0#32=0#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002866#32).getLsbD 0=false;decide) rt2147493990 fun o => ?_
    change interp B img o (exec c8 _ _) ram 0 [] = .ok c9 ram []
    have v0 : c8.get 0=0#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v0,(show alu .add 0#32 47#32=47#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000286a#32).getLsbD 0=false;decide) rt2147493994 fun o => ?_
    change interp B img o (exec c9 _ _) ram 0 [] = .ok c10 ram []
    have v0 : c9.get 0=0#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v0,(show alu .add 0#32 1#32=1#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000286c#32).getLsbD 0=false;decide) rt2147493996 fun o => ?_
    change interp B img o (exec c10 _ _) ram 0 [] = .ok c11 ram []
    have v0 : c10.get 0=0#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v0,(show alu .add 0#32 123#32=123#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002870#32).getLsbD 0=false;decide) rt2147494000 fun o => ?_
    change interp B img o (exec c11 _ _) ram 0 [] = .ok c12 ram []
    have v0 : c11.get 0=0#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v0,(show alu .add 0#32 125#32=125#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002874#32).getLsbD 0=false;decide) rt2147494004 fun o => ?_
    change interp B img o (exec c12 _ _) ram 0 [] = .ok c13 ram []
    have v0 : c12.get 0=0#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v0,(show alu .add 0#32 0#32=0#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002876#32).getLsbD 0=false;decide) rt2147494006 fun o => ?_
    change interp B img o (exec c13 _ _) ram 0 [] = .ok c14 ram []
    have v18 : c13.get 18=9#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v0 : c13.get 0=0#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v18,v0,show taken .eq 9#32 0#32=false by decide +kernel]
    rfl
  have t14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000287a#32).getLsbD 0=false;decide) rt2147494010 fun o => ?_
    change interp B img o (exec c14 _ _) ram 0 [] = .ok c15 ram []
    have v21 : c14.get 21=2147507081#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v22 : c14.get 22=0#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v21,v22,(show alu .add 2147507081#32 0#32=2147507081#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,ram⟩ ⟨c16,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000287e#32).getLsbD 0=false;decide) rt2147494014 fun o => ?_
    change interp B img o (exec c15 _ _) ram 0 [] = .ok c16 ram []
    have v12 : c15.get 12=2147507081#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have byte : ReadBytes.Byte B img ram 2147507081#32 47#8 := by
      have data := patternBytes.bytes ⟨0,by decide⟩
      change ReadBytes.Byte B img ram (0x80005b89#32+0#32) 47#8 at data
      simpa only [show 0x80005b89#32+0#32=2147507081#32 by decide +kernel] using data
    rw [exec_load,v12,(show 2147507081#32+0#32=2147507081#32 by decide +kernel),ReadBytes.load byte,ReadBytes.extend_byte];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,ram⟩ ⟨c17,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002882#32).getLsbD 0=false;decide) rt2147494018 fun o => ?_
    change interp B img o (exec c16 _ _) ram 0 [] = .ok c17 ram []
    have v12 : c16.get 12=47#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v24 : c16.get 24=47#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v12,v24,show taken .eq 47#32 47#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c16.pc=2147494018#32 from rfl,show 2147494018#32+12#32=2147494030#32 by decide +kernel]
    change interp B img o (jump c16 2147494030#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,ram⟩ ⟨c18,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000288e#32).getLsbD 0=false;decide) rt2147494030 fun o => ?_
    change interp B img o (exec c17 _ _) ram 0 [] = .ok c18 ram []
    have v0 : c17.get 0=0#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v10 : c17.get 10=0#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v0,v10,(show alu .add 0#32 0#32=0#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,ram⟩ ⟨c19,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002890#32).getLsbD 0=false;decide) rt2147494032 fun o => ?_
    change interp B img o (exec c18 _ _) ram 0 [] = .ok c19 ram []
    have v10 : c18.get 10=0#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v9 : c18.get 9=5#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v10,v9,show taken .geu 0#32 5#32=false by decide +kernel]
    rfl
  have t19 : Quiet.Step B img ⟨c19,ram⟩ ⟨c20,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002894#32).getLsbD 0=false;decide) rt2147494036 fun o => ?_
    change interp B img o (exec c19 _ _) ram 0 [] = .ok c20 ram []
    have v20 : c19.get 20=path := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v23 : c19.get 23=0#32 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v20,v23,(show alu .add path 0#32=path by simp only [alu,BitVec.zero_add,BitVec.add_zero])];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,ram⟩ ⟨c21,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002898#32).getLsbD 0=false;decide) rt2147494040 fun o => ?_
    change interp B img o (exec c20 _ _) ram 0 [] = .ok c21 ram []
    have v12 : c20.get 12=path := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have byte : ReadBytes.Byte B img ram path 47#8 := by
      have data := pathBytes.bytes ⟨0,by decide⟩
      change ReadBytes.Byte B img ram (path+0#32) 47#8 at data
      simpa only [BitVec.add_zero] using data
    rw [exec_load,v12,(show path+0#32=path by first | rfl | simp only [BitVec.add_zero]),ReadBytes.load byte,ReadBytes.extend_byte];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,ram⟩ ⟨c22,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000289c#32).getLsbD 0=false;decide) rt2147494044 fun o => ?_
    change interp B img o (exec c21 _ _) ram 0 [] = .ok c22 ram []
    have v12 : c21.get 12=47#32 := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v24 : c21.get 24=47#32 := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v12,v24,show taken .eq 47#32 47#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c21.pc=2147494044#32 from rfl,show 2147494044#32+12#32=2147494056#32 by decide +kernel]
    change interp B img o (jump c21 2147494056#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,ram⟩ ⟨c23,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028a8#32).getLsbD 0=false;decide) rt2147494056 fun o => ?_
    change interp B img o (exec c22 _ _) ram 0 [] = .ok c23 ram []
    have v22 : c22.get 22=0#32 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v11 : c22.get 11=0#32 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v22,v11,show taken .ltu 0#32 0#32=false by decide +kernel]
    rfl
  have t23 : Quiet.Step B img ⟨c23,ram⟩ ⟨c24,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028ac#32).getLsbD 0=false;decide) rt2147494060 fun o => ?_
    change interp B img o (exec c23 _ _) ram 0 [] = .ok c24 ram []
    have v18 : c23.get 18=9#32 := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v22 : c23.get 22=0#32 := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v18,v22,show taken .ltu 9#32 0#32=false by decide +kernel]
    rfl
  have t24 : Quiet.Step B img ⟨c24,ram⟩ ⟨c25,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028b0#32).getLsbD 0=false;decide) rt2147494064 fun o => ?_
    change interp B img o (exec c24 _ _) ram 0 [] = .ok c25 ram []
    have v23 : c24.get 23=0#32 := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v10 : c24.get 10=0#32 := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v23,v10,show taken .ltu 0#32 0#32=false by decide +kernel]
    rfl
  have t25 : Quiet.Step B img ⟨c25,ram⟩ ⟨c26,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028b4#32).getLsbD 0=false;decide) rt2147494068 fun o => ?_
    change interp B img o (exec c25 _ _) ram 0 [] = .ok c26 ram []
    have v9 : c25.get 9=5#32 := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v23 : c25.get 23=0#32 := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v9,v23,show taken .ltu 5#32 0#32=false by decide +kernel]
    rfl
  have t26 : Quiet.Step B img ⟨c26,ram⟩ ⟨c27,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028b8#32).getLsbD 0=false;decide) rt2147494072 fun o => ?_
    change interp B img o (exec c26 _ _) ram 0 [] = .ok c27 ram []
    have v22 : c26.get 22=0#32 := by simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v11 : c26.get 11=0#32 := by simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v22,v11,(show alu .sub 0#32 0#32=0#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t27 : Quiet.Step B img ⟨c27,ram⟩ ⟨c28,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028bc#32).getLsbD 0=false;decide) rt2147494076 fun o => ?_
    change interp B img o (exec c27 _ _) ram 0 [] = .ok c28 ram []
    have v21 : c27.get 21=2147507081#32 := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v11 : c27.get 11=0#32 := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v21,v11,(show alu .add 2147507081#32 0#32=2147507081#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t28 : Quiet.Step B img ⟨c28,ram⟩ ⟨c29,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028c0#32).getLsbD 0=false;decide) rt2147494080 fun o => ?_
    change interp B img o (exec c28 _ _) ram 0 [] = .ok c29 ram []
    have v25 : c28.get 25=1#32 := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v12 : c28.get 12=0#32 := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v25,v12,show taken .geu 1#32 0#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c28.pc=2147494080#32 from rfl,show 2147494080#32+58#32=2147494138#32 by decide +kernel]
    change interp B img o (jump c28 2147494138#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t29 : Quiet.Step B img ⟨c29,ram⟩ ⟨c30,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028fa#32).getLsbD 0=false;decide) rt2147494138 fun o => ?_
    change interp B img o (exec c29 _ _) ram 0 [] = .ok c30 ram []
    have v23 : c29.get 23=0#32 := by simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v10 : c29.get 10=0#32 := by simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v23,v10,(show alu .sub 0#32 0#32=0#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t30 : Quiet.Step B img ⟨c30,ram⟩ ⟨c31,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028fe#32).getLsbD 0=false;decide) rt2147494142 fun o => ?_
    change interp B img o (exec c30 _ _) ram 0 [] = .ok c31 ram []
    have v12 : c30.get 12=0#32 := by simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v11 : c30.get 11=0#32 := by simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v12,v11,show taken .ne 0#32 0#32=false by decide +kernel]
    rfl
  have t31 : Quiet.Step B img ⟨c31,ram⟩ ⟨c32,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002902#32).getLsbD 0=false;decide) rt2147494146 fun o => ?_
    change interp B img o (exec c31 _ _) ram 0 [] = .ok c32 ram []
    have v20 : c31.get 20=path := by simp [c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v10 : c31.get 10=0#32 := by simp [c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v20,v10,(show alu .add path 0#32=path by simp only [alu,BitVec.zero_add,BitVec.add_zero])];first | rfl | (rw [hp];rfl)
  have t32 : Quiet.Step B img ⟨c32,ram⟩ ⟨c33,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002906#32).getLsbD 0=false;decide) rt2147494150 fun o => ?_
    change interp B img o (exec c32 _ _) ram 0 [] = .ok c33 ram []
    have v0 : c32.get 0=0#32 := by simp [c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v13 : c32.get 13=2147507081#32 := by simp [c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v0,v13,(show alu .add 0#32 2147507081#32=2147507081#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t33 : Quiet.Step B img ⟨c33,ram⟩ ⟨c34,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002908#32).getLsbD 0=false;decide) rt2147494152 fun o => ?_
    change interp B img o (exec c33 _ _) ram 0 [] = .ok c34 ram []
    rw [exec_auipc];first | rfl | (rw [hp];rfl)
  have t34 : Quiet.Step B img ⟨c34,ram⟩ ⟨c35,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000290c#32).getLsbD 0=false;decide) rt2147494156 fun o => ?_
    change interp B img o (exec c34 _ _) ram 0 [] = .ok c35 ram []
    have v1 : c34.get 1=2147506440#32 := by simp [c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_jalr,v1]
    change interp B img o (jump (c34.set 1 2147494160#32) 2147504482#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t35 : Quiet.Step B img ⟨c35,ram⟩ ⟨c36,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005162#32).getLsbD 0=false;decide) mc2147504482 fun o => ?_
    change interp B img o (exec c35 _ _) ram 0 [] = .ok c36 ram []
    have v12 : c35.get 12=0#32 := by simp [c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v0 : c35.get 0=0#32 := by simp [c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v12,v0,show taken .eq 0#32 0#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c35.pc=2147504482#32 from rfl,show 2147504482#32+22#32=2147504504#32 by decide +kernel]
    change interp B img o (jump c35 2147504504#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t36 : Quiet.Step B img ⟨c36,ram⟩ ⟨c37,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005178#32).getLsbD 0=false;decide) mc2147504504 fun o => ?_
    change interp B img o (exec c36 _ _) ram 0 [] = .ok c37 ram []
    have v0 : c36.get 0=0#32 := by simp [c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v0,(show alu .add 0#32 0#32=0#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t37 : Quiet.Step B img ⟨c37,ram⟩ ⟨c38,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000517a#32).getLsbD 0=false;decide) mc2147504506 fun o => ?_
    change interp B img o (exec c37 _ _) ram 0 [] = .ok c38 ram []
    have v1 : c37.get 1=2147494160#32 := by simp [c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_jalr,v1]
    change interp B img o (jump (c37.set 0 2147504508#32) 2147494160#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t38 : Quiet.Step B img ⟨c38,ram⟩ ⟨c39,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002910#32).getLsbD 0=false;decide) rt2147494160 fun o => ?_
    change interp B img o (exec c38 _ _) ram 0 [] = .ok c39 ram []
    have v10 : c38.get 10=0#32 := by simp [c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v0 : c38.get 0=0#32 := by simp [c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v10,v0,show taken .ne 0#32 0#32=false by decide +kernel]
    rfl
  have t39 : Quiet.Step B img ⟨c39,ram⟩ ⟨c40,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002912#32).getLsbD 0=false;decide) rt2147494162 fun o => ?_
    change interp B img o (exec c39 _ _) ram 0 [] = .ok c40 ram []
    have v22 : c39.get 22=0#32 := by simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v18 : c39.get 18=9#32 := by simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v22,v18,show taken .eq 0#32 9#32=false by decide +kernel]
    rfl
  have t40 : Quiet.Step B img ⟨c40,ram⟩ ⟨c41,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002916#32).getLsbD 0=false;decide) rt2147494166 fun o => ?_
    change interp B img o (exec c40 _ _) ram 0 [] = .ok c41 ram []
    have v23 : c40.get 23=0#32 := by simp [c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v9 : c40.get 9=5#32 := by simp [c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v23,v9,show taken .eq 0#32 5#32=false by decide +kernel]
    rfl
  have t41 : Quiet.Step B img ⟨c41,ram⟩ ⟨c42,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000291a#32).getLsbD 0=false;decide) rt2147494170 fun o => ?_
    change interp B img o (exec c41 _ _) ram 0 [] = .ok c42 ram []
    have v22 : c41.get 22=0#32 := by simp [c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v22,(show alu .add 0#32 1#32=1#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t42 : Quiet.Step B img ⟨c42,ram⟩ ⟨c43,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000291e#32).getLsbD 0=false;decide) rt2147494174 fun o => ?_
    change interp B img o (exec c42 _ _) ram 0 [] = .ok c43 ram []
    have v23 : c42.get 23=0#32 := by simp [c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v23,(show alu .add 0#32 1#32=1#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t43 : Quiet.Step B img ⟨c43,ram⟩ ⟨c44,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002922#32).getLsbD 0=false;decide) rt2147494178 fun o => ?_
    change interp B img o (exec c43 _ _) ram 0 [] = .ok c44 ram []
    have v0 : c43.get 0=0#32 := by simp [c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v11 : c43.get 11=1#32 := by simp [c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v0,v11,(show alu .add 0#32 1#32=1#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t44 : Quiet.Step B img ⟨c44,ram⟩ ⟨c45,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002924#32).getLsbD 0=false;decide) rt2147494180 fun o => ?_
    change interp B img o (exec c44 _ _) ram 0 [] = .ok c45 ram []
    have v11 : c44.get 11=1#32 := by simp [c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v18 : c44.get 18=9#32 := by simp [c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v11,v18,show taken .ltu 1#32 9#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c44.pc=2147494180#32 from rfl,show 2147494180#32+4294967126#32=2147494010#32 by decide +kernel]
    change interp B img o (jump c44 2147494010#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t45 : Quiet.Step B img ⟨c45,ram⟩ ⟨c46,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000287a#32).getLsbD 0=false;decide) rt2147494010 fun o => ?_
    change interp B img o (exec c45 _ _) ram 0 [] = .ok c46 ram []
    have v21 : c45.get 21=2147507081#32 := by simp [c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v22 : c45.get 22=1#32 := by simp [c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v21,v22,(show alu .add 2147507081#32 1#32=2147507082#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t46 : Quiet.Step B img ⟨c46,ram⟩ ⟨c47,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000287e#32).getLsbD 0=false;decide) rt2147494014 fun o => ?_
    change interp B img o (exec c46 _ _) ram 0 [] = .ok c47 ram []
    have v12 : c46.get 12=2147507082#32 := by simp [c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have byte : ReadBytes.Byte B img ram 2147507082#32 115#8 := by
      have data := patternBytes.bytes ⟨1,by decide⟩
      change ReadBytes.Byte B img ram (0x80005b89#32+1#32) 115#8 at data
      simpa only [show 0x80005b89#32+1#32=2147507082#32 by decide +kernel] using data
    rw [exec_load,v12,(show 2147507082#32+0#32=2147507082#32 by decide +kernel),ReadBytes.load byte,ReadBytes.extend_byte];first | rfl | (rw [hp];rfl)
  have t47 : Quiet.Step B img ⟨c47,ram⟩ ⟨c48,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002882#32).getLsbD 0=false;decide) rt2147494018 fun o => ?_
    change interp B img o (exec c47 _ _) ram 0 [] = .ok c48 ram []
    have v12 : c47.get 12=115#32 := by simp [c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v24 : c47.get 24=47#32 := by simp [c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v12,v24,show taken .eq 115#32 47#32=false by decide +kernel]
    rfl
  have t48 : Quiet.Step B img ⟨c48,ram⟩ ⟨c49,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002886#32).getLsbD 0=false;decide) rt2147494022 fun o => ?_
    change interp B img o (exec c48 _ _) ram 0 [] = .ok c49 ram []
    have v22 : c48.get 22=1#32 := by simp [c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v22,(show alu .add 1#32 1#32=2#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t49 : Quiet.Step B img ⟨c49,ram⟩ ⟨c50,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002888#32).getLsbD 0=false;decide) rt2147494024 fun o => ?_
    change interp B img o (exec c49 _ _) ram 0 [] = .ok c50 ram []
    have v18 : c49.get 18=9#32 := by simp [c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v22 : c49.get 22=2#32 := by simp [c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v18,v22,show taken .ne 9#32 2#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c49.pc=2147494024#32 from rfl,show 2147494024#32+4294967282#32=2147494010#32 by decide +kernel]
    change interp B img o (jump c49 2147494010#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t50 : Quiet.Step B img ⟨c50,ram⟩ ⟨c51,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000287a#32).getLsbD 0=false;decide) rt2147494010 fun o => ?_
    change interp B img o (exec c50 _ _) ram 0 [] = .ok c51 ram []
    have v21 : c50.get 21=2147507081#32 := by simp [c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v22 : c50.get 22=2#32 := by simp [c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v21,v22,(show alu .add 2147507081#32 2#32=2147507083#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t51 : Quiet.Step B img ⟨c51,ram⟩ ⟨c52,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000287e#32).getLsbD 0=false;decide) rt2147494014 fun o => ?_
    change interp B img o (exec c51 _ _) ram 0 [] = .ok c52 ram []
    have v12 : c51.get 12=2147507083#32 := by simp [c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have byte : ReadBytes.Byte B img ram 2147507083#32 101#8 := by
      have data := patternBytes.bytes ⟨2,by decide⟩
      change ReadBytes.Byte B img ram (0x80005b89#32+2#32) 101#8 at data
      simpa only [show 0x80005b89#32+2#32=2147507083#32 by decide +kernel] using data
    rw [exec_load,v12,(show 2147507083#32+0#32=2147507083#32 by decide +kernel),ReadBytes.load byte,ReadBytes.extend_byte];first | rfl | (rw [hp];rfl)
  have t52 : Quiet.Step B img ⟨c52,ram⟩ ⟨c53,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002882#32).getLsbD 0=false;decide) rt2147494018 fun o => ?_
    change interp B img o (exec c52 _ _) ram 0 [] = .ok c53 ram []
    have v12 : c52.get 12=101#32 := by simp [c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v24 : c52.get 24=47#32 := by simp [c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v12,v24,show taken .eq 101#32 47#32=false by decide +kernel]
    rfl
  have t53 : Quiet.Step B img ⟨c53,ram⟩ ⟨c54,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002886#32).getLsbD 0=false;decide) rt2147494022 fun o => ?_
    change interp B img o (exec c53 _ _) ram 0 [] = .ok c54 ram []
    have v22 : c53.get 22=2#32 := by simp [c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v22,(show alu .add 2#32 1#32=3#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t54 : Quiet.Step B img ⟨c54,ram⟩ ⟨c55,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002888#32).getLsbD 0=false;decide) rt2147494024 fun o => ?_
    change interp B img o (exec c54 _ _) ram 0 [] = .ok c55 ram []
    have v18 : c54.get 18=9#32 := by simp [c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v22 : c54.get 22=3#32 := by simp [c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v18,v22,show taken .ne 9#32 3#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c54.pc=2147494024#32 from rfl,show 2147494024#32+4294967282#32=2147494010#32 by decide +kernel]
    change interp B img o (jump c54 2147494010#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t55 : Quiet.Step B img ⟨c55,ram⟩ ⟨c56,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000287a#32).getLsbD 0=false;decide) rt2147494010 fun o => ?_
    change interp B img o (exec c55 _ _) ram 0 [] = .ok c56 ram []
    have v21 : c55.get 21=2147507081#32 := by simp [c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v22 : c55.get 22=3#32 := by simp [c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v21,v22,(show alu .add 2147507081#32 3#32=2147507084#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t56 : Quiet.Step B img ⟨c56,ram⟩ ⟨c57,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000287e#32).getLsbD 0=false;decide) rt2147494014 fun o => ?_
    change interp B img o (exec c56 _ _) ram 0 [] = .ok c57 ram []
    have v12 : c56.get 12=2147507084#32 := by simp [c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have byte : ReadBytes.Byte B img ram 2147507084#32 116#8 := by
      have data := patternBytes.bytes ⟨3,by decide⟩
      change ReadBytes.Byte B img ram (0x80005b89#32+3#32) 116#8 at data
      simpa only [show 0x80005b89#32+3#32=2147507084#32 by decide +kernel] using data
    rw [exec_load,v12,(show 2147507084#32+0#32=2147507084#32 by decide +kernel),ReadBytes.load byte,ReadBytes.extend_byte];first | rfl | (rw [hp];rfl)
  have t57 : Quiet.Step B img ⟨c57,ram⟩ ⟨c58,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002882#32).getLsbD 0=false;decide) rt2147494018 fun o => ?_
    change interp B img o (exec c57 _ _) ram 0 [] = .ok c58 ram []
    have v12 : c57.get 12=116#32 := by simp [c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v24 : c57.get 24=47#32 := by simp [c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v12,v24,show taken .eq 116#32 47#32=false by decide +kernel]
    rfl
  have t58 : Quiet.Step B img ⟨c58,ram⟩ ⟨c59,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002886#32).getLsbD 0=false;decide) rt2147494022 fun o => ?_
    change interp B img o (exec c58 _ _) ram 0 [] = .ok c59 ram []
    have v22 : c58.get 22=3#32 := by simp [c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v22,(show alu .add 3#32 1#32=4#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t59 : Quiet.Step B img ⟨c59,ram⟩ ⟨c60,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002888#32).getLsbD 0=false;decide) rt2147494024 fun o => ?_
    change interp B img o (exec c59 _ _) ram 0 [] = .ok c60 ram []
    have v18 : c59.get 18=9#32 := by simp [c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v22 : c59.get 22=4#32 := by simp [c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v18,v22,show taken .ne 9#32 4#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c59.pc=2147494024#32 from rfl,show 2147494024#32+4294967282#32=2147494010#32 by decide +kernel]
    change interp B img o (jump c59 2147494010#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t60 : Quiet.Step B img ⟨c60,ram⟩ ⟨c61,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000287a#32).getLsbD 0=false;decide) rt2147494010 fun o => ?_
    change interp B img o (exec c60 _ _) ram 0 [] = .ok c61 ram []
    have v21 : c60.get 21=2147507081#32 := by simp [c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v22 : c60.get 22=4#32 := by simp [c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v21,v22,(show alu .add 2147507081#32 4#32=2147507085#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t61 : Quiet.Step B img ⟨c61,ram⟩ ⟨c62,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000287e#32).getLsbD 0=false;decide) rt2147494014 fun o => ?_
    change interp B img o (exec c61 _ _) ram 0 [] = .ok c62 ram []
    have v12 : c61.get 12=2147507085#32 := by simp [c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have byte : ReadBytes.Byte B img ram 2147507085#32 112#8 := by
      have data := patternBytes.bytes ⟨4,by decide⟩
      change ReadBytes.Byte B img ram (0x80005b89#32+4#32) 112#8 at data
      simpa only [show 0x80005b89#32+4#32=2147507085#32 by decide +kernel] using data
    rw [exec_load,v12,(show 2147507085#32+0#32=2147507085#32 by decide +kernel),ReadBytes.load byte,ReadBytes.extend_byte];first | rfl | (rw [hp];rfl)
  have t62 : Quiet.Step B img ⟨c62,ram⟩ ⟨c63,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002882#32).getLsbD 0=false;decide) rt2147494018 fun o => ?_
    change interp B img o (exec c62 _ _) ram 0 [] = .ok c63 ram []
    have v12 : c62.get 12=112#32 := by simp [c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v24 : c62.get 24=47#32 := by simp [c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v12,v24,show taken .eq 112#32 47#32=false by decide +kernel]
    rfl
  have t63 : Quiet.Step B img ⟨c63,ram⟩ ⟨c64,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002886#32).getLsbD 0=false;decide) rt2147494022 fun o => ?_
    change interp B img o (exec c63 _ _) ram 0 [] = .ok c64 ram []
    have v22 : c63.get 22=4#32 := by simp [c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v22,(show alu .add 4#32 1#32=5#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t64 : Quiet.Step B img ⟨c64,ram⟩ ⟨c65,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002888#32).getLsbD 0=false;decide) rt2147494024 fun o => ?_
    change interp B img o (exec c64 _ _) ram 0 [] = .ok c65 ram []
    have v18 : c64.get 18=9#32 := by simp [c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v22 : c64.get 22=5#32 := by simp [c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v18,v22,show taken .ne 9#32 5#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c64.pc=2147494024#32 from rfl,show 2147494024#32+4294967282#32=2147494010#32 by decide +kernel]
    change interp B img o (jump c64 2147494010#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t65 : Quiet.Step B img ⟨c65,ram⟩ ⟨c66,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000287a#32).getLsbD 0=false;decide) rt2147494010 fun o => ?_
    change interp B img o (exec c65 _ _) ram 0 [] = .ok c66 ram []
    have v21 : c65.get 21=2147507081#32 := by simp [c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v22 : c65.get 22=5#32 := by simp [c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v21,v22,(show alu .add 2147507081#32 5#32=2147507086#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t66 : Quiet.Step B img ⟨c66,ram⟩ ⟨c67,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000287e#32).getLsbD 0=false;decide) rt2147494014 fun o => ?_
    change interp B img o (exec c66 _ _) ram 0 [] = .ok c67 ram []
    have v12 : c66.get 12=2147507086#32 := by simp [c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have byte : ReadBytes.Byte B img ram 2147507086#32 111#8 := by
      have data := patternBytes.bytes ⟨5,by decide⟩
      change ReadBytes.Byte B img ram (0x80005b89#32+5#32) 111#8 at data
      simpa only [show 0x80005b89#32+5#32=2147507086#32 by decide +kernel] using data
    rw [exec_load,v12,(show 2147507086#32+0#32=2147507086#32 by decide +kernel),ReadBytes.load byte,ReadBytes.extend_byte];first | rfl | (rw [hp];rfl)
  have t67 : Quiet.Step B img ⟨c67,ram⟩ ⟨c68,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002882#32).getLsbD 0=false;decide) rt2147494018 fun o => ?_
    change interp B img o (exec c67 _ _) ram 0 [] = .ok c68 ram []
    have v12 : c67.get 12=111#32 := by simp [c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v24 : c67.get 24=47#32 := by simp [c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v12,v24,show taken .eq 111#32 47#32=false by decide +kernel]
    rfl
  have t68 : Quiet.Step B img ⟨c68,ram⟩ ⟨c69,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002886#32).getLsbD 0=false;decide) rt2147494022 fun o => ?_
    change interp B img o (exec c68 _ _) ram 0 [] = .ok c69 ram []
    have v22 : c68.get 22=5#32 := by simp [c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v22,(show alu .add 5#32 1#32=6#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t69 : Quiet.Step B img ⟨c69,ram⟩ ⟨c70,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002888#32).getLsbD 0=false;decide) rt2147494024 fun o => ?_
    change interp B img o (exec c69 _ _) ram 0 [] = .ok c70 ram []
    have v18 : c69.get 18=9#32 := by simp [c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v22 : c69.get 22=6#32 := by simp [c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v18,v22,show taken .ne 9#32 6#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c69.pc=2147494024#32 from rfl,show 2147494024#32+4294967282#32=2147494010#32 by decide +kernel]
    change interp B img o (jump c69 2147494010#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t70 : Quiet.Step B img ⟨c70,ram⟩ ⟨c71,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000287a#32).getLsbD 0=false;decide) rt2147494010 fun o => ?_
    change interp B img o (exec c70 _ _) ram 0 [] = .ok c71 ram []
    have v21 : c70.get 21=2147507081#32 := by simp [c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v22 : c70.get 22=6#32 := by simp [c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v21,v22,(show alu .add 2147507081#32 6#32=2147507087#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t71 : Quiet.Step B img ⟨c71,ram⟩ ⟨c72,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000287e#32).getLsbD 0=false;decide) rt2147494014 fun o => ?_
    change interp B img o (exec c71 _ _) ram 0 [] = .ok c72 ram []
    have v12 : c71.get 12=2147507087#32 := by simp [c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have byte : ReadBytes.Byte B img ram 2147507087#32 105#8 := by
      have data := patternBytes.bytes ⟨6,by decide⟩
      change ReadBytes.Byte B img ram (0x80005b89#32+6#32) 105#8 at data
      simpa only [show 0x80005b89#32+6#32=2147507087#32 by decide +kernel] using data
    rw [exec_load,v12,(show 2147507087#32+0#32=2147507087#32 by decide +kernel),ReadBytes.load byte,ReadBytes.extend_byte];first | rfl | (rw [hp];rfl)
  have t72 : Quiet.Step B img ⟨c72,ram⟩ ⟨c73,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002882#32).getLsbD 0=false;decide) rt2147494018 fun o => ?_
    change interp B img o (exec c72 _ _) ram 0 [] = .ok c73 ram []
    have v12 : c72.get 12=105#32 := by simp [c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v24 : c72.get 24=47#32 := by simp [c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v12,v24,show taken .eq 105#32 47#32=false by decide +kernel]
    rfl
  have t73 : Quiet.Step B img ⟨c73,ram⟩ ⟨c74,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002886#32).getLsbD 0=false;decide) rt2147494022 fun o => ?_
    change interp B img o (exec c73 _ _) ram 0 [] = .ok c74 ram []
    have v22 : c73.get 22=6#32 := by simp [c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v22,(show alu .add 6#32 1#32=7#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t74 : Quiet.Step B img ⟨c74,ram⟩ ⟨c75,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002888#32).getLsbD 0=false;decide) rt2147494024 fun o => ?_
    change interp B img o (exec c74 _ _) ram 0 [] = .ok c75 ram []
    have v18 : c74.get 18=9#32 := by simp [c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v22 : c74.get 22=7#32 := by simp [c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v18,v22,show taken .ne 9#32 7#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c74.pc=2147494024#32 from rfl,show 2147494024#32+4294967282#32=2147494010#32 by decide +kernel]
    change interp B img o (jump c74 2147494010#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t75 : Quiet.Step B img ⟨c75,ram⟩ ⟨c76,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000287a#32).getLsbD 0=false;decide) rt2147494010 fun o => ?_
    change interp B img o (exec c75 _ _) ram 0 [] = .ok c76 ram []
    have v21 : c75.get 21=2147507081#32 := by simp [c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v22 : c75.get 22=7#32 := by simp [c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v21,v22,(show alu .add 2147507081#32 7#32=2147507088#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t76 : Quiet.Step B img ⟨c76,ram⟩ ⟨c77,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000287e#32).getLsbD 0=false;decide) rt2147494014 fun o => ?_
    change interp B img o (exec c76 _ _) ram 0 [] = .ok c77 ram []
    have v12 : c76.get 12=2147507088#32 := by simp [c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have byte : ReadBytes.Byte B img ram 2147507088#32 110#8 := by
      have data := patternBytes.bytes ⟨7,by decide⟩
      change ReadBytes.Byte B img ram (0x80005b89#32+7#32) 110#8 at data
      simpa only [show 0x80005b89#32+7#32=2147507088#32 by decide +kernel] using data
    rw [exec_load,v12,(show 2147507088#32+0#32=2147507088#32 by decide +kernel),ReadBytes.load byte,ReadBytes.extend_byte];first | rfl | (rw [hp];rfl)
  have t77 : Quiet.Step B img ⟨c77,ram⟩ ⟨c78,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002882#32).getLsbD 0=false;decide) rt2147494018 fun o => ?_
    change interp B img o (exec c77 _ _) ram 0 [] = .ok c78 ram []
    have v12 : c77.get 12=110#32 := by simp [c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v24 : c77.get 24=47#32 := by simp [c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v12,v24,show taken .eq 110#32 47#32=false by decide +kernel]
    rfl
  have t78 : Quiet.Step B img ⟨c78,ram⟩ ⟨c79,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002886#32).getLsbD 0=false;decide) rt2147494022 fun o => ?_
    change interp B img o (exec c78 _ _) ram 0 [] = .ok c79 ram []
    have v22 : c78.get 22=7#32 := by simp [c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v22,(show alu .add 7#32 1#32=8#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t79 : Quiet.Step B img ⟨c79,ram⟩ ⟨c80,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002888#32).getLsbD 0=false;decide) rt2147494024 fun o => ?_
    change interp B img o (exec c79 _ _) ram 0 [] = .ok c80 ram []
    have v18 : c79.get 18=9#32 := by simp [c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v22 : c79.get 22=8#32 := by simp [c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v18,v22,show taken .ne 9#32 8#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c79.pc=2147494024#32 from rfl,show 2147494024#32+4294967282#32=2147494010#32 by decide +kernel]
    change interp B img o (jump c79 2147494010#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t80 : Quiet.Step B img ⟨c80,ram⟩ ⟨c81,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000287a#32).getLsbD 0=false;decide) rt2147494010 fun o => ?_
    change interp B img o (exec c80 _ _) ram 0 [] = .ok c81 ram []
    have v21 : c80.get 21=2147507081#32 := by simp [c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v22 : c80.get 22=8#32 := by simp [c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v21,v22,(show alu .add 2147507081#32 8#32=2147507089#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t81 : Quiet.Step B img ⟨c81,ram⟩ ⟨c82,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000287e#32).getLsbD 0=false;decide) rt2147494014 fun o => ?_
    change interp B img o (exec c81 _ _) ram 0 [] = .ok c82 ram []
    have v12 : c81.get 12=2147507089#32 := by simp [c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have byte : ReadBytes.Byte B img ram 2147507089#32 116#8 := by
      have data := patternBytes.bytes ⟨8,by decide⟩
      change ReadBytes.Byte B img ram (0x80005b89#32+8#32) 116#8 at data
      simpa only [show 0x80005b89#32+8#32=2147507089#32 by decide +kernel] using data
    rw [exec_load,v12,(show 2147507089#32+0#32=2147507089#32 by decide +kernel),ReadBytes.load byte,ReadBytes.extend_byte];first | rfl | (rw [hp];rfl)
  have t82 : Quiet.Step B img ⟨c82,ram⟩ ⟨c83,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002882#32).getLsbD 0=false;decide) rt2147494018 fun o => ?_
    change interp B img o (exec c82 _ _) ram 0 [] = .ok c83 ram []
    have v12 : c82.get 12=116#32 := by simp [c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v24 : c82.get 24=47#32 := by simp [c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v12,v24,show taken .eq 116#32 47#32=false by decide +kernel]
    rfl
  have t83 : Quiet.Step B img ⟨c83,ram⟩ ⟨c84,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002886#32).getLsbD 0=false;decide) rt2147494022 fun o => ?_
    change interp B img o (exec c83 _ _) ram 0 [] = .ok c84 ram []
    have v22 : c83.get 22=8#32 := by simp [c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v22,(show alu .add 8#32 1#32=9#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t84 : Quiet.Step B img ⟨c84,ram⟩ ⟨c85,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002888#32).getLsbD 0=false;decide) rt2147494024 fun o => ?_
    change interp B img o (exec c84 _ _) ram 0 [] = .ok c85 ram []
    have v18 : c84.get 18=9#32 := by simp [c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v22 : c84.get 22=9#32 := by simp [c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v18,v22,show taken .ne 9#32 9#32=false by decide +kernel]
    rfl
  have t85 : Quiet.Step B img ⟨c85,ram⟩ ⟨c86,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000288c#32).getLsbD 0=false;decide) rt2147494028 fun o => ?_
    change interp B img o (exec c85 _ _) ram 0 [] = .ok c86 ram []
    have v0 : c85.get 0=0#32 := by simp [c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v18 : c85.get 18=9#32 := by simp [c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v0,v18,(show alu .add 0#32 9#32=9#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t86 : Quiet.Step B img ⟨c86,ram⟩ ⟨c87,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000288e#32).getLsbD 0=false;decide) rt2147494030 fun o => ?_
    change interp B img o (exec c86 _ _) ram 0 [] = .ok c87 ram []
    have v0 : c86.get 0=0#32 := by simp [c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v10 : c86.get 10=1#32 := by simp [c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v0,v10,(show alu .add 0#32 1#32=1#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t87 : Quiet.Step B img ⟨c87,ram⟩ ⟨c88,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002890#32).getLsbD 0=false;decide) rt2147494032 fun o => ?_
    change interp B img o (exec c87 _ _) ram 0 [] = .ok c88 ram []
    have v10 : c87.get 10=1#32 := by simp [c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v9 : c87.get 9=5#32 := by simp [c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v10,v9,show taken .geu 1#32 5#32=false by decide +kernel]
    rfl
  have t88 : Quiet.Step B img ⟨c88,ram⟩ ⟨c89,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002894#32).getLsbD 0=false;decide) rt2147494036 fun o => ?_
    change interp B img o (exec c88 _ _) ram 0 [] = .ok c89 ram []
    have v20 : c88.get 20=path := by simp [c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v23 : c88.get 23=1#32 := by simp [c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v20,v23,(show alu .add path 1#32=(path+1#32) by simp only [alu,BitVec.zero_add,BitVec.add_zero])];first | rfl | (rw [hp];rfl)
  have t89 : Quiet.Step B img ⟨c89,ram⟩ ⟨c90,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002898#32).getLsbD 0=false;decide) rt2147494040 fun o => ?_
    change interp B img o (exec c89 _ _) ram 0 [] = .ok c90 ram []
    have v12 : c89.get 12=(path+1#32) := by simp [c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have byte : ReadBytes.Byte B img ram (path+1#32) 109#8 := by
      have data := pathBytes.bytes ⟨1,by decide⟩
      change ReadBytes.Byte B img ram (path+1#32) 109#8 at data
      exact data
    rw [exec_load,v12,(show (path+1#32)+0#32=(path+1#32) by rw [BitVec.add_assoc,show 1#32+0#32=1#32 by decide +kernel]),ReadBytes.load byte,ReadBytes.extend_byte];first | rfl | (rw [hp];rfl)
  have t90 : Quiet.Step B img ⟨c90,ram⟩ ⟨c91,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000289c#32).getLsbD 0=false;decide) rt2147494044 fun o => ?_
    change interp B img o (exec c90 _ _) ram 0 [] = .ok c91 ram []
    have v12 : c90.get 12=109#32 := by simp [c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v24 : c90.get 24=47#32 := by simp [c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v12,v24,show taken .eq 109#32 47#32=false by decide +kernel]
    rfl
  have t91 : Quiet.Step B img ⟨c91,ram⟩ ⟨c92,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028a0#32).getLsbD 0=false;decide) rt2147494048 fun o => ?_
    change interp B img o (exec c91 _ _) ram 0 [] = .ok c92 ram []
    have v23 : c91.get 23=1#32 := by simp [c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v23,(show alu .add 1#32 1#32=2#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t92 : Quiet.Step B img ⟨c92,ram⟩ ⟨c93,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028a2#32).getLsbD 0=false;decide) rt2147494050 fun o => ?_
    change interp B img o (exec c92 _ _) ram 0 [] = .ok c93 ram []
    have v9 : c92.get 9=5#32 := by simp [c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v23 : c92.get 23=2#32 := by simp [c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v9,v23,show taken .ne 5#32 2#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c92.pc=2147494050#32 from rfl,show 2147494050#32+4294967282#32=2147494036#32 by decide +kernel]
    change interp B img o (jump c92 2147494036#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t93 : Quiet.Step B img ⟨c93,ram⟩ ⟨c94,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002894#32).getLsbD 0=false;decide) rt2147494036 fun o => ?_
    change interp B img o (exec c93 _ _) ram 0 [] = .ok c94 ram []
    have v20 : c93.get 20=path := by simp [c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v23 : c93.get 23=2#32 := by simp [c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v20,v23,(show alu .add path 2#32=(path+2#32) by simp only [alu,BitVec.zero_add,BitVec.add_zero])];first | rfl | (rw [hp];rfl)
  have t94 : Quiet.Step B img ⟨c94,ram⟩ ⟨c95,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002898#32).getLsbD 0=false;decide) rt2147494040 fun o => ?_
    change interp B img o (exec c94 _ _) ram 0 [] = .ok c95 ram []
    have v12 : c94.get 12=(path+2#32) := by simp [c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have byte : ReadBytes.Byte B img ram (path+2#32) 111#8 := by
      have data := pathBytes.bytes ⟨2,by decide⟩
      change ReadBytes.Byte B img ram (path+2#32) 111#8 at data
      exact data
    rw [exec_load,v12,(show (path+2#32)+0#32=(path+2#32) by rw [BitVec.add_assoc,show 2#32+0#32=2#32 by decide +kernel]),ReadBytes.load byte,ReadBytes.extend_byte];first | rfl | (rw [hp];rfl)
  have t95 : Quiet.Step B img ⟨c95,ram⟩ ⟨c96,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000289c#32).getLsbD 0=false;decide) rt2147494044 fun o => ?_
    change interp B img o (exec c95 _ _) ram 0 [] = .ok c96 ram []
    have v12 : c95.get 12=111#32 := by simp [c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v24 : c95.get 24=47#32 := by simp [c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v12,v24,show taken .eq 111#32 47#32=false by decide +kernel]
    rfl
  have t96 : Quiet.Step B img ⟨c96,ram⟩ ⟨c97,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028a0#32).getLsbD 0=false;decide) rt2147494048 fun o => ?_
    change interp B img o (exec c96 _ _) ram 0 [] = .ok c97 ram []
    have v23 : c96.get 23=2#32 := by simp [c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v23,(show alu .add 2#32 1#32=3#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t97 : Quiet.Step B img ⟨c97,ram⟩ ⟨c98,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028a2#32).getLsbD 0=false;decide) rt2147494050 fun o => ?_
    change interp B img o (exec c97 _ _) ram 0 [] = .ok c98 ram []
    have v9 : c97.get 9=5#32 := by simp [c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v23 : c97.get 23=3#32 := by simp [c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v9,v23,show taken .ne 5#32 3#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c97.pc=2147494050#32 from rfl,show 2147494050#32+4294967282#32=2147494036#32 by decide +kernel]
    change interp B img o (jump c97 2147494036#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t98 : Quiet.Step B img ⟨c98,ram⟩ ⟨c99,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002894#32).getLsbD 0=false;decide) rt2147494036 fun o => ?_
    change interp B img o (exec c98 _ _) ram 0 [] = .ok c99 ram []
    have v20 : c98.get 20=path := by simp [c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v23 : c98.get 23=3#32 := by simp [c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v20,v23,(show alu .add path 3#32=(path+3#32) by simp only [alu,BitVec.zero_add,BitVec.add_zero])];first | rfl | (rw [hp];rfl)
  have t99 : Quiet.Step B img ⟨c99,ram⟩ ⟨c100,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002898#32).getLsbD 0=false;decide) rt2147494040 fun o => ?_
    change interp B img o (exec c99 _ _) ram 0 [] = .ok c100 ram []
    have v12 : c99.get 12=(path+3#32) := by simp [c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have byte : ReadBytes.Byte B img ram (path+3#32) 100#8 := by
      have data := pathBytes.bytes ⟨3,by decide⟩
      change ReadBytes.Byte B img ram (path+3#32) 100#8 at data
      exact data
    rw [exec_load,v12,(show (path+3#32)+0#32=(path+3#32) by rw [BitVec.add_assoc,show 3#32+0#32=3#32 by decide +kernel]),ReadBytes.load byte,ReadBytes.extend_byte];first | rfl | (rw [hp];rfl)
  have t100 : Quiet.Step B img ⟨c100,ram⟩ ⟨c101,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000289c#32).getLsbD 0=false;decide) rt2147494044 fun o => ?_
    change interp B img o (exec c100 _ _) ram 0 [] = .ok c101 ram []
    have v12 : c100.get 12=100#32 := by simp [c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v24 : c100.get 24=47#32 := by simp [c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v12,v24,show taken .eq 100#32 47#32=false by decide +kernel]
    rfl
  have t101 : Quiet.Step B img ⟨c101,ram⟩ ⟨c102,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028a0#32).getLsbD 0=false;decide) rt2147494048 fun o => ?_
    change interp B img o (exec c101 _ _) ram 0 [] = .ok c102 ram []
    have v23 : c101.get 23=3#32 := by simp [c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v23,(show alu .add 3#32 1#32=4#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t102 : Quiet.Step B img ⟨c102,ram⟩ ⟨c103,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028a2#32).getLsbD 0=false;decide) rt2147494050 fun o => ?_
    change interp B img o (exec c102 _ _) ram 0 [] = .ok c103 ram []
    have v9 : c102.get 9=5#32 := by simp [c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v23 : c102.get 23=4#32 := by simp [c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v9,v23,show taken .ne 5#32 4#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c102.pc=2147494050#32 from rfl,show 2147494050#32+4294967282#32=2147494036#32 by decide +kernel]
    change interp B img o (jump c102 2147494036#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t103 : Quiet.Step B img ⟨c103,ram⟩ ⟨c104,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002894#32).getLsbD 0=false;decide) rt2147494036 fun o => ?_
    change interp B img o (exec c103 _ _) ram 0 [] = .ok c104 ram []
    have v20 : c103.get 20=path := by simp [c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v23 : c103.get 23=4#32 := by simp [c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v20,v23,(show alu .add path 4#32=(path+4#32) by simp only [alu,BitVec.zero_add,BitVec.add_zero])];first | rfl | (rw [hp];rfl)
  have t104 : Quiet.Step B img ⟨c104,ram⟩ ⟨c105,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002898#32).getLsbD 0=false;decide) rt2147494040 fun o => ?_
    change interp B img o (exec c104 _ _) ram 0 [] = .ok c105 ram []
    have v12 : c104.get 12=(path+4#32) := by simp [c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have byte : ReadBytes.Byte B img ram (path+4#32) 101#8 := by
      have data := pathBytes.bytes ⟨4,by decide⟩
      change ReadBytes.Byte B img ram (path+4#32) 101#8 at data
      exact data
    rw [exec_load,v12,(show (path+4#32)+0#32=(path+4#32) by rw [BitVec.add_assoc,show 4#32+0#32=4#32 by decide +kernel]),ReadBytes.load byte,ReadBytes.extend_byte];first | rfl | (rw [hp];rfl)
  have t105 : Quiet.Step B img ⟨c105,ram⟩ ⟨c106,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000289c#32).getLsbD 0=false;decide) rt2147494044 fun o => ?_
    change interp B img o (exec c105 _ _) ram 0 [] = .ok c106 ram []
    have v12 : c105.get 12=101#32 := by simp [c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v24 : c105.get 24=47#32 := by simp [c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v12,v24,show taken .eq 101#32 47#32=false by decide +kernel]
    rfl
  have t106 : Quiet.Step B img ⟨c106,ram⟩ ⟨c107,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028a0#32).getLsbD 0=false;decide) rt2147494048 fun o => ?_
    change interp B img o (exec c106 _ _) ram 0 [] = .ok c107 ram []
    have v23 : c106.get 23=4#32 := by simp [c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v23,(show alu .add 4#32 1#32=5#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t107 : Quiet.Step B img ⟨c107,ram⟩ ⟨c108,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028a2#32).getLsbD 0=false;decide) rt2147494050 fun o => ?_
    change interp B img o (exec c107 _ _) ram 0 [] = .ok c108 ram []
    have v9 : c107.get 9=5#32 := by simp [c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v23 : c107.get 23=5#32 := by simp [c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v9,v23,show taken .ne 5#32 5#32=false by decide +kernel]
    rfl
  have t108 : Quiet.Step B img ⟨c108,ram⟩ ⟨c109,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028a6#32).getLsbD 0=false;decide) rt2147494054 fun o => ?_
    change interp B img o (exec c108 _ _) ram 0 [] = .ok c109 ram []
    have v0 : c108.get 0=0#32 := by simp [c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v9 : c108.get 9=5#32 := by simp [c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v0,v9,(show alu .add 0#32 5#32=5#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t109 : Quiet.Step B img ⟨c109,ram⟩ ⟨c110,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028a8#32).getLsbD 0=false;decide) rt2147494056 fun o => ?_
    change interp B img o (exec c109 _ _) ram 0 [] = .ok c110 ram []
    have v22 : c109.get 22=9#32 := by simp [c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v11 : c109.get 11=1#32 := by simp [c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v22,v11,show taken .ltu 9#32 1#32=false by decide +kernel]
    rfl
  have t110 : Quiet.Step B img ⟨c110,ram⟩ ⟨c111,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028ac#32).getLsbD 0=false;decide) rt2147494060 fun o => ?_
    change interp B img o (exec c110 _ _) ram 0 [] = .ok c111 ram []
    have v18 : c110.get 18=9#32 := by simp [c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v22 : c110.get 22=9#32 := by simp [c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v18,v22,show taken .ltu 9#32 9#32=false by decide +kernel]
    rfl
  have t111 : Quiet.Step B img ⟨c111,ram⟩ ⟨c112,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028b0#32).getLsbD 0=false;decide) rt2147494064 fun o => ?_
    change interp B img o (exec c111 _ _) ram 0 [] = .ok c112 ram []
    have v23 : c111.get 23=5#32 := by simp [c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v10 : c111.get 10=1#32 := by simp [c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v23,v10,show taken .ltu 5#32 1#32=false by decide +kernel]
    rfl
  have t112 : Quiet.Step B img ⟨c112,ram⟩ ⟨c113,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028b4#32).getLsbD 0=false;decide) rt2147494068 fun o => ?_
    change interp B img o (exec c112 _ _) ram 0 [] = .ok c113 ram []
    have v9 : c112.get 9=5#32 := by simp [c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v23 : c112.get 23=5#32 := by simp [c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v9,v23,show taken .ltu 5#32 5#32=false by decide +kernel]
    rfl
  have t113 : Quiet.Step B img ⟨c113,ram⟩ ⟨c114,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028b8#32).getLsbD 0=false;decide) rt2147494072 fun o => ?_
    change interp B img o (exec c113 _ _) ram 0 [] = .ok c114 ram []
    have v22 : c113.get 22=9#32 := by simp [c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v11 : c113.get 11=1#32 := by simp [c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v22,v11,(show alu .sub 9#32 1#32=8#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t114 : Quiet.Step B img ⟨c114,ram⟩ ⟨c115,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028bc#32).getLsbD 0=false;decide) rt2147494076 fun o => ?_
    change interp B img o (exec c114 _ _) ram 0 [] = .ok c115 ram []
    have v21 : c114.get 21=2147507081#32 := by simp [c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v11 : c114.get 11=1#32 := by simp [c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v21,v11,(show alu .add 2147507081#32 1#32=2147507082#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t115 : Quiet.Step B img ⟨c115,ram⟩ ⟨c116,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028c0#32).getLsbD 0=false;decide) rt2147494080 fun o => ?_
    change interp B img o (exec c115 _ _) ram 0 [] = .ok c116 ram []
    have v25 : c115.get 25=1#32 := by simp [c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v12 : c115.get 12=8#32 := by simp [c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v25,v12,show taken .geu 1#32 8#32=false by decide +kernel]
    rfl
  have t116 : Quiet.Step B img ⟨c116,ram⟩ ⟨c117,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028c4#32).getLsbD 0=false;decide) rt2147494084 fun o => ?_
    change interp B img o (exec c116 _ _) ram 0 [] = .ok c117 ram []
    have v13 : c116.get 13=2147507082#32 := by simp [c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have byte : ReadBytes.Byte B img ram 2147507082#32 115#8 := by
      have data := patternBytes.bytes ⟨1,by decide⟩
      change ReadBytes.Byte B img ram (0x80005b89#32+1#32) 115#8 at data
      simpa only [show 0x80005b89#32+1#32=2147507082#32 by decide +kernel] using data
    rw [exec_load,v13,(show 2147507082#32+0#32=2147507082#32 by decide +kernel),ReadBytes.load byte,ReadBytes.extend_byte];first | rfl | (rw [hp];rfl)
  have t117 : Quiet.Step B img ⟨c117,ram⟩ ⟨c118,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028c8#32).getLsbD 0=false;decide) rt2147494088 fun o => ?_
    change interp B img o (exec c117 _ _) ram 0 [] = .ok c118 ram []
    have v11 : c117.get 11=115#32 := by simp [c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v26 : c117.get 26=123#32 := by simp [c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v11,v26,show taken .ne 115#32 123#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c117.pc=2147494088#32 from rfl,show 2147494088#32+50#32=2147494138#32 by decide +kernel]
    change interp B img o (jump c117 2147494138#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t118 : Quiet.Step B img ⟨c118,ram⟩ ⟨c119,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028fa#32).getLsbD 0=false;decide) rt2147494138 fun o => ?_
    change interp B img o (exec c118 _ _) ram 0 [] = .ok c119 ram []
    have v23 : c118.get 23=5#32 := by simp [c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v10 : c118.get 10=1#32 := by simp [c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v23,v10,(show alu .sub 5#32 1#32=4#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t119 : Quiet.Step B img ⟨c119,ram⟩ ⟨c120,ram⟩ := by
    refine QuietDet.step_of (by change (0x800028fe#32).getLsbD 0=false;decide) rt2147494142 fun o => ?_
    change interp B img o (exec c119 _ _) ram 0 [] = .ok c120 ram []
    have v12 : c119.get 12=8#32 := by simp [c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v11 : c119.get 11=4#32 := by simp [c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_branch,v12,v11,show taken .ne 8#32 4#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c119.pc=2147494142#32 from rfl,show 2147494142#32+44#32=2147494186#32 by decide +kernel]
    change interp B img o (jump c119 2147494186#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t120 : Quiet.Step B img ⟨c120,ram⟩ ⟨c121,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000292a#32).getLsbD 0=false;decide) rt2147494186 fun o => ?_
    change interp B img o (exec c120 _ _) ram 0 [] = .ok c121 ram []
    have v0 : c120.get 0=0#32 := by simp [c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_opimm,v0,(show alu .add 0#32 0#32=0#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t121 : Quiet.Step B img ⟨c121,ram⟩ ⟨c122,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000292c#32).getLsbD 0=false;decide) rt2147494188 fun o => ?_
    change interp B img o (exec c121 _ _) ram 0 [] = .ok c122 ram []
    rw [exec_jal]
    change interp B img o (jump c121 2147494198#32) ram 0 []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t122 : Quiet.Step B img ⟨c122,ram⟩ ⟨c123,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002936#32).getLsbD 0=false;decide) rt2147494198 fun o => ?_
    change interp B img o (exec c122 _ _) ram 0 [] = .ok c123 ram []
    have v0 : c122.get 0=0#32 := by simp [c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v11 : c122.get 11=0#32 := by simp [c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v0,v11,(show alu .add 0#32 0#32=0#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  have t123 : Quiet.Step B img ⟨c123,ram⟩ ⟨c124,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002938#32).getLsbD 0=false;decide) rt2147494200 fun o => ?_
    change interp B img o (exec c123 _ _) ram 0 [] = .ok c124 ram []
    have v0 : c123.get 0=0#32 := by simp [c123,c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    have v8 : c123.get 8=0#32 := by simp [c123,c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,v0,v8,(show alu .add 0#32 0#32=0#32 by decide +kernel)];first | rfl | (rw [hp];rfl)
  refine ⟨c124,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.step t23 (.step t24 (.step t25 (.step t26 (.step t27 (.step t28 (.step t29 (.step t30 (.step t31 (.step t32 (.step t33 (.step t34 (.step t35 (.step t36 (.step t37 (.step t38 (.step t39 (.step t40 (.step t41 (.step t42 (.step t43 (.step t44 (.step t45 (.step t46 (.step t47 (.step t48 (.step t49 (.step t50 (.step t51 (.step t52 (.step t53 (.step t54 (.step t55 (.step t56 (.step t57 (.step t58 (.step t59 (.step t60 (.step t61 (.step t62 (.step t63 (.step t64 (.step t65 (.step t66 (.step t67 (.step t68 (.step t69 (.step t70 (.step t71 (.step t72 (.step t73 (.step t74 (.step t75 (.step t76 (.step t77 (.step t78 (.step t79 (.step t80 (.step t81 (.step t82 (.step t83 (.step t84 (.step t85 (.step t86 (.step t87 (.step t88 (.step t89 (.step t90 (.step t91 (.step t92 (.step t93 (.step t94 (.step t95 (.step t96 (.step t97 (.step t98 (.step t99 (.step t100 (.step t101 (.step t102 (.step t103 (.step t104 (.step t105 (.step t106 (.step t107 (.step t108 (.step t109 (.step t110 (.step t111 (.step t112 (.step t113 (.step t114 (.step t115 (.step t116 (.step t117 (.step t118 (.step t119 (.step t120 (.step t121 (.step t122 (.single t123))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c124,c123,c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c124,c123,c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c124,c123,c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c124,c123,c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c124,c123,c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c124,c123,c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c124,c123,c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c124,c123,c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c124,c123,c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c124,c123,c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c124,c123,c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c124,c123,c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c124,c123,c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c124,c123,c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c124,c123,c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c124,c123,c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c124,c123,c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · intro reg h19 h9 h20 h18 h21 h8 h10 h11 h24 h25 h26 h27 h22 h12 h23 h13 h1;simp [c124,c123,c122,c121,c120,c119,c118,c117,c116,c115,c114,c113,c112,c111,c110,c109,c108,c107,c106,c105,c104,c103,c102,c101,c100,c99,c98,c97,c96,c95,c94,c93,c92,c91,c90,c89,c88,c87,c86,c85,c84,c83,c82,c81,c80,c79,c78,c77,c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h19,h9,h20,h18,h21,h8,h10,h11,h24,h25,h26,h27,h22,h12,h23,h13,h1]
end E5R.Thermostat.MainSetpointModeBody
