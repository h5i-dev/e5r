import Projects.thermostat.MainRouterCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.RouteMatcherStart
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (pattern patternLength path pathLength params : Word) (h10 : c.get 10=pattern) (h11 : c.get 11=patternLength) (h12 : c.get 12=path) (h13 : c.get 13=pathLength) (h14 : c.get 14=params)
    (hp : c.pc=0x80002856#32) :
    ∃ d, Quiet.Steps B img 13 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002876#32 ∧
      d.get 19=params ∧ d.get 9=pathLength ∧ d.get 20=path ∧ d.get 18=patternLength ∧ d.get 21=pattern ∧ d.get 8=0#32 ∧ d.get 10=0#32 ∧ d.get 11=0#32 ∧ d.get 24=47#32 ∧ d.get 25=1#32 ∧ d.get 26=123#32 ∧ d.get 27=125#32 ∧ d.get 22=0#32 ∧ (∀ r : Reg, r≠19 → r≠9 → r≠20 → r≠18 → r≠21 → r≠8 → r≠10 → r≠11 → r≠24 → r≠25 → r≠26 → r≠27 → r≠22 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 19 (params) 0x80002858#32
  let c2 := c1.wr 9 (pathLength) 0x8000285a#32
  let c3 := c2.wr 20 (path) 0x8000285c#32
  let c4 := c3.wr 18 (patternLength) 0x8000285e#32
  let c5 := c4.wr 21 (pattern) 0x80002860#32
  let c6 := c5.wr 8 (0#32) 0x80002862#32
  let c7 := c6.wr 10 (0#32) 0x80002864#32
  let c8 := c7.wr 11 (0#32) 0x80002866#32
  let c9 := c8.wr 24 (47#32) 0x8000286a#32
  let c10 := c9.wr 25 (1#32) 0x8000286c#32
  let c11 := c10.wr 26 (123#32) 0x80002870#32
  let c12 := c11.wr 27 (125#32) 0x80002874#32
  let c13 := c12.wr 22 (0#32) 0x80002876#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147493974) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have source : c.get 14=params := by simp [Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,Core.get_zero,source]
    try rw [hp]
    change Observed.interp B img o (.done (c.wr 19 (0#32+params) 0x80002858#32)) ram 0 [] []=_
    rw [BitVec.zero_add];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002858#32).getLsbD 0=false;decide) rt2147493976 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have source : c1.get 13=pathLength := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,Core.get_zero,source]
    try rw [hp]
    change Observed.interp B img o (.done (c1.wr 9 (0#32+pathLength) 0x8000285a#32)) ram 0 [] []=_
    rw [BitVec.zero_add];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000285a#32).getLsbD 0=false;decide) rt2147493978 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have source : c2.get 12=path := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,Core.get_zero,source]
    try rw [hp]
    change Observed.interp B img o (.done (c2.wr 20 (0#32+path) 0x8000285c#32)) ram 0 [] []=_
    rw [BitVec.zero_add];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x8000285c#32).getLsbD 0=false;decide) rt2147493980 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have source : c3.get 11=patternLength := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,Core.get_zero,source]
    try rw [hp]
    change Observed.interp B img o (.done (c3.wr 18 (0#32+patternLength) 0x8000285e#32)) ram 0 [] []=_
    rw [BitVec.zero_add];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x8000285e#32).getLsbD 0=false;decide) rt2147493982 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have source : c4.get 10=pattern := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
    rw [exec_op,Core.get_zero,source]
    try rw [hp]
    change Observed.interp B img o (.done (c4.wr 21 (0#32+pattern) 0x80002860#32)) ram 0 [] []=_
    rw [BitVec.zero_add];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80002860#32).getLsbD 0=false;decide) rt2147493984 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80002862#32).getLsbD 0=false;decide) rt2147493986 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80002864#32).getLsbD 0=false;decide) rt2147493988 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80002866#32).getLsbD 0=false;decide) rt2147493990 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x8000286a#32).getLsbD 0=false;decide) rt2147493994 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x8000286c#32).getLsbD 0=false;decide) rt2147493996 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x80002870#32).getLsbD 0=false;decide) rt2147494000 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x80002874#32).getLsbD 0=false;decide) rt2147494004 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  refine ⟨c13,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.single t12)))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14]
  · intro reg h19 h9 h20 h18 h21 h8 h10 h11 h24 h25 h26 h27 h22;simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h19,h9,h20,h18,h21,h8,h10,h11,h24,h25,h26,h27,h22]
end E5R.Thermostat.RouteMatcherStart
