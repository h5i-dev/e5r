import Projects.thermostat.HttpDecCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HttpDecOnesMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HttpDecSmallQuotient
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (n : Nat) (hn : n<100) (h13 : c.get 13=BitVec.ofNat 32 n)
    (hp : c.pc=0x800044e6#32) :
    ∃ d, Quiet.Steps B img 12 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000450e#32 ∧
      d.get 15=0#32 ∧ d.get 16=BitVec.ofNat 32 (n/10) ∧ d.get 17=0#32 ∧ (∀ r : Reg, r≠15 → r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 15 (3435974656#32) 0x800044ea#32
  let c2 := c1.wr 15 (3435973837#32) 0x800044ee#32
  let c3 := c2.wr 15 (HttpDecOnesMath.high n) 0x800044f2#32
  let c4 := c3.wr 16 (429498368#32) 0x800044f6#32
  let c5 := c4.wr 15 (BitVec.ofNat 32 (n/10)) 0x800044f8#32
  let c6 := c5.wr 16 (429496730#32) 0x800044fc#32
  let c7 := c6.wr 16 (0#32) 0x80004500#32
  let c8 := c7.wr 17 (0#32) 0x80004504#32
  let c9 := c8.wr 16 (0#32) 0x80004506#32
  let c10 := c9.wr 16 (0#32) 0x80004508#32
  let c11 := c10.wr 16 (BitVec.ofNat 32 (n/10)) 0x8000450c#32
  let c12 := c11.wr 15 (0#32) 0x8000450e#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact de2147501286) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_lui,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800044ea#32).getLsbD 0=false;decide) de2147501290 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v15 : c1.get 15=3435974656#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h13]
    rw [exec_opimm,v15];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800044ee#32).getLsbD 0=false;decide) de2147501294 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v13 : c2.get 13=BitVec.ofNat 32 n := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h13]
    have v15 : c2.get 15=3435973837#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h13]
    rw [HttpDecMath.exec_muldiv,v13,v15];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800044f2#32).getLsbD 0=false;decide) de2147501298 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800044f6#32).getLsbD 0=false;decide) de2147501302 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v15 : c4.get 15=HttpDecOnesMath.high n := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
    rw [exec_opimm,v15]
    change Observed.interp B img o (.done (c4.wr 15 ((HttpDecOnesMath.high n) >>> 3) 0x800044f8#32)) ram 0 [] [] = _
    rw [show (HttpDecOnesMath.high n) >>> 3=BitVec.ofNat 32 (n/10) from HttpDecMath.quotient10 n (by omega)];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800044f8#32).getLsbD 0=false;decide) de2147501304 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v16 : c5.get 16=429498368#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
    rw [exec_opimm,v16];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x800044fc#32).getLsbD 0=false;decide) de2147501308 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v15 : c6.get 15=BitVec.ofNat 32 (n/10) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
    have v16 : c6.get 16=429496730#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
    rw [HttpDecMath.exec_muldiv,v15,v16,show muldiv .mulhu (BitVec.ofNat 32 (n/10)) 429496730#32=0#32 from HttpDecMath.mulhu_zero (n/10) 429496730 (by omega) (by decide) (by omega)];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80004500#32).getLsbD 0=false;decide) de2147501312 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v16 : c7.get 16=0#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
    rw [exec_opimm,v16];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80004504#32).getLsbD 0=false;decide) de2147501316 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v16 : c8.get 16=0#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
    rw [exec_opimm,v16];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80004506#32).getLsbD 0=false;decide) de2147501318 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v16 : c9.get 16=0#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
    have v17 : c9.get 17=0#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
    rw [exec_op,v16,v17];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80004508#32).getLsbD 0=false;decide) de2147501320 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v15 : c10.get 15=BitVec.ofNat 32 (n/10) := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
    have v16 : c10.get 16=0#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
    rw [exec_op,v15,v16]
    change Observed.interp B img o (.done (c10.wr 16 ((BitVec.ofNat 32 (n/10))-0#32) 0x8000450c#32)) ram 0 [] [] = _
    rw [BitVec.sub_zero];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x8000450c#32).getLsbD 0=false;decide) de2147501324 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  refine ⟨c12,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.single t11))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
  · intro reg h15 h16 h17;simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h15,h16,h17]
end E5R.Thermostat.HttpDecSmallQuotient
