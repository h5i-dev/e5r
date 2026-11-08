import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadNameCase05
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (v last count sp : Word) (h5 : c.get 5=33#32)
(h6 : c.get 6=48#32)
(h7 : c.get 7=14#32)
(h28 : c.get 28=58#32)
(h27 : c.get 27=91#32)
(h30 : c.get 30=v)
(h15 : c.get 15=last)
(h14 : c.get 14=count)
(h2 : c.get 2=sp)
(hmask : ramRead ram (sp+32#32) .w=9409#32) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0)
(hb0 : taken .ltu (v) (33#32)=false)
(hb1 : taken .geu (v) (48#32)=true)
(hb2 : taken .ltu (v) (58#32)=false)
(hb3 : taken .ltu (v) (alu .add ((0 : Word)) (65#32))=false)
(hb4 : taken .ltu (v) (91#32)=false)
(hb5 : taken .ltu (v) (alu .add ((0 : Word)) (94#32))=false)
(hb6 : taken .eq (last) (count)=false)
(hb7 : taken .eq (alu .and (alu .xor (alu .sltu (v) (123#32)) (0xffffffff#32)) (alu .sltu ((0 : Word)) (alu .add (alu .and (v) (253#32)) (0xffffff84#32)))) ((0 : Word))=false)
    (hp : c.pc=0x80002ff8#32) :
    ∃ d, Quiet.Steps B img 17 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000342c#32 ∧
      d.get 12=alu .add ((0 : Word)) (94#32) ∧ d.get 19=alu .sltu ((0 : Word)) (alu .add (alu .and (v) (253#32)) (0xffffff84#32)) ∧ d.get 30=alu .and (alu .xor (alu .sltu (v) (123#32)) (0xffffffff#32)) (alu .sltu ((0 : Word)) (alu .add (alu .and (v) (253#32)) (0xffffff84#32))) ∧ (∀ r : Reg, r≠12 → r≠19 → r≠30 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80002ffc#32
  let c2 := c1.goto 0x8000301c#32
  let c3 := c2.goto 0x80003020#32
  let c4 := c3.wr 12 (alu .add ((0 : Word)) (65#32)) 0x80003024#32
  let c5 := c4.goto 0x80003028#32
  let c6 := c5.goto 0x8000302c#32
  let c7 := c6.wr 12 (alu .add ((0 : Word)) (94#32)) 0x80003030#32
  let c8 := c7.goto 0x80003034#32
  let c9 := c8.goto 0x80003038#32
  let c10 := c9.wr 19 (alu .and (v) (253#32)) 0x8000303c#32
  let c11 := c10.wr 30 (alu .sltu (v) (123#32)) 0x80003040#32
  let c12 := c11.wr 19 (alu .add (alu .and (v) (253#32)) (0xffffff84#32)) 0x80003044#32
  let c13 := c12.wr 30 (alu .xor (alu .sltu (v) (123#32)) (0xffffffff#32)) 0x80003048#32
  let c14 := c13.wr 19 (alu .sltu ((0 : Word)) (alu .add (alu .and (v) (253#32)) (0xffffff84#32))) 0x8000304c#32
  let c15 := c14.wr 30 (alu .and (alu .xor (alu .sltu (v) (123#32)) (0xffffffff#32)) (alu .sltu ((0 : Word)) (alu .add (alu .and (v) (253#32)) (0xffffff84#32)))) 0x80003050#32
  let c16 := c15.goto 0x80003054#32
  let c17 := c16.goto 0x8000342c#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495928) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v30 : c.get 30=v := by simp [Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    have v5 : c.get 5=33#32 := by simp [Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_branch,v30,v5,hb0]
    rw [hp]
    rfl
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ffc#32).getLsbD 0=false;decide) hh2147495932 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v30 : c1.get 30=v := by simp [c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    have v6 : c1.get 6=48#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_branch,v30,v6,hb1]
    simp only [ite_true]
    change Observed.interp B img o (jump c1 (0x80002ffc#32+0x20#32)) ram 0 [] []=_
    rw [show 0x80002ffc#32+0x20#32=0x8000301c#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000301c#32).getLsbD 0=false;decide) hh2147495964 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v30 : c2.get 30=v := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    have v28 : c2.get 28=58#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_branch,v30,v28,hb2]
    rfl
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80003020#32).getLsbD 0=false;decide) hh2147495968 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80003024#32).getLsbD 0=false;decide) hh2147495972 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v30 : c4.get 30=v := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    have v12 : c4.get 12=alu .add ((0 : Word)) (65#32) := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_branch,v30,v12,hb3]
    rfl
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80003028#32).getLsbD 0=false;decide) hh2147495976 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v30 : c5.get 30=v := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    have v27 : c5.get 27=91#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_branch,v30,v27,hb4]
    rfl
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x8000302c#32).getLsbD 0=false;decide) hh2147495980 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80003030#32).getLsbD 0=false;decide) hh2147495984 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v30 : c7.get 30=v := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    have v12 : c7.get 12=alu .add ((0 : Word)) (94#32) := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_branch,v30,v12,hb5]
    rfl
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80003034#32).getLsbD 0=false;decide) hh2147495988 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v15 : c8.get 15=last := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    have v14 : c8.get 14=count := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_branch,v15,v14,hb6]
    rfl
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80003038#32).getLsbD 0=false;decide) hh2147495992 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v30 : c9.get 30=v := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_opimm,v30];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x8000303c#32).getLsbD 0=false;decide) hh2147495996 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v30 : c10.get 30=v := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_opimm,v30];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x80003040#32).getLsbD 0=false;decide) hh2147496000 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v19 : c11.get 19=alu .and (v) (253#32) := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_opimm,v19];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x80003044#32).getLsbD 0=false;decide) hh2147496004 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    have v30 : c12.get 30=alu .sltu (v) (123#32) := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_opimm,v30];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine Quiet.step_of (by change (0x80003048#32).getLsbD 0=false;decide) hh2147496008 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 ram [],[]⟩
    have v19 : c13.get 19=alu .add (alu .and (v) (253#32)) (0xffffff84#32) := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_op,Core.get_zero,v19];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine Quiet.step_of (by change (0x8000304c#32).getLsbD 0=false;decide) hh2147496012 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) ram 0 [] [] = ⟨.ok c15 ram [],[]⟩
    have v30 : c14.get 30=alu .xor (alu .sltu (v) (123#32)) (0xffffffff#32) := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    have v19 : c14.get 19=alu .sltu ((0 : Word)) (alu .add (alu .and (v) (253#32)) (0xffffff84#32)) := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_op,v30,v19];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,ram⟩ ⟨c16,ram⟩ := by
    refine Quiet.step_of (by change (0x80003050#32).getLsbD 0=false;decide) hh2147496016 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) ram 0 [] [] = ⟨.ok c16 ram [],[]⟩
    have v30 : c15.get 30=alu .and (alu .xor (alu .sltu (v) (123#32)) (0xffffffff#32)) (alu .sltu ((0 : Word)) (alu .add (alu .and (v) (253#32)) (0xffffff84#32))) := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_branch,v30,Core.get_zero,hb7]
    rfl
  have t16 : Quiet.Step B img ⟨c16,ram⟩ ⟨c17,ram⟩ := by
    refine Quiet.step_of (by change (0x80003054#32).getLsbD 0=false;decide) hh2147496020 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) ram 0 [] [] = ⟨.ok c17 ram [],[]⟩
    rw [exec_jal,Core.set_zero]
    change Observed.interp B img o (jump c16 (0x80003054#32+0x3d8#32)) ram 0 [] []=_
    rw [show 0x80003054#32+0x3d8#32=0x8000342c#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c17,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.single t16)))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
  · intro reg h12 h19 h30;simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2,h12,h19,h30]
end E5R.Thermostat.HeadNameCase05
