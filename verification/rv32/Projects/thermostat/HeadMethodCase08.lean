import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadMethodCase08
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (v : Word) (h5 : c.get 5=9409#32)
(h6 : c.get 6=33#32)
(h7 : c.get 7=48#32)
(h8 : c.get 8=91#32)
(h18 : c.get 18=94#32)
(h29 : c.get 29=14#32)
(h30 : c.get 30=58#32)
(h31 : c.get 31=65#32)
(h19 : c.get 19=v)
(hb0 : taken .ltu (v) (33#32)=false)
(hb1 : taken .geu (v) (48#32)=true)
(hb2 : taken .ltu (v) (58#32)=false)
(hb3 : taken .ltu (v) (65#32)=false)
(hb4 : taken .ltu (v) (91#32)=false)
(hb5 : taken .ltu (v) (94#32)=false)
(hb6 : taken .ne (alu .or (alu .sltu (v) (123#32)) (alu .sltu (alu .add (alu .and (v) (253#32)) (0xffffff84#32)) (1#32))) ((0 : Word))=true)
    (hp : c.pc=0x80002d06#32) :
    ∃ d, Quiet.Steps B img 12 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002cf4#32 ∧
      d.get 28=alu .or (alu .sltu (v) (123#32)) (alu .sltu (alu .add (alu .and (v) (253#32)) (0xffffff84#32)) (1#32)) ∧ d.get 19=alu .sltu (v) (123#32) ∧ (∀ r : Reg, r≠28 → r≠19 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80002d0a#32
  let c2 := c1.goto 0x80002d28#32
  let c3 := c2.goto 0x80002d2c#32
  let c4 := c3.goto 0x80002d30#32
  let c5 := c4.goto 0x80002d34#32
  let c6 := c5.goto 0x80002d38#32
  let c7 := c6.wr 28 (alu .and (v) (253#32)) 0x80002d3c#32
  let c8 := c7.wr 28 (alu .add (alu .and (v) (253#32)) (0xffffff84#32)) 0x80002d40#32
  let c9 := c8.wr 19 (alu .sltu (v) (123#32)) 0x80002d44#32
  let c10 := c9.wr 28 (alu .sltu (alu .add (alu .and (v) (253#32)) (0xffffff84#32)) (1#32)) 0x80002d48#32
  let c11 := c10.wr 28 (alu .or (alu .sltu (v) (123#32)) (alu .sltu (alu .add (alu .and (v) (253#32)) (0xffffff84#32)) (1#32))) 0x80002d4c#32
  let c12 := c11.goto 0x80002cf4#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495174) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v19 : c.get 19=v := by simp [Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    have v6 : c.get 6=33#32 := by simp [Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    rw [exec_branch,v19,v6,hb0]
    rw [hp]
    rfl
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002d0a#32).getLsbD 0=false;decide) hh2147495178 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v19 : c1.get 19=v := by simp [c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    have v7 : c1.get 7=48#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    rw [exec_branch,v19,v7,hb1]
    simp only [ite_true]
    change Observed.interp B img o (jump c1 (0x80002d0a#32+0x1e#32)) ram 0 [] []=_
    rw [show 0x80002d0a#32+0x1e#32=0x80002d28#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80002d28#32).getLsbD 0=false;decide) hh2147495208 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v19 : c2.get 19=v := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    have v30 : c2.get 30=58#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    rw [exec_branch,v19,v30,hb2]
    rfl
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80002d2c#32).getLsbD 0=false;decide) hh2147495212 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v19 : c3.get 19=v := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    have v31 : c3.get 31=65#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    rw [exec_branch,v19,v31,hb3]
    rfl
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80002d30#32).getLsbD 0=false;decide) hh2147495216 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v19 : c4.get 19=v := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    have v8 : c4.get 8=91#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    rw [exec_branch,v19,v8,hb4]
    rfl
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80002d34#32).getLsbD 0=false;decide) hh2147495220 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v19 : c5.get 19=v := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    have v18 : c5.get 18=94#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    rw [exec_branch,v19,v18,hb5]
    rfl
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80002d38#32).getLsbD 0=false;decide) hh2147495224 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v19 : c6.get 19=v := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    rw [exec_opimm,v19];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80002d3c#32).getLsbD 0=false;decide) hh2147495228 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v28 : c7.get 28=alu .and (v) (253#32) := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    rw [exec_opimm,v28];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80002d40#32).getLsbD 0=false;decide) hh2147495232 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v19 : c8.get 19=v := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    rw [exec_opimm,v19];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80002d44#32).getLsbD 0=false;decide) hh2147495236 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v28 : c9.get 28=alu .add (alu .and (v) (253#32)) (0xffffff84#32) := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    rw [exec_opimm,v28];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80002d48#32).getLsbD 0=false;decide) hh2147495240 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v19 : c10.get 19=alu .sltu (v) (123#32) := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    have v28 : c10.get 28=alu .sltu (alu .add (alu .and (v) (253#32)) (0xffffff84#32)) (1#32) := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    rw [exec_op,v19,v28];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x80002d4c#32).getLsbD 0=false;decide) hh2147495244 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v28 : c11.get 28=alu .or (alu .sltu (v) (123#32)) (alu .sltu (alu .add (alu .and (v) (253#32)) (0xffffff84#32)) (1#32)) := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    rw [exec_branch,v28,Core.get_zero,hb6]
    simp only [ite_true]
    change Observed.interp B img o (jump c11 (0x80002d4c#32+0xffffffa8#32)) ram 0 [] []=_
    rw [show 0x80002d4c#32+0xffffffa8#32=0x80002cf4#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c12,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.single t11))))))))))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
  · intro reg h28 h19;simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19,h28,h19]
end E5R.Thermostat.HeadMethodCase08
