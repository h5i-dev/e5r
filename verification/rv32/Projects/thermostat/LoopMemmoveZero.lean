import Projects.thermostat.LoopMemmoveZeroCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.LoopMemmoveZero
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (_dst _src fp : Word) :=
  ramWrite (ram) (0x80ffeb8c#32) (fp) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (dst src fp : Word) (sp : c.get 2=0x80ffeb90#32) (x8 : c.get 8=fp) (x10 : c.get 10=dst) (x11 : c.get 11=src) (zero : c.get 12=0#32) (ret : c.get 1=0x800017e0#32) (stack : Memory.Block B 0x80ffeb70#32 32)
    (hp : c.pc=0x800056a0#32) :
    ∃ d, Quiet.Steps B img 15 ⟨c,ram⟩ ⟨d,memory ram dst src fp⟩ ∧ d.pc=0x800017e0#32 ∧
      d.get 6=0x800056a0#32 ∧ d.get 2=0x80ffeb90#32 ∧ d.get 13=dst ∧ d.get 14=dst ∧ d.get 8=fp ∧ (∀ r : Reg, r≠6 → r≠2 → r≠13 → r≠14 → r≠8 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 6 (0x800056a0#32) 0x800056a4#32
  let c2 := c1.goto 0x80005310#32
  let c3 := c2.wr 2 (0x80ffeb70#32) 0x80005312#32
  let r1 := ramWrite ram (0x80ffeb8c#32) (fp) .w
  let c4 := c3.goto 0x80005314#32
  let c5 := c4.wr 13 (alu .sub dst src) 0x80005318#32
  let c6 := c5.goto 0x8000538c#32
  let c7 := c6.wr 13 (16#32) 0x8000538e#32
  let c8 := c7.goto 0x80005400#32
  let c9 := c8.wr 13 (dst) 0x80005402#32
  let c10 := c9.wr 14 (dst) 0x80005406#32
  let c11 := c10.goto 0x8000540a#32
  let c12 := c11.goto 0x80005632#32
  let c13 := c12.wr 8 (fp) 0x80005634#32
  let c14 := c13.wr 2 (0x80ffeb90#32) 0x80005636#32
  let c15 := c14.goto 0x800017e0#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact LoopMemmoveZeroCode.at2147505824) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_auipc];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800056a4#32).getLsbD 0=false;decide) LoopMemmoveZeroCode.at2147505828 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v6 : c1.get 6=0x800056a0#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
    rw [exec_jalr,v6]
    change Observed.interp B img o (jump c1 0x80005310#32) ram 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80005310#32).getLsbD 0=false;decide) LoopMemmoveZeroCode.at2147504912 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v2 : c2.get 2=0x80ffeb90#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,r1⟩ := by
    refine Quiet.step_of (by change (0x80005312#32).getLsbD 0=false;decide) LoopMemmoveZeroCode.at2147504914 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 r1 [],[]⟩
    have v2 : c3.get 2=0x80ffeb70#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
    have v8 : c3.get 8=fp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
    rw [exec_store,v2,v8,show 0x80ffeb70#32+28#32=0x80ffeb8c#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (by decide +kernel)
        (by simpa only [show 0x80ffeb70#32+28#32=0x80ffeb8c#32 by decide +kernel] using Memory.block_access stack (off := 28) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r1⟩ ⟨c5,r1⟩ := by
    refine Quiet.step_of (by change (0x80005314#32).getLsbD 0=false;decide) LoopMemmoveZeroCode.at2147504916 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r1 0 [] [] = ⟨.ok c5 r1 [],[]⟩
    have v10 : c4.get 10=dst := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
    have v11 : c4.get 11=src := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
    rw [exec_op,v10,v11];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r1⟩ ⟨c6,r1⟩ := by
    refine Quiet.step_of (by change (0x80005318#32).getLsbD 0=false;decide) LoopMemmoveZeroCode.at2147504920 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r1 0 [] [] = ⟨.ok c6 r1 [],[]⟩
    have v13 : c5.get 13=alu .sub dst src := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
    have v12 : c5.get 12=0#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
    rw [exec_branch,v13,v12,show taken .geu (alu .sub dst src) 0#32=true by simp [taken,BitVec.ult]]
    rw [ite_eq_left rfl,show c5.pc=0x80005318#32 from rfl,show 0x80005318#32+116#32=0x8000538c#32 by decide +kernel]
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r1⟩ ⟨c7,r1⟩ := by
    refine Quiet.step_of (by change (0x8000538c#32).getLsbD 0=false;decide) LoopMemmoveZeroCode.at2147505036 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r1 0 [] [] = ⟨.ok c7 r1 [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r1⟩ ⟨c8,r1⟩ := by
    refine Quiet.step_of (by change (0x8000538e#32).getLsbD 0=false;decide) LoopMemmoveZeroCode.at2147505038 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r1 0 [] [] = ⟨.ok c8 r1 [],[]⟩
    have v12 : c7.get 12=0#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
    have v13 : c7.get 13=16#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
    rw [exec_branch,v12,v13,show taken .ltu 0#32 16#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c7.pc=0x8000538e#32 from rfl,show 0x8000538e#32+114#32=0x80005400#32 by decide +kernel]
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r1⟩ ⟨c9,r1⟩ := by
    refine Quiet.step_of (by change (0x80005400#32).getLsbD 0=false;decide) LoopMemmoveZeroCode.at2147505152 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r1 0 [] [] = ⟨.ok c9 r1 [],[]⟩
    have v10 : c8.get 10=dst := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
    have move : alu .add (0 : Word) dst=dst := by
      change 0#32+dst=dst
      exact BitVec.zero_add dst
    rw [exec_op,Core.get_zero,v10,move];rfl
  have t9 : Quiet.Step B img ⟨c9,r1⟩ ⟨c10,r1⟩ := by
    refine Quiet.step_of (by change (0x80005402#32).getLsbD 0=false;decide) LoopMemmoveZeroCode.at2147505154 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r1 0 [] [] = ⟨.ok c10 r1 [],[]⟩
    have v10 : c9.get 10=dst := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
    have v12 : c9.get 12=0#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
    rw [exec_op,v10,v12];simp only [alu,BitVec.add_zero];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r1⟩ ⟨c11,r1⟩ := by
    refine Quiet.step_of (by change (0x80005406#32).getLsbD 0=false;decide) LoopMemmoveZeroCode.at2147505158 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r1 0 [] [] = ⟨.ok c11 r1 [],[]⟩
    have v10 : c10.get 10=dst := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
    have v14 : c10.get 14=dst := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
    rw [exec_branch,v10,v14,show taken .ltu dst dst=false by simp [taken,BitVec.ult]];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r1⟩ ⟨c12,r1⟩ := by
    refine Quiet.step_of (by change (0x8000540a#32).getLsbD 0=false;decide) LoopMemmoveZeroCode.at2147505162 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r1 0 [] [] = ⟨.ok c12 r1 [],[]⟩
    rw [exec_jal,show c11.pc=0x8000540a#32 from rfl,show 0x8000540a#32+552#32=0x80005632#32 by decide +kernel]
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,r1⟩ ⟨c13,r1⟩ := by
    refine Quiet.step_of (by change (0x80005632#32).getLsbD 0=false;decide) LoopMemmoveZeroCode.at2147505714 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r1 0 [] [] = ⟨.ok c13 r1 [],[]⟩
    have v2 : c12.get 2=0x80ffeb70#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
    rw [exec_load,v2,show 0x80ffeb70#32+28#32=0x80ffeb8c#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (by decide +kernel)
        (by simpa only [show 0x80ffeb70#32+28#32=0x80ffeb8c#32 by decide +kernel] using Memory.block_access stack (off := 28) (by decide) (by decide))]
    rw [ramRead_ramWrite_w];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r1⟩ ⟨c14,r1⟩ := by
    refine Quiet.step_of (by change (0x80005634#32).getLsbD 0=false;decide) LoopMemmoveZeroCode.at2147505716 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r1 0 [] [] = ⟨.ok c14 r1 [],[]⟩
    have v2 : c13.get 2=0x80ffeb70#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,r1⟩ ⟨c15,r1⟩ := by
    refine Quiet.step_of (by change (0x80005636#32).getLsbD 0=false;decide) LoopMemmoveZeroCode.at2147505718 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) r1 0 [] [] = ⟨.ok c15 r1 [],[]⟩
    have v1 : c14.get 1=0x800017e0#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump c14 0x800017e0#32) r1 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c15,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.single t14)))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret]
  · intro reg h6 h2 h13 h14 h8;simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,x8,x10,x11,zero,ret,h6,h2,h13,h14,h8]
end E5R.Thermostat.LoopMemmoveZero
