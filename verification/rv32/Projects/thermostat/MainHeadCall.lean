import Projects.thermostat.FutureCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainHeadCall
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf cfg : Word) (h8 : c.get 8=0x80fff814#32) (h2 : c.get 2=0x80ffeb90#32)
(h108 : ramRead ram (0x80fff814#32+108#32) .w=buf) (h432 : ramRead ram (0x80fff814#32+432#32) .w=cfg)
(object : Memory.Block B 0x80fff814#32 449)
    (hp : c.pc=0x80000a10#32) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002c46#32 ∧
      d.get 11=buf ∧ d.get 13=cfg ∧ d.get 10=0x80fffd38#32 ∧ d.get 1=0x80000a26#32 ∧ (∀ r : Reg, r≠11 → r≠13 → r≠10 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (buf) 0x80000a12#32
  let c2 := c1.wr 13 (cfg) 0x80000a16#32
  let c3 := c2.wr 10 (4096#32) 0x80000a18#32
  let c4 := c3.wr 10 (4520#32) 0x80000a1c#32
  let c5 := c4.wr 10 (0x80fffd38#32) 0x80000a1e#32
  let c6 := c5.wr 1 (0x80002a1e#32) 0x80000a22#32
  let c7 := c6.wr 1 (0x80000a26#32) 0x80002c46#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact fu2147486224) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=0x80fff814#32 := by simp [Core.wr_get_ne,Core.wr_get,h8,h2]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (by decide +kernel) (Memory.block_access object (off := 108) (by decide) (by decide)),h108];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000a12#32).getLsbD 0=false;decide) fu2147486226 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=0x80fff814#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h2]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (by decide +kernel) (Memory.block_access object (off := 432) (by decide) (by decide)),h432];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000a16#32).getLsbD 0=false;decide) fu2147486230 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000a18#32).getLsbD 0=false;decide) fu2147486232 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v10 : c3.get 10=4096#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80000a1c#32).getLsbD 0=false;decide) fu2147486236 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v10 : c4.get 10=4520#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2]
    have v2 : c4.get 2=0x80ffeb90#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2]
    rw [exec_op,v10,v2];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80000a1e#32).getLsbD 0=false;decide) fu2147486238 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    rw [exec_auipc];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80000a22#32).getLsbD 0=false;decide) fu2147486242 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v1 : c6.get 1=0x80002a1e#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c6.set 1 0x80000a26#32) ((0x80002a1e#32+552#32) &&& ~~~1)) ram 0 [] []=_
    rw [show (0x80002a1e#32+552#32) &&& ~~~1=0x80002c46#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c7,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.single t6)))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2]
  · intro reg h11 h13 h10 h1;simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h11,h13,h10,h1]
end E5R.Thermostat.MainHeadCall
