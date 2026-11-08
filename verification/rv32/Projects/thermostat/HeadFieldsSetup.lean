import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.FrameOffsets
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadFieldsSetup
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp buf body length : Word) :=
  ramWrite (ramWrite (ramWrite (ram) (sp+8#32) (body) .w) (sp+16#32) (buf+1#32) .w) (sp+12#32) (length+0xffffffff#32) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf body length : Word) (h2 : c.get 2=sp) (h20 : c.get 20=sp+3664#32)
(hbody : ramRead ram (sp+3668#32) .w=body) (hlen : ramRead ram (sp+48#32) .w=length) (hbuf : ramRead ram (sp+44#32) .w=buf)
(hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0)
    (hp : c.pc=0x80002f28#32) :
    ∃ d, Quiet.Steps B img 18 ⟨c,ram⟩ ⟨d,memory ram sp buf body length⟩ ∧ d.pc=0x80002f58#32 ∧
      d.get 23=0#32 ∧ d.get 9=0#32 ∧ d.get 10=buf+1#32 ∧ d.get 11=length+0xffffffff#32 ∧ d.get 22=0#32-length ∧ d.get 16=10#32 ∧ d.get 17=13#32 ∧ d.get 5=33#32 ∧ d.get 6=48#32 ∧ d.get 7=14#32 ∧ d.get 28=58#32 ∧ d.get 27=91#32 ∧ (∀ r : Reg, r≠23 → r≠9 → r≠10 → r≠11 → r≠22 → r≠16 → r≠17 → r≠5 → r≠6 → r≠7 → r≠28 → r≠27 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 23 (0#32) 0x80002f2a#32
  let c2 := c1.wr 9 (0#32) 0x80002f2c#32
  let c3 := c2.wr 10 (body) 0x80002f30#32
  let r1 := ramWrite ram (sp+8#32) (body) .w
  let c4 := c3.goto 0x80002f32#32
  let c5 := c4.wr 11 (length) 0x80002f34#32
  let c6 := c5.wr 22 (0#32-length) 0x80002f38#32
  let c7 := c6.wr 10 (buf) 0x80002f3a#32
  let c8 := c7.wr 10 (buf+1#32) 0x80002f3c#32
  let r2 := ramWrite r1 (sp+16#32) (buf+1#32) .w
  let c9 := c8.goto 0x80002f3e#32
  let c10 := c9.wr 11 (length+0xffffffff#32) 0x80002f40#32
  let r3 := ramWrite r2 (sp+12#32) (length+0xffffffff#32) .w
  let c11 := c10.goto 0x80002f42#32
  let c12 := c11.wr 16 (10#32) 0x80002f44#32
  let c13 := c12.wr 17 (13#32) 0x80002f46#32
  let c14 := c13.wr 5 (33#32) 0x80002f4a#32
  let c15 := c14.wr 6 (48#32) 0x80002f4e#32
  let c16 := c15.wr 7 (14#32) 0x80002f50#32
  let c17 := c16.wr 28 (58#32) 0x80002f54#32
  let c18 := c17.wr 27 (91#32) 0x80002f58#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495720) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f2a#32).getLsbD 0=false;decide) hh2147495722 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f2c#32).getLsbD 0=false;decide) hh2147495724 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v20 : c2.get 20=sp+3664#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
    rw [exec_load,v20,show (sp+3664#32)+4#32=sp+3668#32 by rw [BitVec.add_assoc];first | rfl | (rw [hp];rfl),
    Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 917 ha)
      (Memory.block_access hm (off := 3668) (by decide) (by decide)),hbody];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,r1⟩ := by
    refine Quiet.step_of (by change (0x80002f30#32).getLsbD 0=false;decide) hh2147495728 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 r1 [],[]⟩
    have v2 : c3.get 2=sp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
    have v10 : c3.get 10=body := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
    rw [exec_store,v2,v10,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 2 ha)
      (Memory.block_access hm (off := 8) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r1⟩ ⟨c5,r1⟩ := by
    refine Quiet.step_of (by change (0x80002f32#32).getLsbD 0=false;decide) hh2147495730 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r1 0 [] [] = ⟨.ok c5 r1 [],[]⟩
    have v2 : c4.get 2=sp := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
    have word : ramRead r1 (sp+48#32) .w=length := by
      dsimp [r1]
      rw [FrameOffsets.word ram sp body 48 8 .w (by decide) (by decide) (by decide),hlen]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 12 ha)
      (Memory.block_access hm (off := 48) (by decide) (by decide)),word];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r1⟩ ⟨c6,r1⟩ := by
    refine Quiet.step_of (by change (0x80002f34#32).getLsbD 0=false;decide) hh2147495732 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r1 0 [] [] = ⟨.ok c6 r1 [],[]⟩
    have v11 : c5.get 11=length := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
    rw [exec_op,Core.get_zero,v11];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r1⟩ ⟨c7,r1⟩ := by
    refine Quiet.step_of (by change (0x80002f38#32).getLsbD 0=false;decide) hh2147495736 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r1 0 [] [] = ⟨.ok c7 r1 [],[]⟩
    have v2 : c6.get 2=sp := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
    have word : ramRead r1 (sp+44#32) .w=buf := by
      dsimp [r1]
      rw [FrameOffsets.word ram sp body 44 8 .w (by decide) (by decide) (by decide),hbuf]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 11 ha)
      (Memory.block_access hm (off := 44) (by decide) (by decide)),word];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r1⟩ ⟨c8,r1⟩ := by
    refine Quiet.step_of (by change (0x80002f3a#32).getLsbD 0=false;decide) hh2147495738 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r1 0 [] [] = ⟨.ok c8 r1 [],[]⟩
    have v10 : c7.get 10=buf := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r1⟩ ⟨c9,r2⟩ := by
    refine Quiet.step_of (by change (0x80002f3c#32).getLsbD 0=false;decide) hh2147495740 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r1 0 [] [] = ⟨.ok c9 r2 [],[]⟩
    have v2 : c8.get 2=sp := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
    have v10 : c8.get 10=buf+1#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
    rw [exec_store,v2,v10,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 4 ha)
      (Memory.block_access hm (off := 16) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r2⟩ ⟨c10,r2⟩ := by
    refine Quiet.step_of (by change (0x80002f3e#32).getLsbD 0=false;decide) hh2147495742 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r2 0 [] [] = ⟨.ok c10 r2 [],[]⟩
    have v11 : c9.get 11=length := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
    rw [exec_opimm,v11];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r2⟩ ⟨c11,r3⟩ := by
    refine Quiet.step_of (by change (0x80002f40#32).getLsbD 0=false;decide) hh2147495744 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r2 0 [] [] = ⟨.ok c11 r3 [],[]⟩
    have v2 : c10.get 2=sp := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
    have v11 : c10.get 11=length+0xffffffff#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
    rw [exec_store,v2,v11,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 3 ha)
      (Memory.block_access hm (off := 12) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r3⟩ ⟨c12,r3⟩ := by
    refine Quiet.step_of (by change (0x80002f42#32).getLsbD 0=false;decide) hh2147495746 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r3 0 [] [] = ⟨.ok c12 r3 [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,r3⟩ ⟨c13,r3⟩ := by
    refine Quiet.step_of (by change (0x80002f44#32).getLsbD 0=false;decide) hh2147495748 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r3 0 [] [] = ⟨.ok c13 r3 [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r3⟩ ⟨c14,r3⟩ := by
    refine Quiet.step_of (by change (0x80002f46#32).getLsbD 0=false;decide) hh2147495750 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r3 0 [] [] = ⟨.ok c14 r3 [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,r3⟩ ⟨c15,r3⟩ := by
    refine Quiet.step_of (by change (0x80002f4a#32).getLsbD 0=false;decide) hh2147495754 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) r3 0 [] [] = ⟨.ok c15 r3 [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,r3⟩ ⟨c16,r3⟩ := by
    refine Quiet.step_of (by change (0x80002f4e#32).getLsbD 0=false;decide) hh2147495758 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) r3 0 [] [] = ⟨.ok c16 r3 [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,r3⟩ ⟨c17,r3⟩ := by
    refine Quiet.step_of (by change (0x80002f50#32).getLsbD 0=false;decide) hh2147495760 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) r3 0 [] [] = ⟨.ok c17 r3 [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,r3⟩ ⟨c18,r3⟩ := by
    refine Quiet.step_of (by change (0x80002f54#32).getLsbD 0=false;decide) hh2147495764 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) r3 0 [] [] = ⟨.ok c18 r3 [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  refine ⟨c18,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.single t17))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
  · simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
  · simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
  · simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
  · simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
  · simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
  · simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
  · simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
  · simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
  · simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
  · simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
  · simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20]
  · intro reg h23 h9 h10 h11 h22 h16 h17 h5 h6 h7 h28 h27;simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h20,h23,h9,h10,h11,h22,h16,h17,h5,h6,h7,h28,h27]
end E5R.Thermostat.HeadFieldsSetup
