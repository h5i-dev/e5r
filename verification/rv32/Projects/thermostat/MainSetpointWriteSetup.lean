import Projects.thermostat.MainSetpointRouterCode
import Projects.thermostat.QuietRam
import Projects.thermostat.FrameOffsets
import Projects.thermostat.ViewFrame
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainSetpointWriteSetup
open E5R E5R.Thermostat
abbrev sp : Word := 0x80ffeb90#32

def memory (ram : Word → BitVec 8)  :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+3680#32) (0#32) .w) (sp+3912#32) (0#32) .b) (sp+3888#32) (832#32) .w) (sp+3872#32) (2164255748#32) .w) (sp+3876#32) (2164258944#32) .w) (sp+3880#32) (2164255676#32) .w) (sp+3884#32) (2164258004#32) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (h2 : c.get 2=0x80ffeb90#32) (h8 : c.get 8=0x80fff814#32) (h10 : c.get 10=1#32) (h11 : c.get 11=0#32) (h22 : c.get 22=1#32)
    (stack : Memory.Block B 0x80ffeb90#32 5232)
    (futureRouter : ramRead ram 0x80fffa98#32 .w=0x80ffebf0#32)
    (futureRequest : ramRead ram 0x80fffa9c#32 .w=0x80fff880#32)
    (futureEngine : ramRead ram 0x80fffaa0#32 .w=0x80ffebbc#32)
    (futurePayload : ramRead ram 0x80fffaa4#32 .w=0x80fff4d4#32)
    (futureCapacity : ramRead ram 0x80fffaa8#32 .w=832#32)
    (methodPut : ram 0x80fff9f4#32=3#8) (routePut : ram 0x80ffec04#32=3#8)
    (hp : c.pc=0x80001422#32) :
    ∃ d, Quiet.Steps B img 28 ⟨c,ram⟩ ⟨d,memory ram ⟩ ∧ d.pc=0x800004c6#32 ∧
      d.get 13=2164255676#32 ∧ d.get 10=2164260152#32 ∧ d.get 12=2164258944#32 ∧ d.get 11=2164259504#32 ∧ d.get 14=2164258004#32 ∧ d.get 9=4#32 ∧ d.get 1=2147489320#32 ∧ (∀ r : Reg, r≠13 → r≠10 → r≠12 → r≠11 → r≠14 → r≠9 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80001426#32
  let c2 := c1.wr 13 (2164255728#32) 0x8000142a#32
  let c3 := c2.wr 10 (2164258944#32) 0x8000142e#32
  let c4 := c3.wr 12 (3#32) 0x80001432#32
  let c5 := c4.wr 13 (3#32) 0x80001436#32
  let c6 := c5.goto 0x80001514#32
  let r1 := ramWrite ram (sp+3680#32) (0#32) .w
  let c7 := c6.goto 0x80001518#32
  let r2 := ramWrite r1 (sp+3912#32) (0#32) .b
  let c8 := c7.goto 0x8000151c#32
  let c9 := c8.wr 10 (832#32) 0x80001520#32
  let c10 := c9.wr 11 (2164255728#32) 0x80001524#32
  let c11 := c10.wr 12 (2164258944#32) 0x80001528#32
  let c12 := c11.wr 13 (2164255676#32) 0x8000152c#32
  let c13 := c12.wr 14 (2164258004#32) 0x80001530#32
  let r3 := ramWrite r2 (sp+3888#32) (832#32) .w
  let c14 := c13.goto 0x80001534#32
  let c15 := c14.wr 11 (2164255748#32) 0x80001536#32
  let r4 := ramWrite r3 (sp+3872#32) (2164255748#32) .w
  let c16 := c15.goto 0x8000153a#32
  let r5 := ramWrite r4 (sp+3876#32) (2164258944#32) .w
  let c17 := c16.goto 0x8000153e#32
  let r6 := ramWrite r5 (sp+3880#32) (2164255676#32) .w
  let c18 := c17.goto 0x80001542#32
  let r7 := ramWrite r6 (sp+3884#32) (2164258004#32) .w
  let c19 := c18.goto 0x80001546#32
  let c20 := c19.wr 9 (4#32) 0x80001548#32
  let c21 := c20.goto 0x80001610#32
  let c22 := c21.wr 10 (4096#32) 0x80001612#32
  let c23 := c22.wr 10 (4520#32) 0x80001616#32
  let c24 := c23.wr 10 (2164260152#32) 0x80001618#32
  let c25 := c24.wr 11 (2164257679#32) 0x8000161c#32
  let c26 := c25.wr 11 (2164259504#32) 0x80001620#32
  let c27 := c26.wr 1 (2147485216#32) 0x80001624#32
  let c28 := c27.wr 1 (2147489320#32) 0x800004c6#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact sc2147488802) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v10 : c.get 10=1#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    have v22 : c.get 22=1#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_branch,v10,v22,show taken .ne 1#32 1#32=false by decide +kernel]
    first | rfl | (rw [hp];first | rfl | (rw [hp];rfl))
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80001426#32).getLsbD 0=false;decide) sc2147488806 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=2164258836#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_load,v8,show 2164258836#32+644#32=sp+3848#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 962 (by decide +kernel)) (Memory.block_access stack (off := 3848) (by decide) (by decide))]
    have saved : ramRead ram (sp+3848#32) .w=ramRead ram (sp+3848#32) .w := by
      rfl
    change Observed.interp B img o (.done (c1.wr 13 (extend .w true (ramRead ram (sp+3848#32) .w)) (c1.pc+4#32))) ram 0 [] []=_
    rw [saved,show sp+3848#32=2164259480#32 by decide +kernel,futureRouter];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000142a#32).getLsbD 0=false;decide) sc2147488810 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v8 : c2.get 8=2164258836#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_load,v8,show 2164258836#32+648#32=sp+3852#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 963 (by decide +kernel)) (Memory.block_access stack (off := 3852) (by decide) (by decide))]
    have saved : ramRead ram (sp+3852#32) .w=ramRead ram (sp+3852#32) .w := by
      rfl
    change Observed.interp B img o (.done (c2.wr 10 (extend .w true (ramRead ram (sp+3852#32) .w)) (c2.pc+4#32))) ram 0 [] []=_
    rw [saved,show sp+3852#32=2164259484#32 by decide +kernel,futureRequest];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x8000142e#32).getLsbD 0=false;decide) sc2147488814 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v10 : c3.get 10=2164258944#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_load,v10,show 2164258944#32+372#32=sp+3684#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3684) (by decide) (by decide))]
    change Observed.interp B img o (.done (c3.wr 12 (extend .b false (BitVec.ofNat 32 (ram 2164259316#32).toNat)) (c3.pc+4#32))) ram 0 [] []=_
    rw [methodPut];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80001432#32).getLsbD 0=false;decide) sc2147488818 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v13 : c4.get 13=2164255728#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_load,v13,show 2164255728#32+20#32=sp+116#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 116) (by decide) (by decide))]
    change Observed.interp B img o (.done (c4.wr 13 (extend .b false (BitVec.ofNat 32 (ram 2164255748#32).toNat)) (c4.pc+4#32))) ram 0 [] []=_
    rw [routePut];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80001436#32).getLsbD 0=false;decide) sc2147488822 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v13 : c5.get 13=3#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    have v12 : c5.get 12=3#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_branch,v13,v12,show taken .eq 3#32 3#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c5.pc=2147488822#32 from rfl,show 2147488822#32+222#32=2147489044#32 by decide +kernel]
    change Observed.interp B img o (jump c5 2147489044#32) ram 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,r1⟩ := by
    refine Quiet.step_of (by change (0x80001514#32).getLsbD 0=false;decide) sc2147489044 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 r1 [],[]⟩
    have v10 : c6.get 10=2164258944#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    have v11 : c6.get 11=0#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_store,v10,v11,show 2164258944#32+368#32=sp+3680#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 920 (by decide +kernel)) (Memory.block_access stack (off := 3680) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r1⟩ ⟨c8,r2⟩ := by
    refine Quiet.step_of (by change (0x80001518#32).getLsbD 0=false;decide) sc2147489048 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r1 0 [] [] = ⟨.ok c8 r2 [],[]⟩
    have v8 : c7.get 8=2164258836#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    have v0 : c7.get 0=0#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_store,v8,v0,show 2164258836#32+708#32=sp+3912#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3912) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r2⟩ ⟨c9,r2⟩ := by
    refine Quiet.step_of (by change (0x8000151c#32).getLsbD 0=false;decide) sc2147489052 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r2 0 [] [] = ⟨.ok c9 r2 [],[]⟩
    have v8 : c8.get 8=2164258836#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_load,v8,show 2164258836#32+660#32=sp+3864#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 966 (by decide +kernel)) (Memory.block_access stack (off := 3864) (by decide) (by decide))]
    have saved : ramRead r2 (sp+3864#32) .w=ramRead ram (sp+3864#32) .w := by
      rw [FrameOffsets.word _ sp _ 3864 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ sp _ 3864 3680 .w (by decide) (by decide) (by decide)]
    change Observed.interp B img o (.done (c8.wr 10 (extend .w true (ramRead r2 (sp+3864#32) .w)) (c8.pc+4#32))) r2 0 [] []=_
    rw [saved,show sp+3864#32=2164259496#32 by decide +kernel,futureCapacity];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r2⟩ ⟨c10,r2⟩ := by
    refine Quiet.step_of (by change (0x80001520#32).getLsbD 0=false;decide) sc2147489056 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r2 0 [] [] = ⟨.ok c10 r2 [],[]⟩
    have v8 : c9.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_load,v8,show 2164258836#32+644#32=sp+3848#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 962 (by decide +kernel)) (Memory.block_access stack (off := 3848) (by decide) (by decide))]
    have saved : ramRead r2 (sp+3848#32) .w=ramRead ram (sp+3848#32) .w := by
      rw [FrameOffsets.word _ sp _ 3848 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ sp _ 3848 3680 .w (by decide) (by decide) (by decide)]
    change Observed.interp B img o (.done (c9.wr 11 (extend .w true (ramRead r2 (sp+3848#32) .w)) (c9.pc+4#32))) r2 0 [] []=_
    rw [saved,show sp+3848#32=2164259480#32 by decide +kernel,futureRouter];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r2⟩ ⟨c11,r2⟩ := by
    refine Quiet.step_of (by change (0x80001524#32).getLsbD 0=false;decide) sc2147489060 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r2 0 [] [] = ⟨.ok c11 r2 [],[]⟩
    have v8 : c10.get 8=2164258836#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_load,v8,show 2164258836#32+648#32=sp+3852#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 963 (by decide +kernel)) (Memory.block_access stack (off := 3852) (by decide) (by decide))]
    have saved : ramRead r2 (sp+3852#32) .w=ramRead ram (sp+3852#32) .w := by
      rw [FrameOffsets.word _ sp _ 3852 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ sp _ 3852 3680 .w (by decide) (by decide) (by decide)]
    change Observed.interp B img o (.done (c10.wr 12 (extend .w true (ramRead r2 (sp+3852#32) .w)) (c10.pc+4#32))) r2 0 [] []=_
    rw [saved,show sp+3852#32=2164259484#32 by decide +kernel,futureRequest];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r2⟩ ⟨c12,r2⟩ := by
    refine Quiet.step_of (by change (0x80001528#32).getLsbD 0=false;decide) sc2147489064 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r2 0 [] [] = ⟨.ok c12 r2 [],[]⟩
    have v8 : c11.get 8=2164258836#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_load,v8,show 2164258836#32+652#32=sp+3856#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 964 (by decide +kernel)) (Memory.block_access stack (off := 3856) (by decide) (by decide))]
    have saved : ramRead r2 (sp+3856#32) .w=ramRead ram (sp+3856#32) .w := by
      rw [FrameOffsets.word _ sp _ 3856 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ sp _ 3856 3680 .w (by decide) (by decide) (by decide)]
    change Observed.interp B img o (.done (c11.wr 13 (extend .w true (ramRead r2 (sp+3856#32) .w)) (c11.pc+4#32))) r2 0 [] []=_
    rw [saved,show sp+3856#32=2164259488#32 by decide +kernel,futureEngine];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,r2⟩ ⟨c13,r2⟩ := by
    refine Quiet.step_of (by change (0x8000152c#32).getLsbD 0=false;decide) sc2147489068 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r2 0 [] [] = ⟨.ok c13 r2 [],[]⟩
    have v8 : c12.get 8=2164258836#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_load,v8,show 2164258836#32+656#32=sp+3860#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 965 (by decide +kernel)) (Memory.block_access stack (off := 3860) (by decide) (by decide))]
    have saved : ramRead r2 (sp+3860#32) .w=ramRead ram (sp+3860#32) .w := by
      rw [FrameOffsets.word _ sp _ 3860 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ sp _ 3860 3680 .w (by decide) (by decide) (by decide)]
    change Observed.interp B img o (.done (c12.wr 14 (extend .w true (ramRead r2 (sp+3860#32) .w)) (c12.pc+4#32))) r2 0 [] []=_
    rw [saved,show sp+3860#32=2164259492#32 by decide +kernel,futurePayload];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r2⟩ ⟨c14,r3⟩ := by
    refine Quiet.step_of (by change (0x80001530#32).getLsbD 0=false;decide) sc2147489072 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r2 0 [] [] = ⟨.ok c14 r3 [],[]⟩
    have v8 : c13.get 8=2164258836#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    have v10 : c13.get 10=832#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_store,v8,v10,show 2164258836#32+684#32=sp+3888#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 972 (by decide +kernel)) (Memory.block_access stack (off := 3888) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,r3⟩ ⟨c15,r3⟩ := by
    refine Quiet.step_of (by change (0x80001534#32).getLsbD 0=false;decide) sc2147489076 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) r3 0 [] [] = ⟨.ok c15 r3 [],[]⟩
    have v11 : c14.get 11=2164255728#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_opimm,v11,show alu .add 2164255728#32 20#32=2164255748#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,r3⟩ ⟨c16,r4⟩ := by
    refine Quiet.step_of (by change (0x80001536#32).getLsbD 0=false;decide) sc2147489078 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) r3 0 [] [] = ⟨.ok c16 r4 [],[]⟩
    have v8 : c15.get 8=2164258836#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    have v11 : c15.get 11=2164255748#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_store,v8,v11,show 2164258836#32+668#32=sp+3872#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 968 (by decide +kernel)) (Memory.block_access stack (off := 3872) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,r4⟩ ⟨c17,r5⟩ := by
    refine Quiet.step_of (by change (0x8000153a#32).getLsbD 0=false;decide) sc2147489082 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) r4 0 [] [] = ⟨.ok c17 r5 [],[]⟩
    have v8 : c16.get 8=2164258836#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    have v12 : c16.get 12=2164258944#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_store,v8,v12,show 2164258836#32+672#32=sp+3876#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 969 (by decide +kernel)) (Memory.block_access stack (off := 3876) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,r5⟩ ⟨c18,r6⟩ := by
    refine Quiet.step_of (by change (0x8000153e#32).getLsbD 0=false;decide) sc2147489086 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) r5 0 [] [] = ⟨.ok c18 r6 [],[]⟩
    have v8 : c17.get 8=2164258836#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    have v13 : c17.get 13=2164255676#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_store,v8,v13,show 2164258836#32+676#32=sp+3880#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 970 (by decide +kernel)) (Memory.block_access stack (off := 3880) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,r6⟩ ⟨c19,r7⟩ := by
    refine Quiet.step_of (by change (0x80001542#32).getLsbD 0=false;decide) sc2147489090 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) r6 0 [] [] = ⟨.ok c19 r7 [],[]⟩
    have v8 : c18.get 8=2164258836#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    have v14 : c18.get 14=2164258004#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_store,v8,v14,show 2164258836#32+680#32=sp+3884#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 971 (by decide +kernel)) (Memory.block_access stack (off := 3884) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,r7⟩ ⟨c20,r7⟩ := by
    refine Quiet.step_of (by change (0x80001546#32).getLsbD 0=false;decide) sc2147489094 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) r7 0 [] [] = ⟨.ok c20 r7 [],[]⟩
    have v0 : c19.get 0=0#32 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_opimm,v0,show alu .add 0#32 4#32=4#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,r7⟩ ⟨c21,r7⟩ := by
    refine Quiet.step_of (by change (0x80001548#32).getLsbD 0=false;decide) sc2147489096 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) r7 0 [] [] = ⟨.ok c21 r7 [],[]⟩
    rw [exec_jal,show c20.pc=2147489096#32 from rfl,show 2147489096#32+200#32=2147489296#32 by decide +kernel]
    change Observed.interp B img o (jump c20 2147489296#32) r7 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,r7⟩ ⟨c22,r7⟩ := by
    refine Quiet.step_of (by change (0x80001610#32).getLsbD 0=false;decide) sc2147489296 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) r7 0 [] [] = ⟨.ok c22 r7 [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,r7⟩ ⟨c23,r7⟩ := by
    refine Quiet.step_of (by change (0x80001612#32).getLsbD 0=false;decide) sc2147489298 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) r7 0 [] [] = ⟨.ok c23 r7 [],[]⟩
    have v10 : c22.get 10=4096#32 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_opimm,v10,show alu .add 4096#32 424#32=4520#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t23 : Quiet.Step B img ⟨c23,r7⟩ ⟨c24,r7⟩ := by
    refine Quiet.step_of (by change (0x80001616#32).getLsbD 0=false;decide) sc2147489302 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) r7 0 [] [] = ⟨.ok c24 r7 [],[]⟩
    have v10 : c23.get 10=4520#32 := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    have v2 : c23.get 2=2164255632#32 := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_op,v10,v2,show alu .add 4520#32 2164255632#32=2164260152#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t24 : Quiet.Step B img ⟨c24,r7⟩ ⟨c25,r7⟩ := by
    refine Quiet.step_of (by change (0x80001618#32).getLsbD 0=false;decide) sc2147489304 fun o => ?_
    change Observed.interp B img o (exec c24 _ _) r7 0 [] [] = ⟨.ok c25 r7 [],[]⟩
    have v2 : c24.get 2=2164255632#32 := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_opimm,v2,show alu .add 2164255632#32 2047#32=2164257679#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t25 : Quiet.Step B img ⟨c25,r7⟩ ⟨c26,r7⟩ := by
    refine Quiet.step_of (by change (0x8000161c#32).getLsbD 0=false;decide) sc2147489308 fun o => ?_
    change Observed.interp B img o (exec c25 _ _) r7 0 [] [] = ⟨.ok c26 r7 [],[]⟩
    have v11 : c25.get 11=2164257679#32 := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_opimm,v11,show alu .add 2164257679#32 1825#32=2164259504#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t26 : Quiet.Step B img ⟨c26,r7⟩ ⟨c27,r7⟩ := by
    refine Quiet.step_of (by change (0x80001620#32).getLsbD 0=false;decide) sc2147489312 fun o => ?_
    change Observed.interp B img o (exec c26 _ _) r7 0 [] [] = ⟨.ok c27 r7 [],[]⟩
    rw [exec_auipc,show c26.pc=2147489312#32 from rfl,show 2147489312#32+4294963200#32=2147485216#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t27 : Quiet.Step B img ⟨c27,r7⟩ ⟨c28,r7⟩ := by
    refine Quiet.step_of (by change (0x80001624#32).getLsbD 0=false;decide) sc2147489316 fun o => ?_
    change Observed.interp B img o (exec c27 _ _) r7 0 [] [] = ⟨.ok c28 r7 [],[]⟩
    have v1 : c27.get 1=2147485216#32 := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c27.set 1 2147489320#32) 2147484870#32) r7 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c28,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.step t23 (.step t24 (.step t25 (.step t26 (.single t27))))))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
  · simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
  · simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
  · simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
  · simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
  · simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
  · simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22]
  · intro reg h13 h10 h12 h11 h14 h9 h1;simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h13,h10,h12,h11,h14,h9,h1]

/-- Exact writable Request count/future fields, with protected live regions. -/
theorem frame (ram : Word → BitVec 8) (off size : Nat) (bound : off+size≤5232)
    (apart : off+size≤3680 ∨ (3684≤off ∧ off+size≤3872) ∨ 3913≤off) :
    ViewFrame.Region ram (memory ram) (sp+BitVec.ofNat 32 off) size := by
  intro i
  unfold memory
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3884 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3880 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3876 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3872 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3888 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    exact FrameOffsets.ne sp off 3912 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<1 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<1 at hj;rcases apart with h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3680 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h <;>omega))]

theorem params_count (ram : Word → BitVec 8) : ramRead (memory ram) (sp+3680#32) .w=0#32 := by
  unfold memory
  rw [FrameOffsets.word _ sp _ 3680 3884 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3880 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3876 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3872 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3888 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3912 .b (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem request (ram : Word → BitVec 8) : ramRead (memory ram) (sp+3876#32) .w=0x80fff880#32 := by
  unfold memory
  rw [FrameOffsets.word _ sp _ 3876 3884 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3876 3880 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem engine (ram : Word → BitVec 8) : ramRead (memory ram) (sp+3880#32) .w=0x80ffebbc#32 := by
  unfold memory
  rw [FrameOffsets.word _ sp _ 3880 3884 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem pointer (ram : Word → BitVec 8) : ramRead (memory ram) (sp+3884#32) .w=0x80fff4d4#32 := by
  unfold memory
  exact ramRead_ramWrite_w _ _ _

theorem capacity (ram : Word → BitVec 8) : ramRead (memory ram) (sp+3888#32) .w=832#32 := by
  unfold memory
  rw [FrameOffsets.word _ sp _ 3888 3884 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3888 3880 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3888 3876 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3888 3872 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem fresh (ram : Word → BitVec 8) : memory ram (sp+3912#32)=0#8 := by
  unfold memory
  rw [FrameOffsets.byte _ sp _ 3912 3884 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp _ 3912 3880 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp _ 3912 3876 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp _ 3912 3872 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp _ 3912 3888 .w (by decide) (by decide) (by decide)]
  change ramPut _ (sp+3912#32) 0#8 (sp+3912#32)=0#8
  exact ramPut_eq _ _ _
end E5R.Thermostat.MainSetpointWriteSetup
