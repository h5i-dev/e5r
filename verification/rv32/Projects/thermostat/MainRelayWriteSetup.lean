import Projects.thermostat.MainRelayRouterCode
import Projects.thermostat.QuietRam
import Projects.thermostat.FrameOffsets
import Projects.thermostat.ViewFrame
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainRelayWriteSetup
open E5R E5R.Thermostat
abbrev sp : Word := 0x80ffeb90#32

def memory (ram : Word → BitVec 8) (savedIo : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+3680#32) (1#32) .w) (sp+3780#32) (0#32) .b) (sp+3756#32) (832#32) .w) (sp+3740#32) (2164255760#32) .w) (sp+3744#32) (2164258944#32) .w) (sp+3748#32) (2164255676#32) .w) (sp+3752#32) (2164258004#32) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (savedIo : Word) (h2 : c.get 2=0x80ffeb90#32) (h8 : c.get 8=0x80fff814#32) (h10 : c.get 10=1#32) (h11 : c.get 11=1#32) (h22 : c.get 22=1#32) (h24 : c.get 24=0x80fffa2c#32)
    (stack : Memory.Block B 0x80ffeb90#32 5232)
    (savedIoWord : ramRead ram (sp+20#32) .w=savedIo)
    (futureRouter : ramRead ram 0x80fffa14#32 .w=0x80ffebd8#32)
    (futureRequest : ramRead ram 0x80fffa18#32 .w=0x80fff880#32)
    (futureEngine : ramRead ram 0x80fffa1c#32 .w=0x80ffebbc#32)
    (futurePayload : ramRead ram 0x80fffa20#32 .w=0x80fff4d4#32)
    (futureCapacity : ramRead ram 0x80fffa24#32 .w=832#32)
    (methodPut : ram 0x80fff9f4#32=3#8) (routePut : ram 0x80ffec10#32=3#8)
    (hp : c.pc=0x80001856#32) :
    ∃ d, Quiet.Steps B img 26 ⟨c,ram⟩ ⟨d,memory ram savedIo⟩ ∧ d.pc=0x800004c6#32 ∧
      d.get 13=2164255676#32 ∧ d.get 10=2164260152#32 ∧ d.get 12=2164258944#32 ∧ d.get 6=savedIo ∧ d.get 11=2164259372#32 ∧ d.get 14=2164258004#32 ∧ d.get 1=2147490156#32 ∧ (∀ r : Reg, r≠13 → r≠10 → r≠12 → r≠6 → r≠11 → r≠14 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x8000185a#32
  let c2 := c1.wr 13 (2164255704#32) 0x8000185e#32
  let c3 := c2.wr 10 (2164258944#32) 0x80001862#32
  let c4 := c3.wr 12 (3#32) 0x80001866#32
  let c5 := c4.wr 13 (3#32) 0x8000186a#32
  let c6 := c5.wr 6 (savedIo) 0x8000186c#32
  let c7 := c6.goto 0x80001926#32
  let r1 := ramWrite ram (sp+3680#32) (1#32) .w
  let c8 := c7.goto 0x8000192a#32
  let r2 := ramWrite r1 (sp+3780#32) (0#32) .b
  let c9 := c8.goto 0x8000192e#32
  let c10 := c9.wr 10 (832#32) 0x80001932#32
  let c11 := c10.wr 11 (2164255704#32) 0x80001936#32
  let c12 := c11.wr 12 (2164258944#32) 0x8000193a#32
  let c13 := c12.wr 13 (2164255676#32) 0x8000193e#32
  let c14 := c13.wr 14 (2164258004#32) 0x80001942#32
  let r3 := ramWrite r2 (sp+3756#32) (832#32) .w
  let c15 := c14.goto 0x80001946#32
  let c16 := c15.wr 10 (2164255760#32) 0x8000194a#32
  let r4 := ramWrite r3 (sp+3740#32) (2164255760#32) .w
  let c17 := c16.goto 0x8000194e#32
  let r5 := ramWrite r4 (sp+3744#32) (2164258944#32) .w
  let c18 := c17.goto 0x80001952#32
  let r6 := ramWrite r5 (sp+3748#32) (2164255676#32) .w
  let c19 := c18.goto 0x80001956#32
  let r7 := ramWrite r6 (sp+3752#32) (2164258004#32) .w
  let c20 := c19.goto 0x8000195a#32
  let c21 := c20.wr 10 (4096#32) 0x8000195c#32
  let c22 := c21.wr 10 (4520#32) 0x80001960#32
  let c23 := c22.wr 10 (2164260152#32) 0x80001962#32
  let c24 := c23.wr 11 (2164259372#32) 0x80001964#32
  let c25 := c24.wr 1 (2147486052#32) 0x80001968#32
  let c26 := c25.wr 1 (2147490156#32) 0x800004c6#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rl2147489878) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v10 : c.get 10=1#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    have v22 : c.get 22=1#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_branch,v10,v22,show taken .ne 1#32 1#32=false by decide +kernel]
    first | rfl | (rw [hp];first | rfl | (rw [hp];rfl))
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000185a#32).getLsbD 0=false;decide) rl2147489882 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=2164258836#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_load,v8,show 2164258836#32+512#32=sp+3716#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 929 (by decide +kernel)) (Memory.block_access stack (off := 3716) (by decide) (by decide))]
    have saved : ramRead ram (sp+3716#32) .w=ramRead ram (sp+3716#32) .w := by
      rfl
    change Observed.interp B img o (.done (c1.wr 13 (extend .w true (ramRead ram (sp+3716#32) .w)) (c1.pc+4#32))) ram 0 [] []=_
    rw [saved,show sp+3716#32=2164259348#32 by decide +kernel,futureRouter];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000185e#32).getLsbD 0=false;decide) rl2147489886 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v8 : c2.get 8=2164258836#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_load,v8,show 2164258836#32+516#32=sp+3720#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 930 (by decide +kernel)) (Memory.block_access stack (off := 3720) (by decide) (by decide))]
    have saved : ramRead ram (sp+3720#32) .w=ramRead ram (sp+3720#32) .w := by
      rfl
    change Observed.interp B img o (.done (c2.wr 10 (extend .w true (ramRead ram (sp+3720#32) .w)) (c2.pc+4#32))) ram 0 [] []=_
    rw [saved,show sp+3720#32=2164259352#32 by decide +kernel,futureRequest];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80001862#32).getLsbD 0=false;decide) rl2147489890 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v10 : c3.get 10=2164258944#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_load,v10,show 2164258944#32+372#32=sp+3684#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3684) (by decide) (by decide))]
    change Observed.interp B img o (.done (c3.wr 12 (extend .b false (BitVec.ofNat 32 (ram 2164259316#32).toNat)) (c3.pc+4#32))) ram 0 [] []=_
    rw [methodPut];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80001866#32).getLsbD 0=false;decide) rl2147489894 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v13 : c4.get 13=2164255704#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_load,v13,show 2164255704#32+56#32=sp+128#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 128) (by decide) (by decide))]
    change Observed.interp B img o (.done (c4.wr 13 (extend .b false (BitVec.ofNat 32 (ram 2164255760#32).toNat)) (c4.pc+4#32))) ram 0 [] []=_
    rw [routePut];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x8000186a#32).getLsbD 0=false;decide) rl2147489898 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v2 : c5.get 2=2164255632#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_load,v2,show 2164255632#32+20#32=sp+20#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 5 (by decide +kernel)) (Memory.block_access stack (off := 20) (by decide) (by decide))]
    have saved : ramRead ram (sp+20#32) .w=ramRead ram (sp+20#32) .w := by
      rfl
    change Observed.interp B img o (.done (c5.wr 6 (extend .w true (ramRead ram (sp+20#32) .w)) (c5.pc+2#32))) ram 0 [] []=_
    rw [saved,savedIoWord];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x8000186c#32).getLsbD 0=false;decide) rl2147489900 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v13 : c6.get 13=3#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    have v12 : c6.get 12=3#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_branch,v13,v12,show taken .eq 3#32 3#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c6.pc=2147489900#32 from rfl,show 2147489900#32+186#32=2147490086#32 by decide +kernel]
    change Observed.interp B img o (jump c6 2147490086#32) ram 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,r1⟩ := by
    refine Quiet.step_of (by change (0x80001926#32).getLsbD 0=false;decide) rl2147490086 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 r1 [],[]⟩
    have v10 : c7.get 10=2164258944#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    have v11 : c7.get 11=1#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_store,v10,v11,show 2164258944#32+368#32=sp+3680#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 920 (by decide +kernel)) (Memory.block_access stack (off := 3680) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r1⟩ ⟨c9,r2⟩ := by
    refine Quiet.step_of (by change (0x8000192a#32).getLsbD 0=false;decide) rl2147490090 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r1 0 [] [] = ⟨.ok c9 r2 [],[]⟩
    have v8 : c8.get 8=2164258836#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    have v0 : c8.get 0=0#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_store,v8,v0,show 2164258836#32+576#32=sp+3780#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3780) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r2⟩ ⟨c10,r2⟩ := by
    refine Quiet.step_of (by change (0x8000192e#32).getLsbD 0=false;decide) rl2147490094 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r2 0 [] [] = ⟨.ok c10 r2 [],[]⟩
    have v8 : c9.get 8=2164258836#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_load,v8,show 2164258836#32+528#32=sp+3732#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 933 (by decide +kernel)) (Memory.block_access stack (off := 3732) (by decide) (by decide))]
    have saved : ramRead r2 (sp+3732#32) .w=ramRead ram (sp+3732#32) .w := by
      rw [FrameOffsets.word _ sp _ 3732 3780 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ sp _ 3732 3680 .w (by decide) (by decide) (by decide)]
    change Observed.interp B img o (.done (c9.wr 10 (extend .w true (ramRead r2 (sp+3732#32) .w)) (c9.pc+4#32))) r2 0 [] []=_
    rw [saved,show sp+3732#32=2164259364#32 by decide +kernel,futureCapacity];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r2⟩ ⟨c11,r2⟩ := by
    refine Quiet.step_of (by change (0x80001932#32).getLsbD 0=false;decide) rl2147490098 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r2 0 [] [] = ⟨.ok c11 r2 [],[]⟩
    have v8 : c10.get 8=2164258836#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_load,v8,show 2164258836#32+512#32=sp+3716#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 929 (by decide +kernel)) (Memory.block_access stack (off := 3716) (by decide) (by decide))]
    have saved : ramRead r2 (sp+3716#32) .w=ramRead ram (sp+3716#32) .w := by
      rw [FrameOffsets.word _ sp _ 3716 3780 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ sp _ 3716 3680 .w (by decide) (by decide) (by decide)]
    change Observed.interp B img o (.done (c10.wr 11 (extend .w true (ramRead r2 (sp+3716#32) .w)) (c10.pc+4#32))) r2 0 [] []=_
    rw [saved,show sp+3716#32=2164259348#32 by decide +kernel,futureRouter];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r2⟩ ⟨c12,r2⟩ := by
    refine Quiet.step_of (by change (0x80001936#32).getLsbD 0=false;decide) rl2147490102 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r2 0 [] [] = ⟨.ok c12 r2 [],[]⟩
    have v8 : c11.get 8=2164258836#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_load,v8,show 2164258836#32+516#32=sp+3720#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 930 (by decide +kernel)) (Memory.block_access stack (off := 3720) (by decide) (by decide))]
    have saved : ramRead r2 (sp+3720#32) .w=ramRead ram (sp+3720#32) .w := by
      rw [FrameOffsets.word _ sp _ 3720 3780 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ sp _ 3720 3680 .w (by decide) (by decide) (by decide)]
    change Observed.interp B img o (.done (c11.wr 12 (extend .w true (ramRead r2 (sp+3720#32) .w)) (c11.pc+4#32))) r2 0 [] []=_
    rw [saved,show sp+3720#32=2164259352#32 by decide +kernel,futureRequest];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,r2⟩ ⟨c13,r2⟩ := by
    refine Quiet.step_of (by change (0x8000193a#32).getLsbD 0=false;decide) rl2147490106 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r2 0 [] [] = ⟨.ok c13 r2 [],[]⟩
    have v8 : c12.get 8=2164258836#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_load,v8,show 2164258836#32+520#32=sp+3724#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 931 (by decide +kernel)) (Memory.block_access stack (off := 3724) (by decide) (by decide))]
    have saved : ramRead r2 (sp+3724#32) .w=ramRead ram (sp+3724#32) .w := by
      rw [FrameOffsets.word _ sp _ 3724 3780 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ sp _ 3724 3680 .w (by decide) (by decide) (by decide)]
    change Observed.interp B img o (.done (c12.wr 13 (extend .w true (ramRead r2 (sp+3724#32) .w)) (c12.pc+4#32))) r2 0 [] []=_
    rw [saved,show sp+3724#32=2164259356#32 by decide +kernel,futureEngine];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r2⟩ ⟨c14,r2⟩ := by
    refine Quiet.step_of (by change (0x8000193e#32).getLsbD 0=false;decide) rl2147490110 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r2 0 [] [] = ⟨.ok c14 r2 [],[]⟩
    have v8 : c13.get 8=2164258836#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_load,v8,show 2164258836#32+524#32=sp+3728#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 932 (by decide +kernel)) (Memory.block_access stack (off := 3728) (by decide) (by decide))]
    have saved : ramRead r2 (sp+3728#32) .w=ramRead ram (sp+3728#32) .w := by
      rw [FrameOffsets.word _ sp _ 3728 3780 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ sp _ 3728 3680 .w (by decide) (by decide) (by decide)]
    change Observed.interp B img o (.done (c13.wr 14 (extend .w true (ramRead r2 (sp+3728#32) .w)) (c13.pc+4#32))) r2 0 [] []=_
    rw [saved,show sp+3728#32=2164259360#32 by decide +kernel,futurePayload];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,r2⟩ ⟨c15,r3⟩ := by
    refine Quiet.step_of (by change (0x80001942#32).getLsbD 0=false;decide) rl2147490114 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) r2 0 [] [] = ⟨.ok c15 r3 [],[]⟩
    have v8 : c14.get 8=2164258836#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    have v10 : c14.get 10=832#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_store,v8,v10,show 2164258836#32+552#32=sp+3756#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 939 (by decide +kernel)) (Memory.block_access stack (off := 3756) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,r3⟩ ⟨c16,r3⟩ := by
    refine Quiet.step_of (by change (0x80001946#32).getLsbD 0=false;decide) rl2147490118 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) r3 0 [] [] = ⟨.ok c16 r3 [],[]⟩
    have v11 : c15.get 11=2164255704#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_opimm,v11,show alu .add 2164255704#32 56#32=2164255760#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,r3⟩ ⟨c17,r4⟩ := by
    refine Quiet.step_of (by change (0x8000194a#32).getLsbD 0=false;decide) rl2147490122 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) r3 0 [] [] = ⟨.ok c17 r4 [],[]⟩
    have v8 : c16.get 8=2164258836#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    have v10 : c16.get 10=2164255760#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_store,v8,v10,show 2164258836#32+536#32=sp+3740#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 935 (by decide +kernel)) (Memory.block_access stack (off := 3740) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,r4⟩ ⟨c18,r5⟩ := by
    refine Quiet.step_of (by change (0x8000194e#32).getLsbD 0=false;decide) rl2147490126 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) r4 0 [] [] = ⟨.ok c18 r5 [],[]⟩
    have v8 : c17.get 8=2164258836#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    have v12 : c17.get 12=2164258944#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_store,v8,v12,show 2164258836#32+540#32=sp+3744#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 936 (by decide +kernel)) (Memory.block_access stack (off := 3744) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,r5⟩ ⟨c19,r6⟩ := by
    refine Quiet.step_of (by change (0x80001952#32).getLsbD 0=false;decide) rl2147490130 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) r5 0 [] [] = ⟨.ok c19 r6 [],[]⟩
    have v8 : c18.get 8=2164258836#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    have v13 : c18.get 13=2164255676#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_store,v8,v13,show 2164258836#32+544#32=sp+3748#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 937 (by decide +kernel)) (Memory.block_access stack (off := 3748) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,r6⟩ ⟨c20,r7⟩ := by
    refine Quiet.step_of (by change (0x80001956#32).getLsbD 0=false;decide) rl2147490134 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) r6 0 [] [] = ⟨.ok c20 r7 [],[]⟩
    have v8 : c19.get 8=2164258836#32 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    have v14 : c19.get 14=2164258004#32 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_store,v8,v14,show 2164258836#32+548#32=sp+3752#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 938 (by decide +kernel)) (Memory.block_access stack (off := 3752) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,r7⟩ ⟨c21,r7⟩ := by
    refine Quiet.step_of (by change (0x8000195a#32).getLsbD 0=false;decide) rl2147490138 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) r7 0 [] [] = ⟨.ok c21 r7 [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,r7⟩ ⟨c22,r7⟩ := by
    refine Quiet.step_of (by change (0x8000195c#32).getLsbD 0=false;decide) rl2147490140 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) r7 0 [] [] = ⟨.ok c22 r7 [],[]⟩
    have v10 : c21.get 10=4096#32 := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_opimm,v10,show alu .add 4096#32 424#32=4520#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,r7⟩ ⟨c23,r7⟩ := by
    refine Quiet.step_of (by change (0x80001960#32).getLsbD 0=false;decide) rl2147490144 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) r7 0 [] [] = ⟨.ok c23 r7 [],[]⟩
    have v10 : c22.get 10=4520#32 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    have v2 : c22.get 2=2164255632#32 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_op,v10,v2,show alu .add 4520#32 2164255632#32=2164260152#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t23 : Quiet.Step B img ⟨c23,r7⟩ ⟨c24,r7⟩ := by
    refine Quiet.step_of (by change (0x80001962#32).getLsbD 0=false;decide) rl2147490146 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) r7 0 [] [] = ⟨.ok c24 r7 [],[]⟩
    have v0 : c23.get 0=0#32 := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    have v24 : c23.get 24=2164259372#32 := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_op,v0,v24,show alu .add 0#32 2164259372#32=2164259372#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t24 : Quiet.Step B img ⟨c24,r7⟩ ⟨c25,r7⟩ := by
    refine Quiet.step_of (by change (0x80001964#32).getLsbD 0=false;decide) rl2147490148 fun o => ?_
    change Observed.interp B img o (exec c24 _ _) r7 0 [] [] = ⟨.ok c25 r7 [],[]⟩
    rw [exec_auipc,show c24.pc=2147490148#32 from rfl,show 2147490148#32+4294963200#32=2147486052#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t25 : Quiet.Step B img ⟨c25,r7⟩ ⟨c26,r7⟩ := by
    refine Quiet.step_of (by change (0x80001968#32).getLsbD 0=false;decide) rl2147490152 fun o => ?_
    change Observed.interp B img o (exec c25 _ _) r7 0 [] [] = ⟨.ok c26 r7 [],[]⟩
    have v1 : c25.get 1=2147486052#32 := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c25.set 1 2147490156#32) 2147484870#32) r7 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c26,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.step t23 (.step t24 (.single t25))))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
  · simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
  · simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
  · simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
  · simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
  · simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
  · simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24]
  · intro reg h13 h10 h12 h6 h11 h14 h1;simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h11,h22,h24,h13,h10,h12,h6,h11,h14,h1]

theorem frame (ram : Word → BitVec 8) (savedIo : Word) (off size : Nat) (bound : off+size≤5232)
    (apart : off+size≤3680 ∨ (3684≤off ∧ off+size≤3740) ∨ 3781≤off) :
    ViewFrame.Region ram (memory ram savedIo) (sp+BitVec.ofNat 32 off) size := by
  intro i
  unfold memory
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3752 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3748 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3744 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3740 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3756 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    exact FrameOffsets.ne sp off 3780 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<1 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<1 at hj;rcases apart with h|h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3680 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h|h <;>omega))]

theorem params_count (ram : Word → BitVec 8) (savedIo : Word) : ramRead (memory ram savedIo) (sp+3680#32) .w=1#32 := by
  unfold memory
  rw [FrameOffsets.word _ sp _ 3680 3752 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3748 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3744 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3740 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3756 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3680 3780 .b (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem request (ram : Word → BitVec 8) (savedIo : Word) : ramRead (memory ram savedIo) (sp+3744#32) .w=0x80fff880#32 := by
  unfold memory
  rw [FrameOffsets.word _ sp _ 3744 3752 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3744 3748 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem engine (ram : Word → BitVec 8) (savedIo : Word) : ramRead (memory ram savedIo) (sp+3748#32) .w=0x80ffebbc#32 := by
  unfold memory
  rw [FrameOffsets.word _ sp _ 3748 3752 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem pointer (ram : Word → BitVec 8) (savedIo : Word) : ramRead (memory ram savedIo) (sp+3752#32) .w=0x80fff4d4#32 := by
  unfold memory
  exact ramRead_ramWrite_w _ _ _

theorem capacity (ram : Word → BitVec 8) (savedIo : Word) : ramRead (memory ram savedIo) (sp+3756#32) .w=832#32 := by
  unfold memory
  rw [FrameOffsets.word _ sp _ 3756 3752 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3756 3748 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3756 3744 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.word _ sp _ 3756 3740 .w (by decide) (by decide) (by decide)]
  exact ramRead_ramWrite_w _ _ _

theorem fresh (ram : Word → BitVec 8) (savedIo : Word) : memory ram savedIo (sp+3780#32)=0#8 := by
  unfold memory
  rw [FrameOffsets.byte _ sp _ 3780 3752 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp _ 3780 3748 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp _ 3780 3744 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp _ 3780 3740 .w (by decide) (by decide) (by decide)]
  rw [FrameOffsets.byte _ sp _ 3780 3756 .w (by decide) (by decide) (by decide)]
  change ramPut _ (sp+3780#32) 0#8 (sp+3780#32)=0#8
  exact ramPut_eq _ _ _
end E5R.Thermostat.MainRelayWriteSetup
