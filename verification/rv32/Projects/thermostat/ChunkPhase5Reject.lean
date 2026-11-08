import Projects.thermostat.ChunkCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ChunkPhase5Reject
open E5R E5R.Thermostat

def memory (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (dst+16#32) (extend .w true (ramRead ram (src+16#32) .w)) .w) (dst+20#32) (extend .w true (ramRead ram (src+20#32) .w)) .w) (dst+24#32) (extend .w true (ramRead ram (src+24#32) .w)) .w) (dst+28#32) (extend .w true (ramRead ram (src+28#32) .w)) .w) (dst+0#32) (extend .w true (ramRead ram (src+0#32) .w)) .w) (dst+4#32) (extend .w true (ramRead ram (src+4#32) .w)) .w) (dst+8#32) (extend .w true (ramRead ram (src+8#32) .w)) .w) (dst+12#32) (extend .w true (ramRead ram (src+12#32) .w)) .w) (dst+32#32) (alu .add (0x01900000#32) 0x00000003#32) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word)
    (h10 : c.get 10=dst) (h11 : c.get 11=src) (h12 : c.get 12=input) (h13 : c.get 13=limit)
    (hsm : Memory.Block B src 32) (hdm : Memory.Block B dst 36)
    (hsa : src.toNat%4=0) (hda : dst.toNat%4=0)
    (hphase : ram (src+24#32)=5#8)
    (hbr0 : taken .ge (alu .add (0#32) 0x00000002#32) (5#32)=false)
    (hbr1 : taken .lt (alu .add (0#32) 0x00000004#32) (5#32)=true)
    (hbr2 : taken .eq (5#32) (alu .add (0#32) 0x00000005#32)=true)
    (hbr3 : taken .ne (input) (alu .add (0#32) 0x0000000d#32)=true)
    (hp : c.pc=0x80002998#32) :
    ∃ d, Quiet.Steps B img 29 ⟨c,ram⟩ ⟨d,memory c ram src dst input limit⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧
      (∀ r : Reg, r≠14 → r≠15 → r≠13 → r≠12 → r≠16 → r≠17 → r≠5 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (5#32) 0x8000299c#32
  let c2 := c1.wr 15 (alu .add (0#32) 0x00000002#32) 0x8000299e#32
  let c3 := c2.goto 0x800029a2#32
  let c4 := c3.wr 13 (alu .add (0#32) 0x00000004#32) 0x800029a4#32
  let c5 := c4.goto 0x80002a1e#32
  let c6 := c5.wr 13 (alu .add (0#32) 0x00000005#32) 0x80002a20#32
  let c7 := c6.goto 0x80002a9c#32
  let c8 := c7.wr 13 (alu .add (0#32) 0x0000000d#32) 0x80002a9e#32
  let c9 := c8.goto 0x80002bc8#32
  let c10 := c9.wr 12 (extend .w true (ramRead ram (src+16#32) .w)) 0x80002bca#32
  let c11 := c10.wr 13 (extend .w true (ramRead ram (src+20#32) .w)) 0x80002bcc#32
  let c12 := c11.wr 14 (extend .w true (ramRead ram (src+24#32) .w)) 0x80002bce#32
  let c13 := c12.wr 15 (extend .w true (ramRead ram (src+28#32) .w)) 0x80002bd0#32
  let c14 := c13.wr 16 (extend .w true (ramRead ram (src+0#32) .w)) 0x80002bd4#32
  let c15 := c14.wr 17 (extend .w true (ramRead ram (src+4#32) .w)) 0x80002bd8#32
  let c16 := c15.wr 5 (extend .w true (ramRead ram (src+8#32) .w)) 0x80002bdc#32
  let c17 := c16.wr 11 (extend .w true (ramRead ram (src+12#32) .w)) 0x80002bde#32
  let r18 := ramWrite ram (dst+16#32) (extend .w true (ramRead ram (src+16#32) .w)) .w
  let c18 := c17.goto 0x80002be0#32
  let r19 := ramWrite r18 (dst+20#32) (extend .w true (ramRead ram (src+20#32) .w)) .w
  let c19 := c18.goto 0x80002be2#32
  let r20 := ramWrite r19 (dst+24#32) (extend .w true (ramRead ram (src+24#32) .w)) .w
  let c20 := c19.goto 0x80002be4#32
  let r21 := ramWrite r20 (dst+28#32) (extend .w true (ramRead ram (src+28#32) .w)) .w
  let c21 := c20.goto 0x80002be6#32
  let c22 := c21.wr 12 (0x01900000#32) 0x80002bea#32
  let c23 := c22.wr 12 (alu .add (0x01900000#32) 0x00000003#32) 0x80002bec#32
  let r24 := ramWrite r21 (dst+0#32) (extend .w true (ramRead ram (src+0#32) .w)) .w
  let c24 := c23.goto 0x80002bf0#32
  let r25 := ramWrite r24 (dst+4#32) (extend .w true (ramRead ram (src+4#32) .w)) .w
  let c25 := c24.goto 0x80002bf4#32
  let r26 := ramWrite r25 (dst+8#32) (extend .w true (ramRead ram (src+8#32) .w)) .w
  let c26 := c25.goto 0x80002bf8#32
  let r27 := ramWrite r26 (dst+12#32) (extend .w true (ramRead ram (src+12#32) .w)) .w
  let c27 := c26.goto 0x80002bfa#32
  let r28 := ramWrite r27 (dst+32#32) (alu .add (0x01900000#32) 0x00000003#32) .w
  let c28 := c27.goto 0x80002bfc#32
  let c29 := c28.goto (c.get 1 &&& ~~~1)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact ck2147494296) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v11 : c.get 11=(src) := by simp [Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hsm (off := 24) (by decide) (by decide)),Memory.load_byte,hphase];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000299c#32).getLsbD 0=false;decide) ck2147494300 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v0 : c1.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_opimm,v0];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000299e#32).getLsbD 0=false;decide) ck2147494302 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v15 : c2.get 15=(alu .add (0#32) 0x00000002#32) := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v14 : c2.get 14=(5#32) := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v14,hbr0]
    try simp only [ite_true,ite_false]
    first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800029a2#32).getLsbD 0=false;decide) ck2147494306 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v0 : c3.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_opimm,v0];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800029a4#32).getLsbD 0=false;decide) ck2147494308 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v13 : c4.get 13=(alu .add (0#32) 0x00000004#32) := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v14 : c4.get 14=(5#32) := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v13,v14,hbr1]
    try simp only [ite_true,ite_false]
    rw [show c4.pc=0x800029a4#32 by rfl,show 0x800029a4#32+0x0000007a#32=0x80002a1e#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80002a1e#32).getLsbD 0=false;decide) ck2147494430 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v0 : c5.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_opimm,v0];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80002a20#32).getLsbD 0=false;decide) ck2147494432 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v14 : c6.get 14=(5#32) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c6.get 13=(alu .add (0#32) 0x00000005#32) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v14,v13,hbr2]
    try simp only [ite_true,ite_false]
    rw [show c6.pc=0x80002a20#32 by rfl,show 0x80002a20#32+0x0000007c#32=0x80002a9c#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80002a9c#32).getLsbD 0=false;decide) ck2147494556 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v0 : c7.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_opimm,v0];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80002a9e#32).getLsbD 0=false;decide) ck2147494558 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v12 : c8.get 12=(input) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c8.get 13=(alu .add (0#32) 0x0000000d#32) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v12,v13,hbr3]
    try simp only [ite_true,ite_false]
    rw [show c8.pc=0x80002a9e#32 by rfl,show 0x80002a9e#32+0x0000012a#32=0x80002bc8#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bc8#32).getLsbD 0=false;decide) ck2147494856 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v11 : c9.get 11=(src) := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 4 hsa) (Memory.block_access hsm (off := 16) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bca#32).getLsbD 0=false;decide) ck2147494858 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v11 : c10.get 11=(src) := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 5 hsa) (Memory.block_access hsm (off := 20) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bcc#32).getLsbD 0=false;decide) ck2147494860 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v11 : c11.get 11=(src) := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 6 hsa) (Memory.block_access hsm (off := 24) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bce#32).getLsbD 0=false;decide) ck2147494862 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    have v11 : c12.get 11=(src) := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 7 hsa) (Memory.block_access hsm (off := 28) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bd0#32).getLsbD 0=false;decide) ck2147494864 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 ram [],[]⟩
    have v11 : c13.get 11=(src) := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 0 hsa) (Memory.block_access hsm (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bd4#32).getLsbD 0=false;decide) ck2147494868 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) ram 0 [] [] = ⟨.ok c15 ram [],[]⟩
    have v11 : c14.get 11=(src) := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 1 hsa) (Memory.block_access hsm (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,ram⟩ ⟨c16,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bd8#32).getLsbD 0=false;decide) ck2147494872 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) ram 0 [] [] = ⟨.ok c16 ram [],[]⟩
    have v11 : c15.get 11=(src) := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 2 hsa) (Memory.block_access hsm (off := 8) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,ram⟩ ⟨c17,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bdc#32).getLsbD 0=false;decide) ck2147494876 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) ram 0 [] [] = ⟨.ok c17 ram [],[]⟩
    have v11 : c16.get 11=(src) := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 3 hsa) (Memory.block_access hsm (off := 12) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,ram⟩ ⟨c18,r18⟩ := by
    refine Quiet.step_of (by change (0x80002bde#32).getLsbD 0=false;decide) ck2147494878 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) ram 0 [] [] = ⟨.ok c18 r18 [],[]⟩
    have v10 : c17.get 10=(dst) := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c17.get 12=(extend .w true (ramRead ram (src+16#32) .w)) := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v12,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 4 hda) (Memory.block_access hdm (off := 16) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,r18⟩ ⟨c19,r19⟩ := by
    refine Quiet.step_of (by change (0x80002be0#32).getLsbD 0=false;decide) ck2147494880 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) r18 0 [] [] = ⟨.ok c19 r19 [],[]⟩
    have v10 : c18.get 10=(dst) := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c18.get 13=(extend .w true (ramRead ram (src+20#32) .w)) := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v13,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 5 hda) (Memory.block_access hdm (off := 20) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,r19⟩ ⟨c20,r20⟩ := by
    refine Quiet.step_of (by change (0x80002be2#32).getLsbD 0=false;decide) ck2147494882 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) r19 0 [] [] = ⟨.ok c20 r20 [],[]⟩
    have v10 : c19.get 10=(dst) := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v14 : c19.get 14=(extend .w true (ramRead ram (src+24#32) .w)) := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v14,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 6 hda) (Memory.block_access hdm (off := 24) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,r20⟩ ⟨c21,r21⟩ := by
    refine Quiet.step_of (by change (0x80002be4#32).getLsbD 0=false;decide) ck2147494884 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) r20 0 [] [] = ⟨.ok c21 r21 [],[]⟩
    have v10 : c20.get 10=(dst) := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c20.get 15=(extend .w true (ramRead ram (src+28#32) .w)) := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v15,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 7 hda) (Memory.block_access hdm (off := 28) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,r21⟩ ⟨c22,r21⟩ := by
    refine Quiet.step_of (by change (0x80002be6#32).getLsbD 0=false;decide) ck2147494886 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) r21 0 [] [] = ⟨.ok c22 r21 [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,r21⟩ ⟨c23,r21⟩ := by
    refine Quiet.step_of (by change (0x80002bea#32).getLsbD 0=false;decide) ck2147494890 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) r21 0 [] [] = ⟨.ok c23 r21 [],[]⟩
    have v12 : c22.get 12=(0x01900000#32) := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v12];first | rfl | (rw [hp];rfl)
  have t23 : Quiet.Step B img ⟨c23,r21⟩ ⟨c24,r24⟩ := by
    refine Quiet.step_of (by change (0x80002bec#32).getLsbD 0=false;decide) ck2147494892 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) r21 0 [] [] = ⟨.ok c24 r24 [],[]⟩
    have v10 : c23.get 10=(dst) := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v16 : c23.get 16=(extend .w true (ramRead ram (src+0#32) .w)) := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v16,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 0 hda) (Memory.block_access hdm (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t24 : Quiet.Step B img ⟨c24,r24⟩ ⟨c25,r25⟩ := by
    refine Quiet.step_of (by change (0x80002bf0#32).getLsbD 0=false;decide) ck2147494896 fun o => ?_
    change Observed.interp B img o (exec c24 _ _) r24 0 [] [] = ⟨.ok c25 r25 [],[]⟩
    have v10 : c24.get 10=(dst) := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v17 : c24.get 17=(extend .w true (ramRead ram (src+4#32) .w)) := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v17,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 1 hda) (Memory.block_access hdm (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t25 : Quiet.Step B img ⟨c25,r25⟩ ⟨c26,r26⟩ := by
    refine Quiet.step_of (by change (0x80002bf4#32).getLsbD 0=false;decide) ck2147494900 fun o => ?_
    change Observed.interp B img o (exec c25 _ _) r25 0 [] [] = ⟨.ok c26 r26 [],[]⟩
    have v10 : c25.get 10=(dst) := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v5 : c25.get 5=(extend .w true (ramRead ram (src+8#32) .w)) := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v5,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 2 hda) (Memory.block_access hdm (off := 8) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t26 : Quiet.Step B img ⟨c26,r26⟩ ⟨c27,r27⟩ := by
    refine Quiet.step_of (by change (0x80002bf8#32).getLsbD 0=false;decide) ck2147494904 fun o => ?_
    change Observed.interp B img o (exec c26 _ _) r26 0 [] [] = ⟨.ok c27 r27 [],[]⟩
    have v10 : c26.get 10=(dst) := by simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c26.get 11=(extend .w true (ramRead ram (src+12#32) .w)) := by simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v11,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 3 hda) (Memory.block_access hdm (off := 12) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t27 : Quiet.Step B img ⟨c27,r27⟩ ⟨c28,r28⟩ := by
    refine Quiet.step_of (by change (0x80002bfa#32).getLsbD 0=false;decide) ck2147494906 fun o => ?_
    change Observed.interp B img o (exec c27 _ _) r27 0 [] [] = ⟨.ok c28 r28 [],[]⟩
    have v10 : c27.get 10=(dst) := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c27.get 12=(alu .add (0x01900000#32) 0x00000003#32) := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v12,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 8 hda) (Memory.block_access hdm (off := 32) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t28 : Quiet.Step B img ⟨c28,r28⟩ ⟨c29,r28⟩ := by
    refine Quiet.step_of (by change (0x80002bfc#32).getLsbD 0=false;decide) ck2147494908 fun o => ?_
    change Observed.interp B img o (exec c28 _ _) r28 0 [] [] = ⟨.ok c29 r28 [],[]⟩
    have v1 : c28.get 1=(c.get 1) := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_jalr,v1,BitVec.add_zero]
    change Observed.interp B img o (jump c28 (c.get 1 &&& ~~~1)) r28 0 [] [] = _
    rw [jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨c29,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.step t23 (.step t24 (.step t25 (.step t26 (.step t27 (.single t28)))))))))))))))))))))))))))),rfl,?_,by rfl⟩
  intro reg hr14 hr15 hr13 hr12 hr16 hr17 hr5 hr11
  simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hr14,hr15,hr13,hr12,hr16,hr17,hr5,hr11]
end E5R.Thermostat.ChunkPhase5Reject
