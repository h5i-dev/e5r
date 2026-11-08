import Projects.thermostat.ChunkCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ChunkPhase4Accept
open E5R E5R.Thermostat

def memory (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (dst+0#32) (0#32) .w) (dst+4#32) (0#32) .w) (dst+8#32) (extend .w true (ramRead ram (src+8#32) .w)) .w) (dst+12#32) (extend .w true (ramRead ram (src+12#32) .w)) .w) (dst+16#32) (extend .w true (ramRead ram (src+16#32) .w)) .w) (dst+20#32) (extend .w true (ramRead ram (src+20#32) .w)) .w) (dst+24#32) (0#32) .b) (dst+32#32) (0#32) .h

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word)
    (h10 : c.get 10=dst) (h11 : c.get 11=src) (h12 : c.get 12=input) (h13 : c.get 13=limit)
    (hsm : Memory.Block B src 32) (hdm : Memory.Block B dst 36)
    (hsa : src.toNat%4=0) (hda : dst.toNat%4=0)
    (hphase : ram (src+24#32)=4#8)
    (hbr0 : taken .ge (alu .add (0#32) 0x00000002#32) (4#32)=false)
    (hbr1 : taken .lt (alu .add (0#32) 0x00000004#32) (4#32)=false)
    (hbr2 : taken .eq (4#32) (alu .add (0#32) 0x00000003#32)=false)
    (hbr3 : taken .ne (4#32) (alu .add (0#32) 0x00000004#32)=false)
    (hbr4 : taken .eq (input) (alu .add (0#32) 0x0000000a#32)=true)
    (hp : c.pc=0x80002998#32) :
    ∃ d, Quiet.Steps B img 24 ⟨c,ram⟩ ⟨d,memory c ram src dst input limit⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧
      (∀ r : Reg, r≠14 → r≠15 → r≠13 → r≠11 → r≠16 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (4#32) 0x8000299c#32
  let c2 := c1.wr 15 (alu .add (0#32) 0x00000002#32) 0x8000299e#32
  let c3 := c2.goto 0x800029a2#32
  let c4 := c3.wr 13 (alu .add (0#32) 0x00000004#32) 0x800029a4#32
  let c5 := c4.goto 0x800029a8#32
  let c6 := c5.wr 13 (alu .add (0#32) 0x00000003#32) 0x800029aa#32
  let c7 := c6.goto 0x800029ae#32
  let c8 := c7.wr 13 (alu .add (0#32) 0x00000004#32) 0x800029b0#32
  let c9 := c8.goto 0x800029b4#32
  let c10 := c9.wr 13 (extend .w true (ramRead ram (src+8#32) .w)) 0x800029b6#32
  let c11 := c10.wr 14 (extend .w true (ramRead ram (src+12#32) .w)) 0x800029b8#32
  let c12 := c11.wr 15 (extend .w true (ramRead ram (src+16#32) .w)) 0x800029ba#32
  let c13 := c12.wr 11 (extend .w true (ramRead ram (src+20#32) .w)) 0x800029bc#32
  let c14 := c13.wr 16 (alu .add (0#32) 0x0000000a#32) 0x800029be#32
  let r15 := ramWrite ram (dst+0#32) (0#32) .w
  let c15 := c14.goto 0x800029c2#32
  let r16 := ramWrite r15 (dst+4#32) (0#32) .w
  let c16 := c15.goto 0x800029c6#32
  let r17 := ramWrite r16 (dst+8#32) (extend .w true (ramRead ram (src+8#32) .w)) .w
  let c17 := c16.goto 0x800029c8#32
  let r18 := ramWrite r17 (dst+12#32) (extend .w true (ramRead ram (src+12#32) .w)) .w
  let c18 := c17.goto 0x800029ca#32
  let r19 := ramWrite r18 (dst+16#32) (extend .w true (ramRead ram (src+16#32) .w)) .w
  let c19 := c18.goto 0x800029cc#32
  let r20 := ramWrite r19 (dst+20#32) (extend .w true (ramRead ram (src+20#32) .w)) .w
  let c20 := c19.goto 0x800029ce#32
  let c21 := c20.goto 0x80002b5e#32
  let r22 := ramWrite r20 (dst+24#32) (0#32) .b
  let c22 := c21.goto 0x80002b62#32
  let r23 := ramWrite r22 (dst+32#32) (0#32) .h
  let c23 := c22.goto 0x80002b66#32
  let c24 := c23.goto (c.get 1 &&& ~~~1)
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
    have v14 : c2.get 14=(4#32) := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
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
    have v14 : c4.get 14=(4#32) := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v13,v14,hbr1]
    try simp only [ite_true,ite_false]
    first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800029a8#32).getLsbD 0=false;decide) ck2147494312 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v0 : c5.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_opimm,v0];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x800029aa#32).getLsbD 0=false;decide) ck2147494314 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v14 : c6.get 14=(4#32) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c6.get 13=(alu .add (0#32) 0x00000003#32) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v14,v13,hbr2]
    try simp only [ite_true,ite_false]
    first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x800029ae#32).getLsbD 0=false;decide) ck2147494318 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v0 : c7.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_opimm,v0];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x800029b0#32).getLsbD 0=false;decide) ck2147494320 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v14 : c8.get 14=(4#32) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c8.get 13=(alu .add (0#32) 0x00000004#32) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v14,v13,hbr3]
    try simp only [ite_true,ite_false]
    first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x800029b4#32).getLsbD 0=false;decide) ck2147494324 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v11 : c9.get 11=(src) := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 2 hsa) (Memory.block_access hsm (off := 8) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x800029b6#32).getLsbD 0=false;decide) ck2147494326 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v11 : c10.get 11=(src) := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 3 hsa) (Memory.block_access hsm (off := 12) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x800029b8#32).getLsbD 0=false;decide) ck2147494328 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v11 : c11.get 11=(src) := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 4 hsa) (Memory.block_access hsm (off := 16) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x800029ba#32).getLsbD 0=false;decide) ck2147494330 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    have v11 : c12.get 11=(src) := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 5 hsa) (Memory.block_access hsm (off := 20) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine Quiet.step_of (by change (0x800029bc#32).getLsbD 0=false;decide) ck2147494332 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 ram [],[]⟩
    have v0 : c13.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_opimm,v0];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,r15⟩ := by
    refine Quiet.step_of (by change (0x800029be#32).getLsbD 0=false;decide) ck2147494334 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) ram 0 [] [] = ⟨.ok c15 r15 [],[]⟩
    have v10 : c14.get 10=(dst) := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v0 : c14.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_store,v10,v0,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 0 hda) (Memory.block_access hdm (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,r15⟩ ⟨c16,r16⟩ := by
    refine Quiet.step_of (by change (0x800029c2#32).getLsbD 0=false;decide) ck2147494338 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) r15 0 [] [] = ⟨.ok c16 r16 [],[]⟩
    have v10 : c15.get 10=(dst) := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v0 : c15.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_store,v10,v0,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 1 hda) (Memory.block_access hdm (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,r16⟩ ⟨c17,r17⟩ := by
    refine Quiet.step_of (by change (0x800029c6#32).getLsbD 0=false;decide) ck2147494342 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) r16 0 [] [] = ⟨.ok c17 r17 [],[]⟩
    have v10 : c16.get 10=(dst) := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c16.get 13=(extend .w true (ramRead ram (src+8#32) .w)) := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v13,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 2 hda) (Memory.block_access hdm (off := 8) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,r17⟩ ⟨c18,r18⟩ := by
    refine Quiet.step_of (by change (0x800029c8#32).getLsbD 0=false;decide) ck2147494344 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) r17 0 [] [] = ⟨.ok c18 r18 [],[]⟩
    have v10 : c17.get 10=(dst) := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v14 : c17.get 14=(extend .w true (ramRead ram (src+12#32) .w)) := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v14,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 3 hda) (Memory.block_access hdm (off := 12) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,r18⟩ ⟨c19,r19⟩ := by
    refine Quiet.step_of (by change (0x800029ca#32).getLsbD 0=false;decide) ck2147494346 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) r18 0 [] [] = ⟨.ok c19 r19 [],[]⟩
    have v10 : c18.get 10=(dst) := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c18.get 15=(extend .w true (ramRead ram (src+16#32) .w)) := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v15,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 4 hda) (Memory.block_access hdm (off := 16) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,r19⟩ ⟨c20,r20⟩ := by
    refine Quiet.step_of (by change (0x800029cc#32).getLsbD 0=false;decide) ck2147494348 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) r19 0 [] [] = ⟨.ok c20 r20 [],[]⟩
    have v10 : c19.get 10=(dst) := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c19.get 11=(extend .w true (ramRead ram (src+20#32) .w)) := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v11,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 5 hda) (Memory.block_access hdm (off := 20) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,r20⟩ ⟨c21,r20⟩ := by
    refine Quiet.step_of (by change (0x800029ce#32).getLsbD 0=false;decide) ck2147494350 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) r20 0 [] [] = ⟨.ok c21 r20 [],[]⟩
    have v12 : c20.get 12=(input) := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v16 : c20.get 16=(alu .add (0#32) 0x0000000a#32) := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v12,v16,hbr4]
    try simp only [ite_true,ite_false]
    rw [show c20.pc=0x800029ce#32 by rfl,show 0x800029ce#32+0x00000190#32=0x80002b5e#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have t21 : Quiet.Step B img ⟨c21,r20⟩ ⟨c22,r22⟩ := by
    refine Quiet.step_of (by change (0x80002b5e#32).getLsbD 0=false;decide) ck2147494750 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) r20 0 [] [] = ⟨.ok c22 r22 [],[]⟩
    have v10 : c21.get 10=(dst) := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v0 : c21.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_store,v10,v0,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hdm (off := 24) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,r22⟩ ⟨c23,r23⟩ := by
    refine Quiet.step_of (by change (0x80002b62#32).getLsbD 0=false;decide) ck2147494754 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) r22 0 [] [] = ⟨.ok c23 r23 [],[]⟩
    have v10 : c22.get 10=(dst) := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v0 : c22.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_store,v10,v0,Quiet.interp_store_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned dst 16 (by omega)) (Memory.block_access hdm (off := 32) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t23 : Quiet.Step B img ⟨c23,r23⟩ ⟨c24,r23⟩ := by
    refine Quiet.step_of (by change (0x80002b66#32).getLsbD 0=false;decide) ck2147494758 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) r23 0 [] [] = ⟨.ok c24 r23 [],[]⟩
    have v1 : c23.get 1=(c.get 1) := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_jalr,v1,BitVec.add_zero]
    change Observed.interp B img o (jump c23 (c.get 1 &&& ~~~1)) r23 0 [] [] = _
    rw [jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨c24,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.single t23))))))))))))))))))))))),rfl,?_,by rfl⟩
  intro reg hr14 hr15 hr13 hr11 hr16
  simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hr14,hr15,hr13,hr11,hr16]
end E5R.Thermostat.ChunkPhase4Accept
