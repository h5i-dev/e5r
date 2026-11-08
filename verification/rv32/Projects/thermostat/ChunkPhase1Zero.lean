import Projects.thermostat.ChunkCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ChunkPhase1Zero
open E5R E5R.Thermostat

def memory (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (dst+0#32) (extend .w true (ramRead ram (src+0#32) .w)) .w) (dst+4#32) (extend .w true (ramRead ram (src+4#32) .w)) .w) (dst+8#32) (0#32) .w) (dst+12#32) (0#32) .w) (dst+16#32) (extend .w true (ramRead ram (src+16#32) .w)) .w) (dst+20#32) (extend .w true (ramRead ram (src+20#32) .w)) .w) (dst+24#32) (alu .add (0#32) 0x00000005#32) .b) (dst+32#32) (0#32) .h

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word)
    (h10 : c.get 10=dst) (h11 : c.get 11=src) (h12 : c.get 12=input) (h13 : c.get 13=limit)
    (hsm : Memory.Block B src 32) (hdm : Memory.Block B dst 36)
    (hsa : src.toNat%4=0) (hda : dst.toNat%4=0)
    (hphase : ram (src+24#32)=1#8)
    (hbr0 : taken .ge (alu .add (0#32) 0x00000002#32) (1#32)=true)
    (hbr1 : taken .eq (1#32) (0#32)=false)
    (hbr2 : taken .eq (1#32) (alu .add (0#32) 0x00000001#32)=true)
    (hbr3 : taken .ne (input) (alu .add (0#32) 0x0000000a#32)=false)
    (hbr4 : taken .eq (alu .or (extend .w true (ramRead ram (src+0#32) .w)) (extend .w true (ramRead ram (src+4#32) .w))) (0#32)=true)
    (hp : c.pc=0x80002998#32) :
    ∃ d, Quiet.Steps B img 24 ⟨c,ram⟩ ⟨d,memory c ram src dst input limit⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧
      (∀ r : Reg, r≠14 → r≠15 → r≠13 → r≠12 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (1#32) 0x8000299c#32
  let c2 := c1.wr 15 (alu .add (0#32) 0x00000002#32) 0x8000299e#32
  let c3 := c2.goto 0x800029e2#32
  let c4 := c3.goto 0x800029e4#32
  let c5 := c4.wr 13 (alu .add (0#32) 0x00000001#32) 0x800029e6#32
  let c6 := c5.goto 0x80002ac0#32
  let c7 := c6.wr 13 (alu .add (0#32) 0x0000000a#32) 0x80002ac2#32
  let c8 := c7.goto 0x80002ac6#32
  let c9 := c8.wr 14 (extend .w true (ramRead ram (src+0#32) .w)) 0x80002ac8#32
  let c10 := c9.wr 13 (extend .w true (ramRead ram (src+4#32) .w)) 0x80002aca#32
  let c11 := c10.wr 12 (alu .or (extend .w true (ramRead ram (src+0#32) .w)) (extend .w true (ramRead ram (src+4#32) .w))) 0x80002ace#32
  let c12 := c11.goto 0x80002b68#32
  let c13 := c12.wr 12 (alu .add (0#32) 0x00000005#32) 0x80002b6a#32
  let c14 := c13.wr 15 (extend .w true (ramRead ram (src+16#32) .w)) 0x80002b6c#32
  let c15 := c14.wr 11 (extend .w true (ramRead ram (src+20#32) .w)) 0x80002b6e#32
  let r16 := ramWrite ram (dst+0#32) (extend .w true (ramRead ram (src+0#32) .w)) .w
  let c16 := c15.goto 0x80002b70#32
  let r17 := ramWrite r16 (dst+4#32) (extend .w true (ramRead ram (src+4#32) .w)) .w
  let c17 := c16.goto 0x80002b72#32
  let r18 := ramWrite r17 (dst+8#32) (0#32) .w
  let c18 := c17.goto 0x80002b76#32
  let r19 := ramWrite r18 (dst+12#32) (0#32) .w
  let c19 := c18.goto 0x80002b7a#32
  let r20 := ramWrite r19 (dst+16#32) (extend .w true (ramRead ram (src+16#32) .w)) .w
  let c20 := c19.goto 0x80002b7c#32
  let r21 := ramWrite r20 (dst+20#32) (extend .w true (ramRead ram (src+20#32) .w)) .w
  let c21 := c20.goto 0x80002b7e#32
  let r22 := ramWrite r21 (dst+24#32) (alu .add (0#32) 0x00000005#32) .b
  let c22 := c21.goto 0x80002b82#32
  let r23 := ramWrite r22 (dst+32#32) (0#32) .h
  let c23 := c22.goto 0x80002b86#32
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
    have v14 : c2.get 14=(1#32) := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v14,hbr0]
    try simp only [ite_true,ite_false]
    rw [show c2.pc=0x8000299e#32 by rfl,show 0x8000299e#32+0x00000044#32=0x800029e2#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800029e2#32).getLsbD 0=false;decide) ck2147494370 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v14 : c3.get 14=(1#32) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v0 : c3.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_branch,v14,v0,hbr1]
    try simp only [ite_true,ite_false]
    first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800029e4#32).getLsbD 0=false;decide) ck2147494372 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v0 : c4.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_opimm,v0];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800029e6#32).getLsbD 0=false;decide) ck2147494374 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v14 : c5.get 14=(1#32) := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c5.get 13=(alu .add (0#32) 0x00000001#32) := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v14,v13,hbr2]
    try simp only [ite_true,ite_false]
    rw [show c5.pc=0x800029e6#32 by rfl,show 0x800029e6#32+0x000000da#32=0x80002ac0#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ac0#32).getLsbD 0=false;decide) ck2147494592 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v0 : c6.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_opimm,v0];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ac2#32).getLsbD 0=false;decide) ck2147494594 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v12 : c7.get 12=(input) := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c7.get 13=(alu .add (0#32) 0x0000000a#32) := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v12,v13,hbr3]
    try simp only [ite_true,ite_false]
    first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ac6#32).getLsbD 0=false;decide) ck2147494598 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v11 : c8.get 11=(src) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 0 hsa) (Memory.block_access hsm (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ac8#32).getLsbD 0=false;decide) ck2147494600 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v11 : c9.get 11=(src) := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 1 hsa) (Memory.block_access hsm (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80002aca#32).getLsbD 0=false;decide) ck2147494602 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v14 : c10.get 14=(extend .w true (ramRead ram (src+0#32) .w)) := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c10.get 13=(extend .w true (ramRead ram (src+4#32) .w)) := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v14,v13];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ace#32).getLsbD 0=false;decide) ck2147494606 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v12 : c11.get 12=(alu .or (extend .w true (ramRead ram (src+0#32) .w)) (extend .w true (ramRead ram (src+4#32) .w))) := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v0 : c11.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_branch,v12,v0,hbr4]
    try simp only [ite_true,ite_false]
    rw [show c11.pc=0x80002ace#32 by rfl,show 0x80002ace#32+0x0000009a#32=0x80002b68#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x80002b68#32).getLsbD 0=false;decide) ck2147494760 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    have v0 : c12.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_opimm,v0];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine Quiet.step_of (by change (0x80002b6a#32).getLsbD 0=false;decide) ck2147494762 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 ram [],[]⟩
    have v11 : c13.get 11=(src) := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 4 hsa) (Memory.block_access hsm (off := 16) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine Quiet.step_of (by change (0x80002b6c#32).getLsbD 0=false;decide) ck2147494764 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) ram 0 [] [] = ⟨.ok c15 ram [],[]⟩
    have v11 : c14.get 11=(src) := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 5 hsa) (Memory.block_access hsm (off := 20) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,ram⟩ ⟨c16,r16⟩ := by
    refine Quiet.step_of (by change (0x80002b6e#32).getLsbD 0=false;decide) ck2147494766 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) ram 0 [] [] = ⟨.ok c16 r16 [],[]⟩
    have v10 : c15.get 10=(dst) := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v14 : c15.get 14=(extend .w true (ramRead ram (src+0#32) .w)) := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v14,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 0 hda) (Memory.block_access hdm (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,r16⟩ ⟨c17,r17⟩ := by
    refine Quiet.step_of (by change (0x80002b70#32).getLsbD 0=false;decide) ck2147494768 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) r16 0 [] [] = ⟨.ok c17 r17 [],[]⟩
    have v10 : c16.get 10=(dst) := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c16.get 13=(extend .w true (ramRead ram (src+4#32) .w)) := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v13,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 1 hda) (Memory.block_access hdm (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,r17⟩ ⟨c18,r18⟩ := by
    refine Quiet.step_of (by change (0x80002b72#32).getLsbD 0=false;decide) ck2147494770 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) r17 0 [] [] = ⟨.ok c18 r18 [],[]⟩
    have v10 : c17.get 10=(dst) := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v0 : c17.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_store,v10,v0,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 2 hda) (Memory.block_access hdm (off := 8) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,r18⟩ ⟨c19,r19⟩ := by
    refine Quiet.step_of (by change (0x80002b76#32).getLsbD 0=false;decide) ck2147494774 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) r18 0 [] [] = ⟨.ok c19 r19 [],[]⟩
    have v10 : c18.get 10=(dst) := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v0 : c18.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_store,v10,v0,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 3 hda) (Memory.block_access hdm (off := 12) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,r19⟩ ⟨c20,r20⟩ := by
    refine Quiet.step_of (by change (0x80002b7a#32).getLsbD 0=false;decide) ck2147494778 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) r19 0 [] [] = ⟨.ok c20 r20 [],[]⟩
    have v10 : c19.get 10=(dst) := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c19.get 15=(extend .w true (ramRead ram (src+16#32) .w)) := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v15,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 4 hda) (Memory.block_access hdm (off := 16) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,r20⟩ ⟨c21,r21⟩ := by
    refine Quiet.step_of (by change (0x80002b7c#32).getLsbD 0=false;decide) ck2147494780 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) r20 0 [] [] = ⟨.ok c21 r21 [],[]⟩
    have v10 : c20.get 10=(dst) := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c20.get 11=(extend .w true (ramRead ram (src+20#32) .w)) := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v11,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 5 hda) (Memory.block_access hdm (off := 20) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,r21⟩ ⟨c22,r22⟩ := by
    refine Quiet.step_of (by change (0x80002b7e#32).getLsbD 0=false;decide) ck2147494782 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) r21 0 [] [] = ⟨.ok c22 r22 [],[]⟩
    have v10 : c21.get 10=(dst) := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c21.get 12=(alu .add (0#32) 0x00000005#32) := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v12,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hdm (off := 24) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,r22⟩ ⟨c23,r23⟩ := by
    refine Quiet.step_of (by change (0x80002b82#32).getLsbD 0=false;decide) ck2147494786 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) r22 0 [] [] = ⟨.ok c23 r23 [],[]⟩
    have v10 : c22.get 10=(dst) := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v0 : c22.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_store,v10,v0,Quiet.interp_store_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned dst 16 (by omega)) (Memory.block_access hdm (off := 32) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t23 : Quiet.Step B img ⟨c23,r23⟩ ⟨c24,r23⟩ := by
    refine Quiet.step_of (by change (0x80002b86#32).getLsbD 0=false;decide) ck2147494790 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) r23 0 [] [] = ⟨.ok c24 r23 [],[]⟩
    have v1 : c23.get 1=(c.get 1) := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_jalr,v1,BitVec.add_zero]
    change Observed.interp B img o (jump c23 (c.get 1 &&& ~~~1)) r23 0 [] [] = _
    rw [jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨c24,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.single t23))))))))))))))))))))))),rfl,?_,by rfl⟩
  intro reg hr14 hr15 hr13 hr12 hr11
  simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hr14,hr15,hr13,hr12,hr11]
end E5R.Thermostat.ChunkPhase1Zero
