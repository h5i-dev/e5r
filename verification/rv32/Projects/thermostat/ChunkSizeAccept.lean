import Projects.thermostat.ChunkCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ChunkSizeAccept
open E5R E5R.Thermostat

def memory (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (dst+0#32) (extend .w true (ramRead ram (src+0#32) .w)) .w) (dst+4#32) (extend .w true (ramRead ram (src+4#32) .w)) .w) (dst+8#32) (extend .w true (ramRead ram (src+8#32) .w)) .w) (dst+12#32) (extend .w true (ramRead ram (src+12#32) .w)) .w) (dst+16#32) (alu .add (extend .w true (ramRead ram (src+16#32) .w)) (extend .w true (ramRead ram (src+0#32) .w))) .w) (dst+20#32) (alu .add (alu .sltu (alu .add (extend .w true (ramRead ram (src+16#32) .w)) (extend .w true (ramRead ram (src+0#32) .w))) (extend .w true (ramRead ram (src+0#32) .w))) (alu .add (extend .w true (ramRead ram (src+20#32) .w)) (extend .w true (ramRead ram (src+4#32) .w)))) .w) (dst+24#32) (alu .add (0#32) 0x00000001#32) .b) (dst+32#32) (0#32) .h

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word)
    (h10 : c.get 10=dst) (h11 : c.get 11=src) (h12 : c.get 12=input) (h13 : c.get 13=limit)
    (hsm : Memory.Block B src 32) (hdm : Memory.Block B dst 36)
    (hsa : src.toNat%4=0) (hda : dst.toNat%4=0)
    (hphase : ram (src+24#32)=0#8)
    (hbr0 : taken .ge (alu .add (0#32) 0x00000002#32) (0#32)=true)
    (hbr1 : taken .eq (0#32) (0#32)=true)
    (hbr2 : taken .ltu (alu .and (alu .add (input) 0xffffffd0#32) 0x000000ff#32) (alu .add (0#32) 0x0000000a#32)=false)
    (hbr3 : taken .geu (alu .and (alu .add (input) 0xffffff9f#32) 0x000000ff#32) (alu .add (0#32) 0x00000006#32)=true)
    (hbr4 : taken .geu (alu .and (alu .add (input) 0xffffffbf#32) 0x000000ff#32) (alu .add (0#32) 0x00000006#32)=true)
    (hbr5 : taken .ne (input) (alu .add (0#32) 0x0000000d#32)=false)
    (hbr6 : taken .eq (alu .or (extend .w true (ramRead ram (src+8#32) .w)) (extend .w true (ramRead ram (src+12#32) .w))) (0#32)=false)
    (hbr7 : taken .ne (alu .or (alu .sltu (limit) (extend .w true (ramRead ram (src+16#32) .w))) (alu .sltu (0#32) (extend .w true (ramRead ram (src+20#32) .w)))) (0#32)=false)
    (hbr8 : taken .eq (extend .w true (ramRead ram (src+4#32) .w)) (alu .sub (alu .sub (0#32) (extend .w true (ramRead ram (src+20#32) .w))) (alu .sltu (limit) (extend .w true (ramRead ram (src+16#32) .w))))=true)
    (hbr9 : taken .eq (alu .sltu (alu .sub (limit) (extend .w true (ramRead ram (src+16#32) .w))) (extend .w true (ramRead ram (src+0#32) .w))) (0#32)=true)
    (hp : c.pc=0x80002998#32) :
    ∃ d, Quiet.Steps B img 51 ⟨c,ram⟩ ⟨d,memory c ram src dst input limit⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧
      (∀ r : Reg, r≠14 → r≠15 → r≠16 → r≠12 → r≠6 → r≠17 → r≠5 → r≠7 → r≠13 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (0#32) 0x8000299c#32
  let c2 := c1.wr 15 (alu .add (0#32) 0x00000002#32) 0x8000299e#32
  let c3 := c2.goto 0x800029e2#32
  let c4 := c3.goto 0x80002a5a#32
  let c5 := c4.wr 14 (alu .add (input) 0xffffffd0#32) 0x80002a5e#32
  let c6 := c5.wr 15 (alu .and (alu .add (input) 0xffffffd0#32) 0x000000ff#32) 0x80002a62#32
  let c7 := c6.wr 16 (alu .add (0#32) 0x0000000a#32) 0x80002a64#32
  let c8 := c7.goto 0x80002a68#32
  let c9 := c8.wr 14 (alu .add (input) 0xffffff9f#32) 0x80002a6c#32
  let c10 := c9.wr 15 (alu .and (alu .add (input) 0xffffff9f#32) 0x000000ff#32) 0x80002a70#32
  let c11 := c10.wr 14 (alu .add (0#32) 0x00000006#32) 0x80002a72#32
  let c12 := c11.goto 0x80002afa#32
  let c13 := c12.wr 15 (alu .add (input) 0xffffffbf#32) 0x80002afe#32
  let c14 := c13.wr 15 (alu .and (alu .add (input) 0xffffffbf#32) 0x000000ff#32) 0x80002b02#32
  let c15 := c14.goto 0x80002b88#32
  let c16 := c15.wr 14 (alu .add (0#32) 0x0000000d#32) 0x80002b8a#32
  let c17 := c16.goto 0x80002b8e#32
  let c18 := c17.wr 12 (extend .w true (ramRead ram (src+8#32) .w)) 0x80002b90#32
  let c19 := c18.wr 14 (extend .w true (ramRead ram (src+12#32) .w)) 0x80002b92#32
  let c20 := c19.wr 15 (alu .or (extend .w true (ramRead ram (src+8#32) .w)) (extend .w true (ramRead ram (src+12#32) .w))) 0x80002b96#32
  let c21 := c20.goto 0x80002b98#32
  let c22 := c21.wr 16 (extend .w true (ramRead ram (src+16#32) .w)) 0x80002b9c#32
  let c23 := c22.wr 15 (extend .w true (ramRead ram (src+20#32) .w)) 0x80002b9e#32
  let c24 := c23.wr 6 (alu .sltu (limit) (extend .w true (ramRead ram (src+16#32) .w))) 0x80002ba2#32
  let c25 := c24.wr 17 (alu .sltu (0#32) (extend .w true (ramRead ram (src+20#32) .w))) 0x80002ba6#32
  let c26 := c25.wr 17 (alu .or (alu .sltu (limit) (extend .w true (ramRead ram (src+16#32) .w))) (alu .sltu (0#32) (extend .w true (ramRead ram (src+20#32) .w)))) 0x80002baa#32
  let c27 := c26.goto 0x80002bae#32
  let c28 := c27.wr 17 (extend .w true (ramRead ram (src+4#32) .w)) 0x80002bb2#32
  let c29 := c28.wr 5 (extend .w true (ramRead ram (src+0#32) .w)) 0x80002bb6#32
  let c30 := c29.wr 7 (alu .sub (0#32) (extend .w true (ramRead ram (src+20#32) .w))) 0x80002bba#32
  let c31 := c30.wr 6 (alu .sub (alu .sub (0#32) (extend .w true (ramRead ram (src+20#32) .w))) (alu .sltu (limit) (extend .w true (ramRead ram (src+16#32) .w)))) 0x80002bbe#32
  let c32 := c31.goto 0x80002bfe#32
  let c33 := c32.wr 13 (alu .sub (limit) (extend .w true (ramRead ram (src+16#32) .w))) 0x80002c02#32
  let c34 := c33.wr 13 (alu .sltu (alu .sub (limit) (extend .w true (ramRead ram (src+16#32) .w))) (extend .w true (ramRead ram (src+0#32) .w))) 0x80002c06#32
  let c35 := c34.goto 0x80002c2c#32
  let c36 := c35.wr 16 (alu .add (extend .w true (ramRead ram (src+16#32) .w)) (extend .w true (ramRead ram (src+0#32) .w))) 0x80002c2e#32
  let c37 := c36.wr 15 (alu .add (extend .w true (ramRead ram (src+20#32) .w)) (extend .w true (ramRead ram (src+4#32) .w))) 0x80002c30#32
  let c38 := c37.wr 11 (alu .sltu (alu .add (extend .w true (ramRead ram (src+16#32) .w)) (extend .w true (ramRead ram (src+0#32) .w))) (extend .w true (ramRead ram (src+0#32) .w))) 0x80002c34#32
  let c39 := c38.wr 11 (alu .add (alu .sltu (alu .add (extend .w true (ramRead ram (src+16#32) .w)) (extend .w true (ramRead ram (src+0#32) .w))) (extend .w true (ramRead ram (src+0#32) .w))) (alu .add (extend .w true (ramRead ram (src+20#32) .w)) (extend .w true (ramRead ram (src+4#32) .w)))) 0x80002c36#32
  let r40 := ramWrite ram (dst+0#32) (extend .w true (ramRead ram (src+0#32) .w)) .w
  let c40 := c39.goto 0x80002c3a#32
  let r41 := ramWrite r40 (dst+4#32) (extend .w true (ramRead ram (src+4#32) .w)) .w
  let c41 := c40.goto 0x80002c3e#32
  let r42 := ramWrite r41 (dst+8#32) (extend .w true (ramRead ram (src+8#32) .w)) .w
  let c42 := c41.goto 0x80002c40#32
  let r43 := ramWrite r42 (dst+12#32) (extend .w true (ramRead ram (src+12#32) .w)) .w
  let c43 := c42.goto 0x80002c42#32
  let c44 := c43.wr 12 (alu .add (0#32) 0x00000001#32) 0x80002c44#32
  let c45 := c44.goto 0x80002aba#32
  let r46 := ramWrite r43 (dst+16#32) (alu .add (extend .w true (ramRead ram (src+16#32) .w)) (extend .w true (ramRead ram (src+0#32) .w))) .w
  let c46 := c45.goto 0x80002abe#32
  let c47 := c46.goto 0x80002b7c#32
  let r48 := ramWrite r46 (dst+20#32) (alu .add (alu .sltu (alu .add (extend .w true (ramRead ram (src+16#32) .w)) (extend .w true (ramRead ram (src+0#32) .w))) (extend .w true (ramRead ram (src+0#32) .w))) (alu .add (extend .w true (ramRead ram (src+20#32) .w)) (extend .w true (ramRead ram (src+4#32) .w)))) .w
  let c48 := c47.goto 0x80002b7e#32
  let r49 := ramWrite r48 (dst+24#32) (alu .add (0#32) 0x00000001#32) .b
  let c49 := c48.goto 0x80002b82#32
  let r50 := ramWrite r49 (dst+32#32) (0#32) .h
  let c50 := c49.goto 0x80002b86#32
  let c51 := c50.goto (c.get 1 &&& ~~~1)
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
    have v14 : c2.get 14=(0#32) := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v14,hbr0]
    try simp only [ite_true,ite_false]
    rw [show c2.pc=0x8000299e#32 by rfl,show 0x8000299e#32+0x00000044#32=0x800029e2#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800029e2#32).getLsbD 0=false;decide) ck2147494370 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v14 : c3.get 14=(0#32) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v0 : c3.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_branch,v14,v0,hbr1]
    try simp only [ite_true,ite_false]
    rw [show c3.pc=0x800029e2#32 by rfl,show 0x800029e2#32+0x00000078#32=0x80002a5a#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80002a5a#32).getLsbD 0=false;decide) ck2147494490 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v12 : c4.get 12=(input) := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v12];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80002a5e#32).getLsbD 0=false;decide) ck2147494494 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v14 : c5.get 14=(alu .add (input) 0xffffffd0#32) := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v14];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80002a62#32).getLsbD 0=false;decide) ck2147494498 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v0 : c6.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_opimm,v0];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80002a64#32).getLsbD 0=false;decide) ck2147494500 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v15 : c7.get 15=(alu .and (alu .add (input) 0xffffffd0#32) 0x000000ff#32) := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v16 : c7.get 16=(alu .add (0#32) 0x0000000a#32) := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v16,hbr2]
    try simp only [ite_true,ite_false]
    first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80002a68#32).getLsbD 0=false;decide) ck2147494504 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v12 : c8.get 12=(input) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v12];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80002a6c#32).getLsbD 0=false;decide) ck2147494508 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v14 : c9.get 14=(alu .add (input) 0xffffff9f#32) := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v14];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80002a70#32).getLsbD 0=false;decide) ck2147494512 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v0 : c10.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_opimm,v0];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x80002a72#32).getLsbD 0=false;decide) ck2147494514 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v15 : c11.get 15=(alu .and (alu .add (input) 0xffffff9f#32) 0x000000ff#32) := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v14 : c11.get 14=(alu .add (0#32) 0x00000006#32) := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v14,hbr3]
    try simp only [ite_true,ite_false]
    rw [show c11.pc=0x80002a72#32 by rfl,show 0x80002a72#32+0x00000088#32=0x80002afa#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x80002afa#32).getLsbD 0=false;decide) ck2147494650 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    have v12 : c12.get 12=(input) := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v12];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine Quiet.step_of (by change (0x80002afe#32).getLsbD 0=false;decide) ck2147494654 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 ram [],[]⟩
    have v15 : c13.get 15=(alu .add (input) 0xffffffbf#32) := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v15];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine Quiet.step_of (by change (0x80002b02#32).getLsbD 0=false;decide) ck2147494658 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) ram 0 [] [] = ⟨.ok c15 ram [],[]⟩
    have v15 : c14.get 15=(alu .and (alu .add (input) 0xffffffbf#32) 0x000000ff#32) := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v14 : c14.get 14=(alu .add (0#32) 0x00000006#32) := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v14,hbr4]
    try simp only [ite_true,ite_false]
    rw [show c14.pc=0x80002b02#32 by rfl,show 0x80002b02#32+0x00000086#32=0x80002b88#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have t15 : Quiet.Step B img ⟨c15,ram⟩ ⟨c16,ram⟩ := by
    refine Quiet.step_of (by change (0x80002b88#32).getLsbD 0=false;decide) ck2147494792 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) ram 0 [] [] = ⟨.ok c16 ram [],[]⟩
    have v0 : c15.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_opimm,v0];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,ram⟩ ⟨c17,ram⟩ := by
    refine Quiet.step_of (by change (0x80002b8a#32).getLsbD 0=false;decide) ck2147494794 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) ram 0 [] [] = ⟨.ok c17 ram [],[]⟩
    have v12 : c16.get 12=(input) := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v14 : c16.get 14=(alu .add (0#32) 0x0000000d#32) := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v12,v14,hbr5]
    try simp only [ite_true,ite_false]
    first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,ram⟩ ⟨c18,ram⟩ := by
    refine Quiet.step_of (by change (0x80002b8e#32).getLsbD 0=false;decide) ck2147494798 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) ram 0 [] [] = ⟨.ok c18 ram [],[]⟩
    have v11 : c17.get 11=(src) := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 2 hsa) (Memory.block_access hsm (off := 8) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,ram⟩ ⟨c19,ram⟩ := by
    refine Quiet.step_of (by change (0x80002b90#32).getLsbD 0=false;decide) ck2147494800 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) ram 0 [] [] = ⟨.ok c19 ram [],[]⟩
    have v11 : c18.get 11=(src) := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 3 hsa) (Memory.block_access hsm (off := 12) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,ram⟩ ⟨c20,ram⟩ := by
    refine Quiet.step_of (by change (0x80002b92#32).getLsbD 0=false;decide) ck2147494802 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) ram 0 [] [] = ⟨.ok c20 ram [],[]⟩
    have v12 : c19.get 12=(extend .w true (ramRead ram (src+8#32) .w)) := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v14 : c19.get 14=(extend .w true (ramRead ram (src+12#32) .w)) := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v12,v14];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,ram⟩ ⟨c21,ram⟩ := by
    refine Quiet.step_of (by change (0x80002b96#32).getLsbD 0=false;decide) ck2147494806 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) ram 0 [] [] = ⟨.ok c21 ram [],[]⟩
    have v15 : c20.get 15=(alu .or (extend .w true (ramRead ram (src+8#32) .w)) (extend .w true (ramRead ram (src+12#32) .w))) := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v0 : c20.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_branch,v15,v0,hbr6]
    try simp only [ite_true,ite_false]
    first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,ram⟩ ⟨c22,ram⟩ := by
    refine Quiet.step_of (by change (0x80002b98#32).getLsbD 0=false;decide) ck2147494808 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) ram 0 [] [] = ⟨.ok c22 ram [],[]⟩
    have v11 : c21.get 11=(src) := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 4 hsa) (Memory.block_access hsm (off := 16) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,ram⟩ ⟨c23,ram⟩ := by
    refine Quiet.step_of (by change (0x80002b9c#32).getLsbD 0=false;decide) ck2147494812 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) ram 0 [] [] = ⟨.ok c23 ram [],[]⟩
    have v11 : c22.get 11=(src) := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 5 hsa) (Memory.block_access hsm (off := 20) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t23 : Quiet.Step B img ⟨c23,ram⟩ ⟨c24,ram⟩ := by
    refine Quiet.step_of (by change (0x80002b9e#32).getLsbD 0=false;decide) ck2147494814 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) ram 0 [] [] = ⟨.ok c24 ram [],[]⟩
    have v13 : c23.get 13=(limit) := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v16 : c23.get 16=(extend .w true (ramRead ram (src+16#32) .w)) := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v13,v16];first | rfl | (rw [hp];rfl)
  have t24 : Quiet.Step B img ⟨c24,ram⟩ ⟨c25,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ba2#32).getLsbD 0=false;decide) ck2147494818 fun o => ?_
    change Observed.interp B img o (exec c24 _ _) ram 0 [] [] = ⟨.ok c25 ram [],[]⟩
    have v0 : c24.get 0=(0#32) := by exact Core.get_zero _
    have v15 : c24.get 15=(extend .w true (ramRead ram (src+20#32) .w)) := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v0,v15];first | rfl | (rw [hp];rfl)
  have t25 : Quiet.Step B img ⟨c25,ram⟩ ⟨c26,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ba6#32).getLsbD 0=false;decide) ck2147494822 fun o => ?_
    change Observed.interp B img o (exec c25 _ _) ram 0 [] [] = ⟨.ok c26 ram [],[]⟩
    have v6 : c25.get 6=(alu .sltu (limit) (extend .w true (ramRead ram (src+16#32) .w))) := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v17 : c25.get 17=(alu .sltu (0#32) (extend .w true (ramRead ram (src+20#32) .w))) := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v6,v17];first | rfl | (rw [hp];rfl)
  have t26 : Quiet.Step B img ⟨c26,ram⟩ ⟨c27,ram⟩ := by
    refine Quiet.step_of (by change (0x80002baa#32).getLsbD 0=false;decide) ck2147494826 fun o => ?_
    change Observed.interp B img o (exec c26 _ _) ram 0 [] [] = ⟨.ok c27 ram [],[]⟩
    have v17 : c26.get 17=(alu .or (alu .sltu (limit) (extend .w true (ramRead ram (src+16#32) .w))) (alu .sltu (0#32) (extend .w true (ramRead ram (src+20#32) .w)))) := by simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v0 : c26.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_branch,v17,v0,hbr7]
    try simp only [ite_true,ite_false]
    first | rfl | (rw [hp];rfl)
  have t27 : Quiet.Step B img ⟨c27,ram⟩ ⟨c28,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bae#32).getLsbD 0=false;decide) ck2147494830 fun o => ?_
    change Observed.interp B img o (exec c27 _ _) ram 0 [] [] = ⟨.ok c28 ram [],[]⟩
    have v11 : c27.get 11=(src) := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 1 hsa) (Memory.block_access hsm (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t28 : Quiet.Step B img ⟨c28,ram⟩ ⟨c29,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bb2#32).getLsbD 0=false;decide) ck2147494834 fun o => ?_
    change Observed.interp B img o (exec c28 _ _) ram 0 [] [] = ⟨.ok c29 ram [],[]⟩
    have v11 : c28.get 11=(src) := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 0 hsa) (Memory.block_access hsm (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t29 : Quiet.Step B img ⟨c29,ram⟩ ⟨c30,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bb6#32).getLsbD 0=false;decide) ck2147494838 fun o => ?_
    change Observed.interp B img o (exec c29 _ _) ram 0 [] [] = ⟨.ok c30 ram [],[]⟩
    have v0 : c29.get 0=(0#32) := by exact Core.get_zero _
    have v15 : c29.get 15=(extend .w true (ramRead ram (src+20#32) .w)) := by simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v0,v15];first | rfl | (rw [hp];rfl)
  have t30 : Quiet.Step B img ⟨c30,ram⟩ ⟨c31,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bba#32).getLsbD 0=false;decide) ck2147494842 fun o => ?_
    change Observed.interp B img o (exec c30 _ _) ram 0 [] [] = ⟨.ok c31 ram [],[]⟩
    have v7 : c30.get 7=(alu .sub (0#32) (extend .w true (ramRead ram (src+20#32) .w))) := by simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v6 : c30.get 6=(alu .sltu (limit) (extend .w true (ramRead ram (src+16#32) .w))) := by simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v7,v6];first | rfl | (rw [hp];rfl)
  have t31 : Quiet.Step B img ⟨c31,ram⟩ ⟨c32,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bbe#32).getLsbD 0=false;decide) ck2147494846 fun o => ?_
    change Observed.interp B img o (exec c31 _ _) ram 0 [] [] = ⟨.ok c32 ram [],[]⟩
    have v17 : c31.get 17=(extend .w true (ramRead ram (src+4#32) .w)) := by simp [c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v6 : c31.get 6=(alu .sub (alu .sub (0#32) (extend .w true (ramRead ram (src+20#32) .w))) (alu .sltu (limit) (extend .w true (ramRead ram (src+16#32) .w)))) := by simp [c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v17,v6,hbr8]
    try simp only [ite_true,ite_false]
    rw [show c31.pc=0x80002bbe#32 by rfl,show 0x80002bbe#32+0x00000040#32=0x80002bfe#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have t32 : Quiet.Step B img ⟨c32,ram⟩ ⟨c33,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bfe#32).getLsbD 0=false;decide) ck2147494910 fun o => ?_
    change Observed.interp B img o (exec c32 _ _) ram 0 [] [] = ⟨.ok c33 ram [],[]⟩
    have v13 : c32.get 13=(limit) := by simp [c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v16 : c32.get 16=(extend .w true (ramRead ram (src+16#32) .w)) := by simp [c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v13,v16];first | rfl | (rw [hp];rfl)
  have t33 : Quiet.Step B img ⟨c33,ram⟩ ⟨c34,ram⟩ := by
    refine Quiet.step_of (by change (0x80002c02#32).getLsbD 0=false;decide) ck2147494914 fun o => ?_
    change Observed.interp B img o (exec c33 _ _) ram 0 [] [] = ⟨.ok c34 ram [],[]⟩
    have v13 : c33.get 13=(alu .sub (limit) (extend .w true (ramRead ram (src+16#32) .w))) := by simp [c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v5 : c33.get 5=(extend .w true (ramRead ram (src+0#32) .w)) := by simp [c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v13,v5];first | rfl | (rw [hp];rfl)
  have t34 : Quiet.Step B img ⟨c34,ram⟩ ⟨c35,ram⟩ := by
    refine Quiet.step_of (by change (0x80002c06#32).getLsbD 0=false;decide) ck2147494918 fun o => ?_
    change Observed.interp B img o (exec c34 _ _) ram 0 [] [] = ⟨.ok c35 ram [],[]⟩
    have v13 : c34.get 13=(alu .sltu (alu .sub (limit) (extend .w true (ramRead ram (src+16#32) .w))) (extend .w true (ramRead ram (src+0#32) .w))) := by simp [c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v0 : c34.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_branch,v13,v0,hbr9]
    try simp only [ite_true,ite_false]
    rw [show c34.pc=0x80002c06#32 by rfl,show 0x80002c06#32+0x00000026#32=0x80002c2c#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have t35 : Quiet.Step B img ⟨c35,ram⟩ ⟨c36,ram⟩ := by
    refine Quiet.step_of (by change (0x80002c2c#32).getLsbD 0=false;decide) ck2147494956 fun o => ?_
    change Observed.interp B img o (exec c35 _ _) ram 0 [] [] = ⟨.ok c36 ram [],[]⟩
    have v16 : c35.get 16=(extend .w true (ramRead ram (src+16#32) .w)) := by simp [c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v5 : c35.get 5=(extend .w true (ramRead ram (src+0#32) .w)) := by simp [c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v16,v5];first | rfl | (rw [hp];rfl)
  have t36 : Quiet.Step B img ⟨c36,ram⟩ ⟨c37,ram⟩ := by
    refine Quiet.step_of (by change (0x80002c2e#32).getLsbD 0=false;decide) ck2147494958 fun o => ?_
    change Observed.interp B img o (exec c36 _ _) ram 0 [] [] = ⟨.ok c37 ram [],[]⟩
    have v15 : c36.get 15=(extend .w true (ramRead ram (src+20#32) .w)) := by simp [c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v17 : c36.get 17=(extend .w true (ramRead ram (src+4#32) .w)) := by simp [c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v15,v17];first | rfl | (rw [hp];rfl)
  have t37 : Quiet.Step B img ⟨c37,ram⟩ ⟨c38,ram⟩ := by
    refine Quiet.step_of (by change (0x80002c30#32).getLsbD 0=false;decide) ck2147494960 fun o => ?_
    change Observed.interp B img o (exec c37 _ _) ram 0 [] [] = ⟨.ok c38 ram [],[]⟩
    have v16 : c37.get 16=(alu .add (extend .w true (ramRead ram (src+16#32) .w)) (extend .w true (ramRead ram (src+0#32) .w))) := by simp [c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v5 : c37.get 5=(extend .w true (ramRead ram (src+0#32) .w)) := by simp [c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v16,v5];first | rfl | (rw [hp];rfl)
  have t38 : Quiet.Step B img ⟨c38,ram⟩ ⟨c39,ram⟩ := by
    refine Quiet.step_of (by change (0x80002c34#32).getLsbD 0=false;decide) ck2147494964 fun o => ?_
    change Observed.interp B img o (exec c38 _ _) ram 0 [] [] = ⟨.ok c39 ram [],[]⟩
    have v11 : c38.get 11=(alu .sltu (alu .add (extend .w true (ramRead ram (src+16#32) .w)) (extend .w true (ramRead ram (src+0#32) .w))) (extend .w true (ramRead ram (src+0#32) .w))) := by simp [c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c38.get 15=(alu .add (extend .w true (ramRead ram (src+20#32) .w)) (extend .w true (ramRead ram (src+4#32) .w))) := by simp [c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v11,v15];first | rfl | (rw [hp];rfl)
  have t39 : Quiet.Step B img ⟨c39,ram⟩ ⟨c40,r40⟩ := by
    refine Quiet.step_of (by change (0x80002c36#32).getLsbD 0=false;decide) ck2147494966 fun o => ?_
    change Observed.interp B img o (exec c39 _ _) ram 0 [] [] = ⟨.ok c40 r40 [],[]⟩
    have v10 : c39.get 10=(dst) := by simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v5 : c39.get 5=(extend .w true (ramRead ram (src+0#32) .w)) := by simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v5,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 0 hda) (Memory.block_access hdm (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t40 : Quiet.Step B img ⟨c40,r40⟩ ⟨c41,r41⟩ := by
    refine Quiet.step_of (by change (0x80002c3a#32).getLsbD 0=false;decide) ck2147494970 fun o => ?_
    change Observed.interp B img o (exec c40 _ _) r40 0 [] [] = ⟨.ok c41 r41 [],[]⟩
    have v10 : c40.get 10=(dst) := by simp [c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v17 : c40.get 17=(extend .w true (ramRead ram (src+4#32) .w)) := by simp [c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v17,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 1 hda) (Memory.block_access hdm (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t41 : Quiet.Step B img ⟨c41,r41⟩ ⟨c42,r42⟩ := by
    refine Quiet.step_of (by change (0x80002c3e#32).getLsbD 0=false;decide) ck2147494974 fun o => ?_
    change Observed.interp B img o (exec c41 _ _) r41 0 [] [] = ⟨.ok c42 r42 [],[]⟩
    have v10 : c41.get 10=(dst) := by simp [c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c41.get 12=(extend .w true (ramRead ram (src+8#32) .w)) := by simp [c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v12,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 2 hda) (Memory.block_access hdm (off := 8) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t42 : Quiet.Step B img ⟨c42,r42⟩ ⟨c43,r43⟩ := by
    refine Quiet.step_of (by change (0x80002c40#32).getLsbD 0=false;decide) ck2147494976 fun o => ?_
    change Observed.interp B img o (exec c42 _ _) r42 0 [] [] = ⟨.ok c43 r43 [],[]⟩
    have v10 : c42.get 10=(dst) := by simp [c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v14 : c42.get 14=(extend .w true (ramRead ram (src+12#32) .w)) := by simp [c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v14,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 3 hda) (Memory.block_access hdm (off := 12) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t43 : Quiet.Step B img ⟨c43,r43⟩ ⟨c44,r43⟩ := by
    refine Quiet.step_of (by change (0x80002c42#32).getLsbD 0=false;decide) ck2147494978 fun o => ?_
    change Observed.interp B img o (exec c43 _ _) r43 0 [] [] = ⟨.ok c44 r43 [],[]⟩
    have v0 : c43.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_opimm,v0];first | rfl | (rw [hp];rfl)
  have t44 : Quiet.Step B img ⟨c44,r43⟩ ⟨c45,r43⟩ := by
    refine Quiet.step_of (by change (0x80002c44#32).getLsbD 0=false;decide) ck2147494980 fun o => ?_
    change Observed.interp B img o (exec c44 _ _) r43 0 [] [] = ⟨.ok c45 r43 [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c44 (c44.pc+0xfffffe76#32)) r43 0 [] [] = _
    rw [show c44.pc=0x80002c44#32 by rfl,show 0x80002c44#32+0xfffffe76#32=0x80002aba#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have t45 : Quiet.Step B img ⟨c45,r43⟩ ⟨c46,r46⟩ := by
    refine Quiet.step_of (by change (0x80002aba#32).getLsbD 0=false;decide) ck2147494586 fun o => ?_
    change Observed.interp B img o (exec c45 _ _) r43 0 [] [] = ⟨.ok c46 r46 [],[]⟩
    have v10 : c45.get 10=(dst) := by simp [c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v16 : c45.get 16=(alu .add (extend .w true (ramRead ram (src+16#32) .w)) (extend .w true (ramRead ram (src+0#32) .w))) := by simp [c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v16,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 4 hda) (Memory.block_access hdm (off := 16) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t46 : Quiet.Step B img ⟨c46,r46⟩ ⟨c47,r46⟩ := by
    refine Quiet.step_of (by change (0x80002abe#32).getLsbD 0=false;decide) ck2147494590 fun o => ?_
    change Observed.interp B img o (exec c46 _ _) r46 0 [] [] = ⟨.ok c47 r46 [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c46 (c46.pc+0x000000be#32)) r46 0 [] [] = _
    rw [show c46.pc=0x80002abe#32 by rfl,show 0x80002abe#32+0x000000be#32=0x80002b7c#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have t47 : Quiet.Step B img ⟨c47,r46⟩ ⟨c48,r48⟩ := by
    refine Quiet.step_of (by change (0x80002b7c#32).getLsbD 0=false;decide) ck2147494780 fun o => ?_
    change Observed.interp B img o (exec c47 _ _) r46 0 [] [] = ⟨.ok c48 r48 [],[]⟩
    have v10 : c47.get 10=(dst) := by simp [c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c47.get 11=(alu .add (alu .sltu (alu .add (extend .w true (ramRead ram (src+16#32) .w)) (extend .w true (ramRead ram (src+0#32) .w))) (extend .w true (ramRead ram (src+0#32) .w))) (alu .add (extend .w true (ramRead ram (src+20#32) .w)) (extend .w true (ramRead ram (src+4#32) .w)))) := by simp [c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v11,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 5 hda) (Memory.block_access hdm (off := 20) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t48 : Quiet.Step B img ⟨c48,r48⟩ ⟨c49,r49⟩ := by
    refine Quiet.step_of (by change (0x80002b7e#32).getLsbD 0=false;decide) ck2147494782 fun o => ?_
    change Observed.interp B img o (exec c48 _ _) r48 0 [] [] = ⟨.ok c49 r49 [],[]⟩
    have v10 : c48.get 10=(dst) := by simp [c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c48.get 12=(alu .add (0#32) 0x00000001#32) := by simp [c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v12,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hdm (off := 24) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t49 : Quiet.Step B img ⟨c49,r49⟩ ⟨c50,r50⟩ := by
    refine Quiet.step_of (by change (0x80002b82#32).getLsbD 0=false;decide) ck2147494786 fun o => ?_
    change Observed.interp B img o (exec c49 _ _) r49 0 [] [] = ⟨.ok c50 r50 [],[]⟩
    have v10 : c49.get 10=(dst) := by simp [c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v0 : c49.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_store,v10,v0,Quiet.interp_store_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned dst 16 (by omega)) (Memory.block_access hdm (off := 32) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t50 : Quiet.Step B img ⟨c50,r50⟩ ⟨c51,r50⟩ := by
    refine Quiet.step_of (by change (0x80002b86#32).getLsbD 0=false;decide) ck2147494790 fun o => ?_
    change Observed.interp B img o (exec c50 _ _) r50 0 [] [] = ⟨.ok c51 r50 [],[]⟩
    have v1 : c50.get 1=(c.get 1) := by simp [c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_jalr,v1,BitVec.add_zero]
    change Observed.interp B img o (jump c50 (c.get 1 &&& ~~~1)) r50 0 [] [] = _
    rw [jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨c51,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.step t23 (.step t24 (.step t25 (.step t26 (.step t27 (.step t28 (.step t29 (.step t30 (.step t31 (.step t32 (.step t33 (.step t34 (.step t35 (.step t36 (.step t37 (.step t38 (.step t39 (.step t40 (.step t41 (.step t42 (.step t43 (.step t44 (.step t45 (.step t46 (.step t47 (.step t48 (.step t49 (.single t50)))))))))))))))))))))))))))))))))))))))))))))))))),rfl,?_,by rfl⟩
  intro reg hr14 hr15 hr16 hr12 hr6 hr17 hr5 hr7 hr13 hr11
  simp [c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hr14,hr15,hr16,hr12,hr6,hr17,hr5,hr7,hr13,hr11]
end E5R.Thermostat.ChunkSizeAccept
