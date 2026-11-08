import Projects.thermostat.ChunkCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ChunkHexUpperDigitsReject
open E5R E5R.Thermostat

def memory (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (dst+16#32) (extend .w true (ramRead ram (src+16#32) .w)) .w) (dst+20#32) (extend .w true (ramRead ram (src+20#32) .w)) .w) (dst+24#32) (extend .w true (ramRead ram (src+24#32) .w)) .w) (dst+28#32) (extend .w true (ramRead ram (src+28#32) .w)) .w) (dst+0#32) (extend .w true (ramRead ram (src+0#32) .w)) .w) (dst+4#32) (extend .w true (ramRead ram (src+4#32) .w)) .w) (dst+8#32) (extend .w true (ramRead ram (src+8#32) .w)) .w) (dst+12#32) (extend .w true (ramRead ram (src+12#32) .w)) .w) (dst+32#32) (alu .add (0x01900000#32) 0x00000003#32) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst input limit : Word)
    (h10 : c.get 10=dst) (h11 : c.get 11=src) (h12 : c.get 12=input) (h13 : c.get 13=limit)
    (hsm : Memory.Block B src 32) (hdm : Memory.Block B dst 36)
    (hsa : src.toNat%4=0) (hda : dst.toNat%4=0)
    (hphase : ram (src+24#32)=0#8)
    (hbr0 : taken .ge (alu .add (0#32) 0x00000002#32) (0#32)=true)
    (hbr1 : taken .eq (0#32) (0#32)=true)
    (hbr2 : taken .ltu (alu .and (alu .add (input) 0xffffffd0#32) 0x000000ff#32) (alu .add (0#32) 0x0000000a#32)=false)
    (hbr3 : taken .geu (alu .and (alu .add (input) 0xffffff9f#32) 0x000000ff#32) (alu .add (0#32) 0x00000006#32)=true)
    (hbr4 : taken .geu (alu .and (alu .add (input) 0xffffffbf#32) 0x000000ff#32) (alu .add (0#32) 0x00000006#32)=false)
    (hbr5 : taken .eq (alu .and (alu .sltu (extend .w true (ramRead ram (src+12#32) .w)) 0x00000001#32) (alu .sltu (extend .w true (ramRead ram (src+8#32) .w)) 0x00000008#32)) (0#32)=true)
    (hp : c.pc=0x80002998#32) :
    ∃ d, Quiet.Steps B img 42 ⟨c,ram⟩ ⟨d,memory c ram src dst input limit⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧
      (∀ r : Reg, r≠14 → r≠15 → r≠16 → r≠13 → r≠12 → r≠17 → r≠5 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
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
  let c15 := c14.goto 0x80002b06#32
  let c16 := c15.wr 14 (alu .add (input) 0xffffffc9#32) 0x80002b0a#32
  let c17 := c16.wr 13 (extend .w true (ramRead ram (src+8#32) .w)) 0x80002b0c#32
  let c18 := c17.wr 12 (extend .w true (ramRead ram (src+12#32) .w)) 0x80002b0e#32
  let c19 := c18.wr 15 (alu .sltu (extend .w true (ramRead ram (src+12#32) .w)) 0x00000001#32) 0x80002b12#32
  let c20 := c19.wr 16 (alu .sltu (extend .w true (ramRead ram (src+8#32) .w)) 0x00000008#32) 0x80002b16#32
  let c21 := c20.wr 15 (alu .and (alu .sltu (extend .w true (ramRead ram (src+12#32) .w)) 0x00000001#32) (alu .sltu (extend .w true (ramRead ram (src+8#32) .w)) 0x00000008#32)) 0x80002b1a#32
  let c22 := c21.goto 0x80002bc8#32
  let c23 := c22.wr 12 (extend .w true (ramRead ram (src+16#32) .w)) 0x80002bca#32
  let c24 := c23.wr 13 (extend .w true (ramRead ram (src+20#32) .w)) 0x80002bcc#32
  let c25 := c24.wr 14 (extend .w true (ramRead ram (src+24#32) .w)) 0x80002bce#32
  let c26 := c25.wr 15 (extend .w true (ramRead ram (src+28#32) .w)) 0x80002bd0#32
  let c27 := c26.wr 16 (extend .w true (ramRead ram (src+0#32) .w)) 0x80002bd4#32
  let c28 := c27.wr 17 (extend .w true (ramRead ram (src+4#32) .w)) 0x80002bd8#32
  let c29 := c28.wr 5 (extend .w true (ramRead ram (src+8#32) .w)) 0x80002bdc#32
  let c30 := c29.wr 11 (extend .w true (ramRead ram (src+12#32) .w)) 0x80002bde#32
  let r31 := ramWrite ram (dst+16#32) (extend .w true (ramRead ram (src+16#32) .w)) .w
  let c31 := c30.goto 0x80002be0#32
  let r32 := ramWrite r31 (dst+20#32) (extend .w true (ramRead ram (src+20#32) .w)) .w
  let c32 := c31.goto 0x80002be2#32
  let r33 := ramWrite r32 (dst+24#32) (extend .w true (ramRead ram (src+24#32) .w)) .w
  let c33 := c32.goto 0x80002be4#32
  let r34 := ramWrite r33 (dst+28#32) (extend .w true (ramRead ram (src+28#32) .w)) .w
  let c34 := c33.goto 0x80002be6#32
  let c35 := c34.wr 12 (0x01900000#32) 0x80002bea#32
  let c36 := c35.wr 12 (alu .add (0x01900000#32) 0x00000003#32) 0x80002bec#32
  let r37 := ramWrite r34 (dst+0#32) (extend .w true (ramRead ram (src+0#32) .w)) .w
  let c37 := c36.goto 0x80002bf0#32
  let r38 := ramWrite r37 (dst+4#32) (extend .w true (ramRead ram (src+4#32) .w)) .w
  let c38 := c37.goto 0x80002bf4#32
  let r39 := ramWrite r38 (dst+8#32) (extend .w true (ramRead ram (src+8#32) .w)) .w
  let c39 := c38.goto 0x80002bf8#32
  let r40 := ramWrite r39 (dst+12#32) (extend .w true (ramRead ram (src+12#32) .w)) .w
  let c40 := c39.goto 0x80002bfa#32
  let r41 := ramWrite r40 (dst+32#32) (alu .add (0x01900000#32) 0x00000003#32) .w
  let c41 := c40.goto 0x80002bfc#32
  let c42 := c41.goto (c.get 1 &&& ~~~1)
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
    first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,ram⟩ ⟨c16,ram⟩ := by
    refine Quiet.step_of (by change (0x80002b06#32).getLsbD 0=false;decide) ck2147494662 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) ram 0 [] [] = ⟨.ok c16 ram [],[]⟩
    have v12 : c15.get 12=(input) := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v12];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,ram⟩ ⟨c17,ram⟩ := by
    refine Quiet.step_of (by change (0x80002b0a#32).getLsbD 0=false;decide) ck2147494666 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) ram 0 [] [] = ⟨.ok c17 ram [],[]⟩
    have v11 : c16.get 11=(src) := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 2 hsa) (Memory.block_access hsm (off := 8) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,ram⟩ ⟨c18,ram⟩ := by
    refine Quiet.step_of (by change (0x80002b0c#32).getLsbD 0=false;decide) ck2147494668 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) ram 0 [] [] = ⟨.ok c18 ram [],[]⟩
    have v11 : c17.get 11=(src) := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 3 hsa) (Memory.block_access hsm (off := 12) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,ram⟩ ⟨c19,ram⟩ := by
    refine Quiet.step_of (by change (0x80002b0e#32).getLsbD 0=false;decide) ck2147494670 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) ram 0 [] [] = ⟨.ok c19 ram [],[]⟩
    have v12 : c18.get 12=(extend .w true (ramRead ram (src+12#32) .w)) := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v12];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,ram⟩ ⟨c20,ram⟩ := by
    refine Quiet.step_of (by change (0x80002b12#32).getLsbD 0=false;decide) ck2147494674 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) ram 0 [] [] = ⟨.ok c20 ram [],[]⟩
    have v13 : c19.get 13=(extend .w true (ramRead ram (src+8#32) .w)) := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v13];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,ram⟩ ⟨c21,ram⟩ := by
    refine Quiet.step_of (by change (0x80002b16#32).getLsbD 0=false;decide) ck2147494678 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) ram 0 [] [] = ⟨.ok c21 ram [],[]⟩
    have v15 : c20.get 15=(alu .sltu (extend .w true (ramRead ram (src+12#32) .w)) 0x00000001#32) := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v16 : c20.get 16=(alu .sltu (extend .w true (ramRead ram (src+8#32) .w)) 0x00000008#32) := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,v15,v16];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,ram⟩ ⟨c22,ram⟩ := by
    refine Quiet.step_of (by change (0x80002b1a#32).getLsbD 0=false;decide) ck2147494682 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) ram 0 [] [] = ⟨.ok c22 ram [],[]⟩
    have v15 : c21.get 15=(alu .and (alu .sltu (extend .w true (ramRead ram (src+12#32) .w)) 0x00000001#32) (alu .sltu (extend .w true (ramRead ram (src+8#32) .w)) 0x00000008#32)) := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v0 : c21.get 0=(0#32) := by exact Core.get_zero _
    rw [exec_branch,v15,v0,hbr5]
    try simp only [ite_true,ite_false]
    rw [show c21.pc=0x80002b1a#32 by rfl,show 0x80002b1a#32+0x000000ae#32=0x80002bc8#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have t22 : Quiet.Step B img ⟨c22,ram⟩ ⟨c23,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bc8#32).getLsbD 0=false;decide) ck2147494856 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) ram 0 [] [] = ⟨.ok c23 ram [],[]⟩
    have v11 : c22.get 11=(src) := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 4 hsa) (Memory.block_access hsm (off := 16) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t23 : Quiet.Step B img ⟨c23,ram⟩ ⟨c24,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bca#32).getLsbD 0=false;decide) ck2147494858 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) ram 0 [] [] = ⟨.ok c24 ram [],[]⟩
    have v11 : c23.get 11=(src) := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 5 hsa) (Memory.block_access hsm (off := 20) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t24 : Quiet.Step B img ⟨c24,ram⟩ ⟨c25,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bcc#32).getLsbD 0=false;decide) ck2147494860 fun o => ?_
    change Observed.interp B img o (exec c24 _ _) ram 0 [] [] = ⟨.ok c25 ram [],[]⟩
    have v11 : c24.get 11=(src) := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 6 hsa) (Memory.block_access hsm (off := 24) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t25 : Quiet.Step B img ⟨c25,ram⟩ ⟨c26,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bce#32).getLsbD 0=false;decide) ck2147494862 fun o => ?_
    change Observed.interp B img o (exec c25 _ _) ram 0 [] [] = ⟨.ok c26 ram [],[]⟩
    have v11 : c25.get 11=(src) := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 7 hsa) (Memory.block_access hsm (off := 28) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t26 : Quiet.Step B img ⟨c26,ram⟩ ⟨c27,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bd0#32).getLsbD 0=false;decide) ck2147494864 fun o => ?_
    change Observed.interp B img o (exec c26 _ _) ram 0 [] [] = ⟨.ok c27 ram [],[]⟩
    have v11 : c26.get 11=(src) := by simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 0 hsa) (Memory.block_access hsm (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t27 : Quiet.Step B img ⟨c27,ram⟩ ⟨c28,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bd4#32).getLsbD 0=false;decide) ck2147494868 fun o => ?_
    change Observed.interp B img o (exec c27 _ _) ram 0 [] [] = ⟨.ok c28 ram [],[]⟩
    have v11 : c27.get 11=(src) := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 1 hsa) (Memory.block_access hsm (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t28 : Quiet.Step B img ⟨c28,ram⟩ ⟨c29,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bd8#32).getLsbD 0=false;decide) ck2147494872 fun o => ?_
    change Observed.interp B img o (exec c28 _ _) ram 0 [] [] = ⟨.ok c29 ram [],[]⟩
    have v11 : c28.get 11=(src) := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 2 hsa) (Memory.block_access hsm (off := 8) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t29 : Quiet.Step B img ⟨c29,ram⟩ ⟨c30,ram⟩ := by
    refine Quiet.step_of (by change (0x80002bdc#32).getLsbD 0=false;decide) ck2147494876 fun o => ?_
    change Observed.interp B img o (exec c29 _ _) ram 0 [] [] = ⟨.ok c30 ram [],[]⟩
    have v11 : c29.get 11=(src) := by simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned src 3 hsa) (Memory.block_access hsm (off := 12) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t30 : Quiet.Step B img ⟨c30,ram⟩ ⟨c31,r31⟩ := by
    refine Quiet.step_of (by change (0x80002bde#32).getLsbD 0=false;decide) ck2147494878 fun o => ?_
    change Observed.interp B img o (exec c30 _ _) ram 0 [] [] = ⟨.ok c31 r31 [],[]⟩
    have v10 : c30.get 10=(dst) := by simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c30.get 12=(extend .w true (ramRead ram (src+16#32) .w)) := by simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v12,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 4 hda) (Memory.block_access hdm (off := 16) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t31 : Quiet.Step B img ⟨c31,r31⟩ ⟨c32,r32⟩ := by
    refine Quiet.step_of (by change (0x80002be0#32).getLsbD 0=false;decide) ck2147494880 fun o => ?_
    change Observed.interp B img o (exec c31 _ _) r31 0 [] [] = ⟨.ok c32 r32 [],[]⟩
    have v10 : c31.get 10=(dst) := by simp [c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c31.get 13=(extend .w true (ramRead ram (src+20#32) .w)) := by simp [c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v13,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 5 hda) (Memory.block_access hdm (off := 20) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t32 : Quiet.Step B img ⟨c32,r32⟩ ⟨c33,r33⟩ := by
    refine Quiet.step_of (by change (0x80002be2#32).getLsbD 0=false;decide) ck2147494882 fun o => ?_
    change Observed.interp B img o (exec c32 _ _) r32 0 [] [] = ⟨.ok c33 r33 [],[]⟩
    have v10 : c32.get 10=(dst) := by simp [c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v14 : c32.get 14=(extend .w true (ramRead ram (src+24#32) .w)) := by simp [c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v14,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 6 hda) (Memory.block_access hdm (off := 24) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t33 : Quiet.Step B img ⟨c33,r33⟩ ⟨c34,r34⟩ := by
    refine Quiet.step_of (by change (0x80002be4#32).getLsbD 0=false;decide) ck2147494884 fun o => ?_
    change Observed.interp B img o (exec c33 _ _) r33 0 [] [] = ⟨.ok c34 r34 [],[]⟩
    have v10 : c33.get 10=(dst) := by simp [c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c33.get 15=(extend .w true (ramRead ram (src+28#32) .w)) := by simp [c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v15,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 7 hda) (Memory.block_access hdm (off := 28) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t34 : Quiet.Step B img ⟨c34,r34⟩ ⟨c35,r34⟩ := by
    refine Quiet.step_of (by change (0x80002be6#32).getLsbD 0=false;decide) ck2147494886 fun o => ?_
    change Observed.interp B img o (exec c34 _ _) r34 0 [] [] = ⟨.ok c35 r34 [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t35 : Quiet.Step B img ⟨c35,r34⟩ ⟨c36,r34⟩ := by
    refine Quiet.step_of (by change (0x80002bea#32).getLsbD 0=false;decide) ck2147494890 fun o => ?_
    change Observed.interp B img o (exec c35 _ _) r34 0 [] [] = ⟨.ok c36 r34 [],[]⟩
    have v12 : c35.get 12=(0x01900000#32) := by simp [c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_opimm,v12];first | rfl | (rw [hp];rfl)
  have t36 : Quiet.Step B img ⟨c36,r34⟩ ⟨c37,r37⟩ := by
    refine Quiet.step_of (by change (0x80002bec#32).getLsbD 0=false;decide) ck2147494892 fun o => ?_
    change Observed.interp B img o (exec c36 _ _) r34 0 [] [] = ⟨.ok c37 r37 [],[]⟩
    have v10 : c36.get 10=(dst) := by simp [c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v16 : c36.get 16=(extend .w true (ramRead ram (src+0#32) .w)) := by simp [c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v16,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 0 hda) (Memory.block_access hdm (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t37 : Quiet.Step B img ⟨c37,r37⟩ ⟨c38,r38⟩ := by
    refine Quiet.step_of (by change (0x80002bf0#32).getLsbD 0=false;decide) ck2147494896 fun o => ?_
    change Observed.interp B img o (exec c37 _ _) r37 0 [] [] = ⟨.ok c38 r38 [],[]⟩
    have v10 : c37.get 10=(dst) := by simp [c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v17 : c37.get 17=(extend .w true (ramRead ram (src+4#32) .w)) := by simp [c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v17,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 1 hda) (Memory.block_access hdm (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t38 : Quiet.Step B img ⟨c38,r38⟩ ⟨c39,r39⟩ := by
    refine Quiet.step_of (by change (0x80002bf4#32).getLsbD 0=false;decide) ck2147494900 fun o => ?_
    change Observed.interp B img o (exec c38 _ _) r38 0 [] [] = ⟨.ok c39 r39 [],[]⟩
    have v10 : c38.get 10=(dst) := by simp [c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v5 : c38.get 5=(extend .w true (ramRead ram (src+8#32) .w)) := by simp [c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v5,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 2 hda) (Memory.block_access hdm (off := 8) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t39 : Quiet.Step B img ⟨c39,r39⟩ ⟨c40,r40⟩ := by
    refine Quiet.step_of (by change (0x80002bf8#32).getLsbD 0=false;decide) ck2147494904 fun o => ?_
    change Observed.interp B img o (exec c39 _ _) r39 0 [] [] = ⟨.ok c40 r40 [],[]⟩
    have v10 : c39.get 10=(dst) := by simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v11 : c39.get 11=(extend .w true (ramRead ram (src+12#32) .w)) := by simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v11,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 3 hda) (Memory.block_access hdm (off := 12) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t40 : Quiet.Step B img ⟨c40,r40⟩ ⟨c41,r41⟩ := by
    refine Quiet.step_of (by change (0x80002bfa#32).getLsbD 0=false;decide) ck2147494906 fun o => ?_
    change Observed.interp B img o (exec c40 _ _) r40 0 [] [] = ⟨.ok c41 r41 [],[]⟩
    have v10 : c40.get 10=(dst) := by simp [c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v12 : c40.get 12=(alu .add (0x01900000#32) 0x00000003#32) := by simp [c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_store,v10,v12,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned dst 8 hda) (Memory.block_access hdm (off := 32) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t41 : Quiet.Step B img ⟨c41,r41⟩ ⟨c42,r41⟩ := by
    refine Quiet.step_of (by change (0x80002bfc#32).getLsbD 0=false;decide) ck2147494908 fun o => ?_
    change Observed.interp B img o (exec c41 _ _) r41 0 [] [] = ⟨.ok c42 r41 [],[]⟩
    have v1 : c41.get 1=(c.get 1) := by simp [c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_jalr,v1,BitVec.add_zero]
    change Observed.interp B img o (jump c41 (c.get 1 &&& ~~~1)) r41 0 [] [] = _
    rw [jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨c42,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.step t23 (.step t24 (.step t25 (.step t26 (.step t27 (.step t28 (.step t29 (.step t30 (.step t31 (.step t32 (.step t33 (.step t34 (.step t35 (.step t36 (.step t37 (.step t38 (.step t39 (.step t40 (.single t41))))))))))))))))))))))))))))))))))))))))),rfl,?_,by rfl⟩
  intro reg hr14 hr15 hr16 hr13 hr12 hr17 hr5 hr11
  simp [c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hr14,hr15,hr16,hr13,hr12,hr17,hr5,hr11]
end E5R.Thermostat.ChunkHexUpperDigitsReject
