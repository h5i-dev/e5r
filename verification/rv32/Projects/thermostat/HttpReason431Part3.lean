import Projects.thermostat.HttpReasonCode
import Projects.thermostat.QuietRam
import Projects.thermostat.ObservedByte
import Projects.thermostat.PackedData
import Projects.thermostat.UartPlatform
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HttpReason431Part3
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def memory (ram : Word → BitVec 8) (dst : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (dst+27#32) (32#32) .b) (dst+28#32) (70#32) .b) (dst+29#32) (105#32) .b) (dst+30#32) (101#32) .b) (dst+31#32) (108#32) .b) (dst+32#32) (100#32) .b

theorem contract (c : Core) (ram : Word → BitVec 8) (dst : Word) (h10 : c.get 10=(dst+44#32)) (h11 : c.get 11=2147507450#32) (h12 : c.get 12=13#32) (h13 : c.get 13=32#32) (h14 : c.get 14=(dst+27#32)) (h15 : c.get 15=431#32) (hm : Memory.Block B dst 192)
    (hp : c.pc=0x80003e3a#32) :
    ∃ d, Quiet.Steps B img 30 ⟨c,ram⟩ ⟨d,memory ram dst⟩ ∧ d.pc=0x80003e3a#32 ∧
      d.get 14=(dst+33#32) ∧ d.get 11=2147507456#32 ∧ d.get 13=115#32 ∧ (∀ r : Reg, r≠14 → r≠11 → r≠13 → d.get r=c.get r) ∧ d.sameCsr c := by
  let r1 := ramWrite ram (dst+27#32) (32#32) .b
  let c1 := c.goto 0x80003e3e#32
  let c2 := c1.wr 14 ((dst+28#32)) 0x80003e40#32
  let c3 := c2.wr 11 (2147507451#32) 0x80003e42#32
  let c4 := c3.goto 0x80003e36#32
  let c5 := c4.wr 13 (70#32) 0x80003e3a#32
  let r2 := ramWrite r1 (dst+28#32) (70#32) .b
  let c6 := c5.goto 0x80003e3e#32
  let c7 := c6.wr 14 ((dst+29#32)) 0x80003e40#32
  let c8 := c7.wr 11 (2147507452#32) 0x80003e42#32
  let c9 := c8.goto 0x80003e36#32
  let c10 := c9.wr 13 (105#32) 0x80003e3a#32
  let r3 := ramWrite r2 (dst+29#32) (105#32) .b
  let c11 := c10.goto 0x80003e3e#32
  let c12 := c11.wr 14 ((dst+30#32)) 0x80003e40#32
  let c13 := c12.wr 11 (2147507453#32) 0x80003e42#32
  let c14 := c13.goto 0x80003e36#32
  let c15 := c14.wr 13 (101#32) 0x80003e3a#32
  let r4 := ramWrite r3 (dst+30#32) (101#32) .b
  let c16 := c15.goto 0x80003e3e#32
  let c17 := c16.wr 14 ((dst+31#32)) 0x80003e40#32
  let c18 := c17.wr 11 (2147507454#32) 0x80003e42#32
  let c19 := c18.goto 0x80003e36#32
  let c20 := c19.wr 13 (108#32) 0x80003e3a#32
  let r5 := ramWrite r4 (dst+31#32) (108#32) .b
  let c21 := c20.goto 0x80003e3e#32
  let c22 := c21.wr 14 ((dst+32#32)) 0x80003e40#32
  let c23 := c22.wr 11 (2147507455#32) 0x80003e42#32
  let c24 := c23.goto 0x80003e36#32
  let c25 := c24.wr 13 (100#32) 0x80003e3a#32
  let r6 := ramWrite r5 (dst+32#32) (100#32) .b
  let c26 := c25.goto 0x80003e3e#32
  let c27 := c26.wr 14 ((dst+33#32)) 0x80003e40#32
  let c28 := c27.wr 11 (2147507456#32) 0x80003e42#32
  let c29 := c28.goto 0x80003e36#32
  let c30 := c29.wr 13 (115#32) 0x80003e3a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,r1⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rp2147499578) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 r1 [],[]⟩
    have v14 : c.get 14=(dst+27#32) := by simp [Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    have v13 : c.get 13=32#32 := by simp [Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_store,v14,v13]
    rw [hp]
    change Observed.interp B img o (.store .b ((dst+27#32)+0#32) 32#32 false (.done (c.goto 0x80003e3e#32))) ram 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+27#32)+0#32=dst+27#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 27) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,r1⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x80003e3e#32).getLsbD 0=false;decide) rp2147499582 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) r1 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v14 : c1.get 14=(dst+27#32) := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c1.wr 14 (alu .add (dst+27#32) 1#32) 0x80003e40#32)) r1 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : alu .add (dst+27#32) 1#32=(dst+28#32))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r1⟩ := by
    refine Quiet.step_of (by change (0x80003e40#32).getLsbD 0=false;decide) rp2147499584 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r1 [],[]⟩
    have v11 : c2.get 11=2147507450#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_opimm,v11]
    change Observed.interp B img o (.done (c2.wr 11 (alu .add 2147507450#32 1#32) 0x80003e42#32)) r1 0 [] [] = _
    rw [(by decide +kernel : alu .add 2147507450#32 1#32=2147507451#32)];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r1⟩ ⟨c4,r1⟩ := by
    refine Quiet.step_of (by change (0x80003e42#32).getLsbD 0=false;decide) rp2147499586 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r1 0 [] [] = ⟨.ok c4 r1 [],[]⟩
    have v14 : c3.get 14=(dst+28#32) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    have v10 : c3.get 10=(dst+44#32) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_branch,v14,v10,(by simp [taken,BitVec.add_right_inj] : taken .ne (dst+28#32) (dst+44#32)=true)]
    simp only [ite_true]
    rw [show c3.pc=2147499586#32 by rfl,show 2147499586#32+4294967284#32=2147499574#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r1⟩ ⟨c5,r1⟩ := by
    refine Quiet.step_of (by change (0x80003e36#32).getLsbD 0=false;decide) rp2147499574 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r1 0 [] [] = ⟨.ok c5 r1 [],[]⟩
    have v11 : c4.get 11=2147507451#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    have hb : ReadBytes.Byte B img r1 2147507451#32 70#8 := .rom (by unfold B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by rw [PackedData.read_byte _ (by decide) (by decide)];exact congrArg some (by decide +kernel))
    rw [exec_load,v11]
    change Observed.interp B img o (.load .b 2147507451#32 false _) r1 0 [] [] = _
    rw [ObservedByte.load hb o _ 0 [] []];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r1⟩ ⟨c6,r2⟩ := by
    refine Quiet.step_of (by change (0x80003e3a#32).getLsbD 0=false;decide) rp2147499578 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r1 0 [] [] = ⟨.ok c6 r2 [],[]⟩
    have v14 : c5.get 14=(dst+28#32) := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    have v13 : c5.get 13=70#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+28#32)+0#32) 70#32 false (.done (c5.goto 0x80003e3e#32))) r1 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+28#32)+0#32=dst+28#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 28) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r2⟩ ⟨c7,r2⟩ := by
    refine Quiet.step_of (by change (0x80003e3e#32).getLsbD 0=false;decide) rp2147499582 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r2 0 [] [] = ⟨.ok c7 r2 [],[]⟩
    have v14 : c6.get 14=(dst+28#32) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c6.wr 14 (alu .add (dst+28#32) 1#32) 0x80003e40#32)) r2 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : alu .add (dst+28#32) 1#32=(dst+29#32))];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r2⟩ ⟨c8,r2⟩ := by
    refine Quiet.step_of (by change (0x80003e40#32).getLsbD 0=false;decide) rp2147499584 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r2 0 [] [] = ⟨.ok c8 r2 [],[]⟩
    have v11 : c7.get 11=2147507451#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_opimm,v11]
    change Observed.interp B img o (.done (c7.wr 11 (alu .add 2147507451#32 1#32) 0x80003e42#32)) r2 0 [] [] = _
    rw [(by decide +kernel : alu .add 2147507451#32 1#32=2147507452#32)];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r2⟩ ⟨c9,r2⟩ := by
    refine Quiet.step_of (by change (0x80003e42#32).getLsbD 0=false;decide) rp2147499586 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r2 0 [] [] = ⟨.ok c9 r2 [],[]⟩
    have v14 : c8.get 14=(dst+29#32) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    have v10 : c8.get 10=(dst+44#32) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_branch,v14,v10,(by simp [taken,BitVec.add_right_inj] : taken .ne (dst+29#32) (dst+44#32)=true)]
    simp only [ite_true]
    rw [show c8.pc=2147499586#32 by rfl,show 2147499586#32+4294967284#32=2147499574#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r2⟩ ⟨c10,r2⟩ := by
    refine Quiet.step_of (by change (0x80003e36#32).getLsbD 0=false;decide) rp2147499574 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r2 0 [] [] = ⟨.ok c10 r2 [],[]⟩
    have v11 : c9.get 11=2147507452#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    have hb : ReadBytes.Byte B img r2 2147507452#32 105#8 := .rom (by unfold B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by rw [PackedData.read_byte _ (by decide) (by decide)];exact congrArg some (by decide +kernel))
    rw [exec_load,v11]
    change Observed.interp B img o (.load .b 2147507452#32 false _) r2 0 [] [] = _
    rw [ObservedByte.load hb o _ 0 [] []];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r2⟩ ⟨c11,r3⟩ := by
    refine Quiet.step_of (by change (0x80003e3a#32).getLsbD 0=false;decide) rp2147499578 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r2 0 [] [] = ⟨.ok c11 r3 [],[]⟩
    have v14 : c10.get 14=(dst+29#32) := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    have v13 : c10.get 13=105#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+29#32)+0#32) 105#32 false (.done (c10.goto 0x80003e3e#32))) r2 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+29#32)+0#32=dst+29#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 29) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r3⟩ ⟨c12,r3⟩ := by
    refine Quiet.step_of (by change (0x80003e3e#32).getLsbD 0=false;decide) rp2147499582 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r3 0 [] [] = ⟨.ok c12 r3 [],[]⟩
    have v14 : c11.get 14=(dst+29#32) := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c11.wr 14 (alu .add (dst+29#32) 1#32) 0x80003e40#32)) r3 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : alu .add (dst+29#32) 1#32=(dst+30#32))];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,r3⟩ ⟨c13,r3⟩ := by
    refine Quiet.step_of (by change (0x80003e40#32).getLsbD 0=false;decide) rp2147499584 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r3 0 [] [] = ⟨.ok c13 r3 [],[]⟩
    have v11 : c12.get 11=2147507452#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_opimm,v11]
    change Observed.interp B img o (.done (c12.wr 11 (alu .add 2147507452#32 1#32) 0x80003e42#32)) r3 0 [] [] = _
    rw [(by decide +kernel : alu .add 2147507452#32 1#32=2147507453#32)];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r3⟩ ⟨c14,r3⟩ := by
    refine Quiet.step_of (by change (0x80003e42#32).getLsbD 0=false;decide) rp2147499586 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r3 0 [] [] = ⟨.ok c14 r3 [],[]⟩
    have v14 : c13.get 14=(dst+30#32) := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    have v10 : c13.get 10=(dst+44#32) := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_branch,v14,v10,(by simp [taken,BitVec.add_right_inj] : taken .ne (dst+30#32) (dst+44#32)=true)]
    simp only [ite_true]
    rw [show c13.pc=2147499586#32 by rfl,show 2147499586#32+4294967284#32=2147499574#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,r3⟩ ⟨c15,r3⟩ := by
    refine Quiet.step_of (by change (0x80003e36#32).getLsbD 0=false;decide) rp2147499574 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) r3 0 [] [] = ⟨.ok c15 r3 [],[]⟩
    have v11 : c14.get 11=2147507453#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    have hb : ReadBytes.Byte B img r3 2147507453#32 101#8 := .rom (by unfold B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by rw [PackedData.read_byte _ (by decide) (by decide)];exact congrArg some (by decide +kernel))
    rw [exec_load,v11]
    change Observed.interp B img o (.load .b 2147507453#32 false _) r3 0 [] [] = _
    rw [ObservedByte.load hb o _ 0 [] []];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,r3⟩ ⟨c16,r4⟩ := by
    refine Quiet.step_of (by change (0x80003e3a#32).getLsbD 0=false;decide) rp2147499578 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) r3 0 [] [] = ⟨.ok c16 r4 [],[]⟩
    have v14 : c15.get 14=(dst+30#32) := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    have v13 : c15.get 13=101#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+30#32)+0#32) 101#32 false (.done (c15.goto 0x80003e3e#32))) r3 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+30#32)+0#32=dst+30#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 30) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,r4⟩ ⟨c17,r4⟩ := by
    refine Quiet.step_of (by change (0x80003e3e#32).getLsbD 0=false;decide) rp2147499582 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) r4 0 [] [] = ⟨.ok c17 r4 [],[]⟩
    have v14 : c16.get 14=(dst+30#32) := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c16.wr 14 (alu .add (dst+30#32) 1#32) 0x80003e40#32)) r4 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : alu .add (dst+30#32) 1#32=(dst+31#32))];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,r4⟩ ⟨c18,r4⟩ := by
    refine Quiet.step_of (by change (0x80003e40#32).getLsbD 0=false;decide) rp2147499584 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) r4 0 [] [] = ⟨.ok c18 r4 [],[]⟩
    have v11 : c17.get 11=2147507453#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_opimm,v11]
    change Observed.interp B img o (.done (c17.wr 11 (alu .add 2147507453#32 1#32) 0x80003e42#32)) r4 0 [] [] = _
    rw [(by decide +kernel : alu .add 2147507453#32 1#32=2147507454#32)];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,r4⟩ ⟨c19,r4⟩ := by
    refine Quiet.step_of (by change (0x80003e42#32).getLsbD 0=false;decide) rp2147499586 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) r4 0 [] [] = ⟨.ok c19 r4 [],[]⟩
    have v14 : c18.get 14=(dst+31#32) := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    have v10 : c18.get 10=(dst+44#32) := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_branch,v14,v10,(by simp [taken,BitVec.add_right_inj] : taken .ne (dst+31#32) (dst+44#32)=true)]
    simp only [ite_true]
    rw [show c18.pc=2147499586#32 by rfl,show 2147499586#32+4294967284#32=2147499574#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,r4⟩ ⟨c20,r4⟩ := by
    refine Quiet.step_of (by change (0x80003e36#32).getLsbD 0=false;decide) rp2147499574 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) r4 0 [] [] = ⟨.ok c20 r4 [],[]⟩
    have v11 : c19.get 11=2147507454#32 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    have hb : ReadBytes.Byte B img r4 2147507454#32 108#8 := .rom (by unfold B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by rw [PackedData.read_byte _ (by decide) (by decide)];exact congrArg some (by decide +kernel))
    rw [exec_load,v11]
    change Observed.interp B img o (.load .b 2147507454#32 false _) r4 0 [] [] = _
    rw [ObservedByte.load hb o _ 0 [] []];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,r4⟩ ⟨c21,r5⟩ := by
    refine Quiet.step_of (by change (0x80003e3a#32).getLsbD 0=false;decide) rp2147499578 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) r4 0 [] [] = ⟨.ok c21 r5 [],[]⟩
    have v14 : c20.get 14=(dst+31#32) := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    have v13 : c20.get 13=108#32 := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+31#32)+0#32) 108#32 false (.done (c20.goto 0x80003e3e#32))) r4 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+31#32)+0#32=dst+31#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 31) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,r5⟩ ⟨c22,r5⟩ := by
    refine Quiet.step_of (by change (0x80003e3e#32).getLsbD 0=false;decide) rp2147499582 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) r5 0 [] [] = ⟨.ok c22 r5 [],[]⟩
    have v14 : c21.get 14=(dst+31#32) := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c21.wr 14 (alu .add (dst+31#32) 1#32) 0x80003e40#32)) r5 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : alu .add (dst+31#32) 1#32=(dst+32#32))];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,r5⟩ ⟨c23,r5⟩ := by
    refine Quiet.step_of (by change (0x80003e40#32).getLsbD 0=false;decide) rp2147499584 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) r5 0 [] [] = ⟨.ok c23 r5 [],[]⟩
    have v11 : c22.get 11=2147507454#32 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_opimm,v11]
    change Observed.interp B img o (.done (c22.wr 11 (alu .add 2147507454#32 1#32) 0x80003e42#32)) r5 0 [] [] = _
    rw [(by decide +kernel : alu .add 2147507454#32 1#32=2147507455#32)];first | rfl | (rw [hp];rfl)
  have t23 : Quiet.Step B img ⟨c23,r5⟩ ⟨c24,r5⟩ := by
    refine Quiet.step_of (by change (0x80003e42#32).getLsbD 0=false;decide) rp2147499586 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) r5 0 [] [] = ⟨.ok c24 r5 [],[]⟩
    have v14 : c23.get 14=(dst+32#32) := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    have v10 : c23.get 10=(dst+44#32) := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_branch,v14,v10,(by simp [taken,BitVec.add_right_inj] : taken .ne (dst+32#32) (dst+44#32)=true)]
    simp only [ite_true]
    rw [show c23.pc=2147499586#32 by rfl,show 2147499586#32+4294967284#32=2147499574#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t24 : Quiet.Step B img ⟨c24,r5⟩ ⟨c25,r5⟩ := by
    refine Quiet.step_of (by change (0x80003e36#32).getLsbD 0=false;decide) rp2147499574 fun o => ?_
    change Observed.interp B img o (exec c24 _ _) r5 0 [] [] = ⟨.ok c25 r5 [],[]⟩
    have v11 : c24.get 11=2147507455#32 := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    have hb : ReadBytes.Byte B img r5 2147507455#32 100#8 := .rom (by unfold B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by rw [PackedData.read_byte _ (by decide) (by decide)];exact congrArg some (by decide +kernel))
    rw [exec_load,v11]
    change Observed.interp B img o (.load .b 2147507455#32 false _) r5 0 [] [] = _
    rw [ObservedByte.load hb o _ 0 [] []];first | rfl | (rw [hp];rfl)
  have t25 : Quiet.Step B img ⟨c25,r5⟩ ⟨c26,r6⟩ := by
    refine Quiet.step_of (by change (0x80003e3a#32).getLsbD 0=false;decide) rp2147499578 fun o => ?_
    change Observed.interp B img o (exec c25 _ _) r5 0 [] [] = ⟨.ok c26 r6 [],[]⟩
    have v14 : c25.get 14=(dst+32#32) := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    have v13 : c25.get 13=100#32 := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_store,v14,v13]
    change Observed.interp B img o (.store .b ((dst+32#32)+0#32) 100#32 false (.done (c25.goto 0x80003e3e#32))) r5 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : (dst+32#32)+0#32=dst+32#32),Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 32) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t26 : Quiet.Step B img ⟨c26,r6⟩ ⟨c27,r6⟩ := by
    refine Quiet.step_of (by change (0x80003e3e#32).getLsbD 0=false;decide) rp2147499582 fun o => ?_
    change Observed.interp B img o (exec c26 _ _) r6 0 [] [] = ⟨.ok c27 r6 [],[]⟩
    have v14 : c26.get 14=(dst+32#32) := by simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c26.wr 14 (alu .add (dst+32#32) 1#32) 0x80003e40#32)) r6 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : alu .add (dst+32#32) 1#32=(dst+33#32))];first | rfl | (rw [hp];rfl)
  have t27 : Quiet.Step B img ⟨c27,r6⟩ ⟨c28,r6⟩ := by
    refine Quiet.step_of (by change (0x80003e40#32).getLsbD 0=false;decide) rp2147499584 fun o => ?_
    change Observed.interp B img o (exec c27 _ _) r6 0 [] [] = ⟨.ok c28 r6 [],[]⟩
    have v11 : c27.get 11=2147507455#32 := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_opimm,v11]
    change Observed.interp B img o (.done (c27.wr 11 (alu .add 2147507455#32 1#32) 0x80003e42#32)) r6 0 [] [] = _
    rw [(by decide +kernel : alu .add 2147507455#32 1#32=2147507456#32)];first | rfl | (rw [hp];rfl)
  have t28 : Quiet.Step B img ⟨c28,r6⟩ ⟨c29,r6⟩ := by
    refine Quiet.step_of (by change (0x80003e42#32).getLsbD 0=false;decide) rp2147499586 fun o => ?_
    change Observed.interp B img o (exec c28 _ _) r6 0 [] [] = ⟨.ok c29 r6 [],[]⟩
    have v14 : c28.get 14=(dst+33#32) := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    have v10 : c28.get 10=(dst+44#32) := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    rw [exec_branch,v14,v10,(by simp [taken,BitVec.add_right_inj] : taken .ne (dst+33#32) (dst+44#32)=true)]
    simp only [ite_true]
    rw [show c28.pc=2147499586#32 by rfl,show 2147499586#32+4294967284#32=2147499574#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t29 : Quiet.Step B img ⟨c29,r6⟩ ⟨c30,r6⟩ := by
    refine Quiet.step_of (by change (0x80003e36#32).getLsbD 0=false;decide) rp2147499574 fun o => ?_
    change Observed.interp B img o (exec c29 _ _) r6 0 [] [] = ⟨.ok c30 r6 [],[]⟩
    have v11 : c29.get 11=2147507456#32 := by simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
    have hb : ReadBytes.Byte B img r6 2147507456#32 115#8 := .rom (by unfold B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by rw [PackedData.read_byte _ (by decide) (by decide)];exact congrArg some (by decide +kernel))
    rw [exec_load,v11]
    change Observed.interp B img o (.load .b 2147507456#32 false _) r6 0 [] [] = _
    rw [ObservedByte.load hb o _ 0 [] []];first | rfl | (rw [hp];rfl)
  refine ⟨c30,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.step t23 (.step t24 (.step t25 (.step t26 (.step t27 (.step t28 (.single t29))))))))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15]
  · intro reg h14 h11 h13;simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15,h14,h11,h13]
end E5R.Thermostat.HttpReason431Part3
