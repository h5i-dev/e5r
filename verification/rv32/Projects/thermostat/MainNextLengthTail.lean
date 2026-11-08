import Projects.thermostat.FrameOffsets
import Projects.thermostat.MainNextCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainNextLengthTail
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp len used minor p0 p1 p2 p3 p4 p5 p6 : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+40#32) (minor) .w) (sp+4896#32) (alu .or (alu .or (alu .sll p1 8#32) p0) (alu .or (alu .sll p2 16#32) (alu .sll p3 24#32))) .w) (sp+4900#32) (alu .or (alu .sll p5 8#32) p4) .h) (sp+4902#32) (p6) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp len used minor p0 p1 p2 p3 p4 p5 p6 : Word) (h2 : c.get 2=sp) (h8 : c.get 8=sp+3204#32) (h25 : c.get 25=used)
(stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
(hminor : extend .b false (ramRead ram (sp+3616#32) .b)=minor) (hlen : ramRead ram (sp+3648#32) .w=len)
(hp0 : extend .b false (ramRead ram (sp+3617#32) .b)=p0)
(hp1 : extend .b false (ramRead ram (sp+3618#32) .b)=p1)
(hp2 : extend .b false (ramRead ram (sp+3619#32) .b)=p2)
(hp3 : extend .b false (ramRead ram (sp+3620#32) .b)=p3)
(hp4 : extend .b false (ramRead ram (sp+3621#32) .b)=p4)
(hp5 : extend .b false (ramRead ram (sp+3622#32) .b)=p5)
(hp6 : extend .b false (ramRead ram (sp+3623#32) .b)=p6)

    (hp : c.pc=0x80000cf6#32) :
    ∃ d, Quiet.Steps B img 25 ⟨c,ram⟩ ⟨d,memory ram sp len used minor p0 p1 p2 p3 p4 p5 p6⟩ ∧ d.pc=0x80000a9a#32 ∧
      d.get 16=p6 ∧ d.get 10=alu .or (alu .sll p5 8#32) (p4) ∧ d.get 11=alu .or (alu .or (alu .sll p1 8#32) p0) (alu .or (alu .sll p2 16#32) (alu .sll p3 24#32)) ∧ d.get 12=alu .or (alu .sll p2 16#32) (alu .sll p3 24#32) ∧ d.get 13=minor ∧ d.get 14=p0 ∧ d.get 15=p4 ∧ d.get 20=len ∧ d.get 24=used ∧ (∀ r : Reg, r≠16 → r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → r≠15 → r≠20 → r≠24 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 16 (sp+2047#32) 0x80000cfa#32
  let c2 := c1.wr 16 (sp+3617#32) 0x80000cfe#32
  let c3 := c2.wr 10 (p5) 0x80000d02#32
  let c4 := c3.wr 11 (p1) 0x80000d06#32
  let c5 := c4.wr 12 (p2) 0x80000d0a#32
  let c6 := c5.wr 13 (p3) 0x80000d0e#32
  let c7 := c6.wr 14 (p0) 0x80000d12#32
  let c8 := c7.wr 15 (p4) 0x80000d16#32
  let c9 := c8.wr 16 (p6) 0x80000d1a#32
  let c10 := c9.wr 10 (alu .sll p5 8#32) 0x80000d1c#32
  let c11 := c10.wr 11 (alu .sll p1 8#32) 0x80000d1e#32
  let c12 := c11.wr 12 (alu .sll p2 16#32) 0x80000d20#32
  let c13 := c12.wr 13 (alu .sll p3 24#32) 0x80000d22#32
  let c14 := c13.wr 11 (alu .or (alu .sll p1 8#32) (p0)) 0x80000d24#32
  let c15 := c14.wr 12 (alu .or (alu .sll p2 16#32) (alu .sll p3 24#32)) 0x80000d26#32
  let c16 := c15.wr 13 (minor) 0x80000d2a#32
  let r1 := ramWrite ram (sp+40#32) (minor) .w
  let c17 := c16.goto 0x80000d2c#32
  let c18 := c17.wr 20 (len) 0x80000d30#32
  let c19 := c18.wr 10 (alu .or (alu .sll p5 8#32) (p4)) 0x80000d32#32
  let c20 := c19.wr 11 (alu .or (alu .or (alu .sll p1 8#32) p0) (alu .or (alu .sll p2 16#32) (alu .sll p3 24#32))) 0x80000d34#32
  let r2 := ramWrite r1 (sp+4896#32) (alu .or (alu .or (alu .sll p1 8#32) p0) (alu .or (alu .sll p2 16#32) (alu .sll p3 24#32))) .w
  let c21 := c20.goto 0x80000d38#32
  let r3 := ramWrite r2 (sp+4900#32) (alu .or (alu .sll p5 8#32) p4) .h
  let c22 := c21.goto 0x80000d3c#32
  let r4 := ramWrite r3 (sp+4902#32) (p6) .b
  let c23 := c22.goto 0x80000d40#32
  let c24 := c23.wr 24 (used) 0x80000d42#32
  let c25 := c24.goto 0x80000a9a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact nx2147486966) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h2];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000cfa#32).getLsbD 0=false;decide) nx2147486970 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v16 : c1.get 16=sp+2047#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_opimm,v16]
    change Observed.interp B img o (Eff.done (c1.wr 16 ((sp+2047#32)+1570#32) 0x80000cfe#32)) ram 0 [] []=_
    rw [BitVec.add_assoc,show 2047#32+1570#32=3617#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000cfe#32).getLsbD 0=false;decide) nx2147486974 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v16 : c2.get 16=sp+3617#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_load,v16,BitVec.add_assoc,show 3617#32+5#32=3622#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access stack (off := 3622) (by decide) (by decide)),hp5];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000d02#32).getLsbD 0=false;decide) nx2147486978 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v16 : c3.get 16=sp+3617#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_load,v16,BitVec.add_assoc,show 3617#32+1#32=3618#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access stack (off := 3618) (by decide) (by decide)),hp1];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80000d06#32).getLsbD 0=false;decide) nx2147486982 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v16 : c4.get 16=sp+3617#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_load,v16,BitVec.add_assoc,show 3617#32+2#32=3619#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access stack (off := 3619) (by decide) (by decide)),hp2];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80000d0a#32).getLsbD 0=false;decide) nx2147486986 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v16 : c5.get 16=sp+3617#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_load,v16,BitVec.add_assoc,show 3617#32+3#32=3620#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access stack (off := 3620) (by decide) (by decide)),hp3];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80000d0e#32).getLsbD 0=false;decide) nx2147486990 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v16 : c6.get 16=sp+3617#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_load,v16,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access stack (off := 3617) (by decide) (by decide)),hp0];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80000d12#32).getLsbD 0=false;decide) nx2147486994 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v16 : c7.get 16=sp+3617#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_load,v16,BitVec.add_assoc,show 3617#32+4#32=3621#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access stack (off := 3621) (by decide) (by decide)),hp4];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80000d16#32).getLsbD 0=false;decide) nx2147486998 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v16 : c8.get 16=sp+3617#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_load,v16,BitVec.add_assoc,show 3617#32+6#32=3623#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access stack (off := 3623) (by decide) (by decide)),hp6];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80000d1a#32).getLsbD 0=false;decide) nx2147487002 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v10 : c9.get 10=p5 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80000d1c#32).getLsbD 0=false;decide) nx2147487004 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v11 : c10.get 11=p1 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_opimm,v11];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x80000d1e#32).getLsbD 0=false;decide) nx2147487006 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v12 : c11.get 12=p2 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_opimm,v12];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x80000d20#32).getLsbD 0=false;decide) nx2147487008 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    have v13 : c12.get 13=p3 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_opimm,v13];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine Quiet.step_of (by change (0x80000d22#32).getLsbD 0=false;decide) nx2147487010 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 ram [],[]⟩
    have v11 : c13.get 11=alu .sll p1 8#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    have v14 : c13.get 14=p0 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_op,v11,v14];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine Quiet.step_of (by change (0x80000d24#32).getLsbD 0=false;decide) nx2147487012 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) ram 0 [] [] = ⟨.ok c15 ram [],[]⟩
    have v12 : c14.get 12=alu .sll p2 16#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    have v13 : c14.get 13=alu .sll p3 24#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_op,v12,v13];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,ram⟩ ⟨c16,ram⟩ := by
    refine Quiet.step_of (by change (0x80000d26#32).getLsbD 0=false;decide) nx2147487014 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) ram 0 [] [] = ⟨.ok c16 ram [],[]⟩
    have v8 : c15.get 8=sp+3204#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+412#32=3616#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access stack (off := 3616) (by decide) (by decide)),hminor];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,ram⟩ ⟨c17,r1⟩ := by
    refine Quiet.step_of (by change (0x80000d2a#32).getLsbD 0=false;decide) nx2147487018 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) ram 0 [] [] = ⟨.ok c17 r1 [],[]⟩
    have v2 : c16.get 2=sp := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    have v13 : c16.get 13=minor := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_store,v2,v13,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 10 aligned) (Memory.block_access stack (off := 40) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,r1⟩ ⟨c18,r1⟩ := by
    refine Quiet.step_of (by change (0x80000d2c#32).getLsbD 0=false;decide) nx2147487020 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) r1 0 [] [] = ⟨.ok c18 r1 [],[]⟩
    have v8 : c17.get 8=sp+3204#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    have input : ramRead r1 (sp+3648#32) .w=ramRead ram (sp+3648#32) .w := by
      dsimp only [r1]
      exact FrameOffsets.word ram sp minor 3648 40 .w (by decide) (by decide) (by decide)
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+444#32=3648#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 912 aligned) (Memory.block_access stack (off := 3648) (by decide) (by decide)),input,hlen];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,r1⟩ ⟨c19,r1⟩ := by
    refine Quiet.step_of (by change (0x80000d30#32).getLsbD 0=false;decide) nx2147487024 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) r1 0 [] [] = ⟨.ok c19 r1 [],[]⟩
    have v10 : c18.get 10=alu .sll p5 8#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    have v15 : c18.get 15=p4 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_op,v10,v15];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,r1⟩ ⟨c20,r1⟩ := by
    refine Quiet.step_of (by change (0x80000d32#32).getLsbD 0=false;decide) nx2147487026 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) r1 0 [] [] = ⟨.ok c20 r1 [],[]⟩
    have v11 : c19.get 11=alu .or (alu .sll p1 8#32) p0 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    have v12 : c19.get 12=alu .or (alu .sll p2 16#32) (alu .sll p3 24#32) := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_op,v11,v12];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,r1⟩ ⟨c21,r2⟩ := by
    refine Quiet.step_of (by change (0x80000d34#32).getLsbD 0=false;decide) nx2147487028 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) r1 0 [] [] = ⟨.ok c21 r2 [],[]⟩
    have v8 : c20.get 8=sp+3204#32 := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    have v11 : c20.get 11=alu .or (alu .or (alu .sll p1 8#32) p0) (alu .or (alu .sll p2 16#32) (alu .sll p3 24#32)) := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_store,v8,v11,BitVec.add_assoc,show 3204#32+1692#32=4896#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1224 aligned) (Memory.block_access stack (off := 4896) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,r2⟩ ⟨c22,r3⟩ := by
    refine Quiet.step_of (by change (0x80000d38#32).getLsbD 0=false;decide) nx2147487032 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) r2 0 [] [] = ⟨.ok c22 r3 [],[]⟩
    have v8 : c21.get 8=sp+3204#32 := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    have v10 : c21.get 10=alu .or (alu .sll p5 8#32) p4 := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_store,v8,v10,BitVec.add_assoc,show 3204#32+1696#32=4900#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 2450 (by omega)) (Memory.block_access stack (off := 4900) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,r3⟩ ⟨c23,r4⟩ := by
    refine Quiet.step_of (by change (0x80000d3c#32).getLsbD 0=false;decide) nx2147487036 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) r3 0 [] [] = ⟨.ok c23 r4 [],[]⟩
    have v8 : c22.get 8=sp+3204#32 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    have v16 : c22.get 16=p6 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_store,v8,v16,BitVec.add_assoc,show 3204#32+1698#32=4902#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access stack (off := 4902) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t23 : Quiet.Step B img ⟨c23,r4⟩ ⟨c24,r4⟩ := by
    refine Quiet.step_of (by change (0x80000d40#32).getLsbD 0=false;decide) nx2147487040 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) r4 0 [] [] = ⟨.ok c24 r4 [],[]⟩
    have v25 : c23.get 25=used := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
    rw [exec_op,Core.get_zero,v25]
    change Observed.interp B img o (Eff.done (c23.wr 24 (0#32+used) 0x80000d42#32)) r4 0 [] []=⟨.ok c24 r4 [],[]⟩
    rw [BitVec.zero_add]
    rfl
  have t24 : Quiet.Step B img ⟨c24,r4⟩ ⟨c25,r4⟩ := by
    refine Quiet.step_of (by change (0x80000d42#32).getLsbD 0=false;decide) nx2147487042 fun o => ?_
    change Observed.interp B img o (exec c24 _ _) r4 0 [] [] = ⟨.ok c25 r4 [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump (c24.set 0 0x80000d44#32) (0x80000d42#32+0xfffffd58#32)) r4 0 [] []=_
    rw [show 0x80000d42#32+0xfffffd58#32=0x80000a9a#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c25,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.step t23 (.single t24)))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
  · simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
  · simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
  · simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
  · simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
  · simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
  · simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
  · simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
  · simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25]
  · intro reg h16 h10 h11 h12 h13 h14 h15 h20 h24;simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h25,h16,h10,h11,h12,h13,h14,h15,h20,h24]
end E5R.Thermostat.MainNextLengthTail
