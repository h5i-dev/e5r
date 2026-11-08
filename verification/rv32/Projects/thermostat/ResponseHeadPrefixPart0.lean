import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.ResponseHeadMath
import Projects.thermostat.HttpDecTensMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseHeadPrefixPart0
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (dst+0#32) (72#32) .b) (dst+1#32) (84#32) .b) (dst+2#32) (84#32) .b) (dst+3#32) (80#32) .b) (dst+4#32) (47#32) .b) (dst+5#32) (49#32) .b) (dst+6#32) (46#32) .b) (dst+7#32) (49#32) .b) (dst+8#32) (32#32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat) (hlo : 100≤status) (hhi : status≤599) (hct : ctlen≤16) (h2 : c.get 2=(frame+16#32)) (h10 : c.get 10=dst) (h11 : c.get 11=192#32) (h12 : c.get 12=(BitVec.ofNat 32 status)) (h13 : c.get 13=ctptr) (h14 : c.get 14=(BitVec.ofNat 32 ctlen)) (h15 : c.get 15=body) (h16 : c.get 16=flag) (h17 : c.get 17=9#32) (hstack : Memory.Block B frame 96) (ha : frame.toNat%4=0) (hdst : Memory.Block B dst 192)
    (hp : c.pc=0x80003f26#32) :
    ∃ d, Quiet.Steps B img 24 ⟨c,ram⟩ ⟨d,memory ram frame dst ctptr body flag status ctlen⟩ ∧ d.pc=0x80003f82#32 ∧
      d.get 5=(BitVec.ofNat 32 (48+status/100)) ∧ d.get 6=49#32 ∧ d.get 7=46#32 ∧ d.get 28=32#32 ∧ d.get 17=11#32 ∧ (∀ r : Reg, r≠5 → r≠6 → r≠7 → r≠28 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 5 (72#32) 0x80003f2a#32
  let c2 := c1.wr 6 (84#32) 0x80003f2e#32
  let c3 := c2.wr 7 (80#32) 0x80003f32#32
  let r1 := ramWrite ram (dst+0#32) (72#32) .b
  let c4 := c3.goto 0x80003f36#32
  let r2 := ramWrite r1 (dst+1#32) (84#32) .b
  let c5 := c4.goto 0x80003f3a#32
  let r3 := ramWrite r2 (dst+2#32) (84#32) .b
  let c6 := c5.goto 0x80003f3e#32
  let r4 := ramWrite r3 (dst+3#32) (80#32) .b
  let c7 := c6.goto 0x80003f42#32
  let c8 := c7.wr 5 (47#32) 0x80003f46#32
  let c9 := c8.wr 6 (49#32) 0x80003f4a#32
  let c10 := c9.wr 7 (46#32) 0x80003f4e#32
  let c11 := c10.wr 28 (32#32) 0x80003f52#32
  let r5 := ramWrite r4 (dst+4#32) (47#32) .b
  let c12 := c11.goto 0x80003f56#32
  let r6 := ramWrite r5 (dst+5#32) (49#32) .b
  let c13 := c12.goto 0x80003f5a#32
  let r7 := ramWrite r6 (dst+6#32) (46#32) .b
  let c14 := c13.goto 0x80003f5e#32
  let r8 := ramWrite r7 (dst+7#32) (49#32) .b
  let c15 := c14.goto 0x80003f62#32
  let r9 := ramWrite r8 (dst+8#32) (32#32) .b
  let c16 := c15.goto 0x80003f66#32
  let c17 := c16.goto 0x80003f6a#32
  let c18 := c17.wr 17 (4096#32) 0x80003f6c#32
  let c19 := c18.wr 5 ((((BitVec.ofNat 32 status)) >>> 2)) 0x80003f70#32
  let c20 := c19.wr 17 (5243#32) 0x80003f74#32
  let c21 := c20.wr 17 ((((((BitVec.ofNat 32 status)) >>> 2))*(5243#32))) 0x80003f78#32
  let c22 := c21.wr 17 ((BitVec.ofNat 32 (status/100))) 0x80003f7c#32
  let c23 := c22.wr 5 ((BitVec.ofNat 32 (48+status/100))) 0x80003f80#32
  let c24 := c23.wr 17 (11#32) 0x80003f82#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147499814) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c.wr 5 (alu .add (0#32) (72#32)) (c.pc+4#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003f2a#32).getLsbD 0=false;decide) rh2147499818 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c1.wr 6 (alu .add (0#32) (84#32)) (c1.pc+4#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80003f2e#32).getLsbD 0=false;decide) rh2147499822 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c2.wr 7 (alu .add (0#32) (80#32)) (c2.pc+4#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,r1⟩ := by
    refine Quiet.step_of (by change (0x80003f32#32).getLsbD 0=false;decide) rh2147499826 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 r1 [],[]⟩
    have v10 : c3.get 10=dst := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    have v5 : c3.get 5=72#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    rw [exec_store,v10,v5]
    rw [Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hdst (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r1⟩ ⟨c5,r2⟩ := by
    refine Quiet.step_of (by change (0x80003f36#32).getLsbD 0=false;decide) rh2147499830 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r1 0 [] [] = ⟨.ok c5 r2 [],[]⟩
    have v10 : c4.get 10=dst := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    have v6 : c4.get 6=84#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    rw [exec_store,v10,v6]
    rw [Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hdst (off := 1) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r2⟩ ⟨c6,r3⟩ := by
    refine Quiet.step_of (by change (0x80003f3a#32).getLsbD 0=false;decide) rh2147499834 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r2 0 [] [] = ⟨.ok c6 r3 [],[]⟩
    have v10 : c5.get 10=dst := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    have v6 : c5.get 6=84#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    rw [exec_store,v10,v6]
    rw [Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hdst (off := 2) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r3⟩ ⟨c7,r4⟩ := by
    refine Quiet.step_of (by change (0x80003f3e#32).getLsbD 0=false;decide) rh2147499838 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r3 0 [] [] = ⟨.ok c7 r4 [],[]⟩
    have v10 : c6.get 10=dst := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    have v7 : c6.get 7=80#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    rw [exec_store,v10,v7]
    rw [Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hdst (off := 3) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r4⟩ ⟨c8,r4⟩ := by
    refine Quiet.step_of (by change (0x80003f42#32).getLsbD 0=false;decide) rh2147499842 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r4 0 [] [] = ⟨.ok c8 r4 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c7.wr 5 (alu .add (0#32) (47#32)) (c7.pc+4#32))) r4 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t8 : Quiet.Step B img ⟨c8,r4⟩ ⟨c9,r4⟩ := by
    refine Quiet.step_of (by change (0x80003f46#32).getLsbD 0=false;decide) rh2147499846 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r4 0 [] [] = ⟨.ok c9 r4 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c8.wr 6 (alu .add (0#32) (49#32)) (c8.pc+4#32))) r4 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t9 : Quiet.Step B img ⟨c9,r4⟩ ⟨c10,r4⟩ := by
    refine Quiet.step_of (by change (0x80003f4a#32).getLsbD 0=false;decide) rh2147499850 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r4 0 [] [] = ⟨.ok c10 r4 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c9.wr 7 (alu .add (0#32) (46#32)) (c9.pc+4#32))) r4 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t10 : Quiet.Step B img ⟨c10,r4⟩ ⟨c11,r4⟩ := by
    refine Quiet.step_of (by change (0x80003f4e#32).getLsbD 0=false;decide) rh2147499854 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r4 0 [] [] = ⟨.ok c11 r4 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c10.wr 28 (alu .add (0#32) (32#32)) (c10.pc+4#32))) r4 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t11 : Quiet.Step B img ⟨c11,r4⟩ ⟨c12,r5⟩ := by
    refine Quiet.step_of (by change (0x80003f52#32).getLsbD 0=false;decide) rh2147499858 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r4 0 [] [] = ⟨.ok c12 r5 [],[]⟩
    have v10 : c11.get 10=dst := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    have v5 : c11.get 5=47#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    rw [exec_store,v10,v5]
    rw [Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hdst (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,r5⟩ ⟨c13,r6⟩ := by
    refine Quiet.step_of (by change (0x80003f56#32).getLsbD 0=false;decide) rh2147499862 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r5 0 [] [] = ⟨.ok c13 r6 [],[]⟩
    have v10 : c12.get 10=dst := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    have v6 : c12.get 6=49#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    rw [exec_store,v10,v6]
    rw [Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hdst (off := 5) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r6⟩ ⟨c14,r7⟩ := by
    refine Quiet.step_of (by change (0x80003f5a#32).getLsbD 0=false;decide) rh2147499866 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r6 0 [] [] = ⟨.ok c14 r7 [],[]⟩
    have v10 : c13.get 10=dst := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    have v7 : c13.get 7=46#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    rw [exec_store,v10,v7]
    rw [Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hdst (off := 6) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,r7⟩ ⟨c15,r8⟩ := by
    refine Quiet.step_of (by change (0x80003f5e#32).getLsbD 0=false;decide) rh2147499870 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) r7 0 [] [] = ⟨.ok c15 r8 [],[]⟩
    have v10 : c14.get 10=dst := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    have v6 : c14.get 6=49#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    rw [exec_store,v10,v6]
    rw [Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hdst (off := 7) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,r8⟩ ⟨c16,r9⟩ := by
    refine Quiet.step_of (by change (0x80003f62#32).getLsbD 0=false;decide) rh2147499874 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) r8 0 [] [] = ⟨.ok c16 r9 [],[]⟩
    have v10 : c15.get 10=dst := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    have v28 : c15.get 28=32#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    rw [exec_store,v10,v28]
    rw [Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hdst (off := 8) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,r9⟩ ⟨c17,r9⟩ := by
    refine Quiet.step_of (by change (0x80003f66#32).getLsbD 0=false;decide) rh2147499878 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) r9 0 [] [] = ⟨.ok c17 r9 [],[]⟩
    have v11 : c16.get 11=192#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    have v17 : c16.get 17=9#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    rw [exec_branch,v11,v17,(by decide +kernel : taken .eq (192#32) (9#32)=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,r9⟩ ⟨c18,r9⟩ := by
    refine Quiet.step_of (by change (0x80003f6a#32).getLsbD 0=false;decide) rh2147499882 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) r9 0 [] [] = ⟨.ok c18 r9 [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,r9⟩ ⟨c19,r9⟩ := by
    refine Quiet.step_of (by change (0x80003f6c#32).getLsbD 0=false;decide) rh2147499884 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) r9 0 [] [] = ⟨.ok c19 r9 [],[]⟩
    have v12 : c18.get 12=(BitVec.ofNat 32 status) := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    rw [exec_opimm,v12]
    change Observed.interp B img o (.done (c18.wr 5 (alu .srl ((BitVec.ofNat 32 status)) (2#32)) (c18.pc+4#32))) r9 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t19 : Quiet.Step B img ⟨c19,r9⟩ ⟨c20,r9⟩ := by
    refine Quiet.step_of (by change (0x80003f70#32).getLsbD 0=false;decide) rh2147499888 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) r9 0 [] [] = ⟨.ok c20 r9 [],[]⟩
    have v17 : c19.get 17=4096#32 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    rw [exec_opimm,v17]
    change Observed.interp B img o (.done (c19.wr 17 (alu .add (4096#32) (1147#32)) (c19.pc+4#32))) r9 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t20 : Quiet.Step B img ⟨c20,r9⟩ ⟨c21,r9⟩ := by
    refine Quiet.step_of (by change (0x80003f74#32).getLsbD 0=false;decide) rh2147499892 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) r9 0 [] [] = ⟨.ok c21 r9 [],[]⟩
    have v5 : c20.get 5=(((BitVec.ofNat 32 status)) >>> 2) := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    have v17 : c20.get 17=5243#32 := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    rw [HttpDecMath.exec_muldiv,v5,v17]
    change Observed.interp B img o (.done (c20.wr 17 (muldiv .mul ((((BitVec.ofNat 32 status)) >>> 2)) (5243#32)) (c20.pc+4#32))) r9 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t21 : Quiet.Step B img ⟨c21,r9⟩ ⟨c22,r9⟩ := by
    refine Quiet.step_of (by change (0x80003f78#32).getLsbD 0=false;decide) rh2147499896 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) r9 0 [] [] = ⟨.ok c22 r9 [],[]⟩
    have v17 : c21.get 17=(((((BitVec.ofNat 32 status)) >>> 2))*(5243#32)) := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    rw [exec_opimm,v17]
    change Observed.interp B img o (.done (c21.wr 17 (alu .srl ((((((BitVec.ofNat 32 status)) >>> 2))*(5243#32))) (17#32)) (c21.pc+4#32))) r9 0 [] [] = _
    rw [(show alu .srl ((((((BitVec.ofNat 32 status)) >>> 2))*(5243#32))) (17#32)=(BitVec.ofNat 32 (status/100)) from ResponseHeadMath.quotient100 status hhi)]
    first | rfl | (rw [hp]; rfl)
  have t22 : Quiet.Step B img ⟨c22,r9⟩ ⟨c23,r9⟩ := by
    refine Quiet.step_of (by change (0x80003f7c#32).getLsbD 0=false;decide) rh2147499900 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) r9 0 [] [] = ⟨.ok c23 r9 [],[]⟩
    have v17 : c22.get 17=(BitVec.ofNat 32 (status/100)) := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
    rw [exec_opimm,v17]
    change Observed.interp B img o (.done (c22.wr 5 (alu .or ((BitVec.ofNat 32 (status/100))) (48#32)) (c22.pc+4#32))) r9 0 [] [] = _
    rw [(show alu .or ((BitVec.ofNat 32 (status/100))) (48#32)=(BitVec.ofNat 32 (48+status/100)) from HttpDecMath.ascii_or (status/100) (by omega))]
    first | rfl | (rw [hp]; rfl)
  have t23 : Quiet.Step B img ⟨c23,r9⟩ ⟨c24,r9⟩ := by
    refine Quiet.step_of (by change (0x80003f80#32).getLsbD 0=false;decide) rh2147499904 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) r9 0 [] [] = ⟨.ok c24 r9 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c23.wr 17 (alu .add (0#32) (11#32)) (c23.pc+2#32))) r9 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  refine ⟨c24,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.single t23))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
  · simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
  · simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
  · simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
  · simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17]
  · intro reg h5 h6 h7 h28 h17;simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h13,h14,h15,h16,h17,h5,h6,h7,h28,h17]
end E5R.Thermostat.ResponseHeadPrefixPart0
