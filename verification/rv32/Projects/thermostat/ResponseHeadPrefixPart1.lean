import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.ResponseHeadMath
import Projects.thermostat.HttpDecTensMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseHeadPrefixPart1
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat) :=
  ramWrite (ramWrite (ramWrite (ram) (dst+9#32) ((BitVec.ofNat 32 (48+status/100))) .b) (dst+10#32) ((BitVec.ofNat 32 (48+(status/10)%10))) .b) (dst+11#32) ((BitVec.ofNat 32 (48+status%10))) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat) (hlo : 100≤status) (hhi : status≤599) (hct : ctlen≤16) (h2 : c.get 2=(frame+16#32)) (h5 : c.get 5=(BitVec.ofNat 32 (48+status/100))) (h6 : c.get 6=49#32) (h7 : c.get 7=46#32) (h10 : c.get 10=dst) (h11 : c.get 11=192#32) (h12 : c.get 12=(BitVec.ofNat 32 status)) (h13 : c.get 13=ctptr) (h14 : c.get 14=(BitVec.ofNat 32 ctlen)) (h15 : c.get 15=body) (h16 : c.get 16=flag) (h17 : c.get 17=11#32) (h28 : c.get 28=32#32) (hstack : Memory.Block B frame 96) (ha : frame.toNat%4=0) (hdst : Memory.Block B dst 192)
    (hp : c.pc=0x80003f82#32) :
    ∃ d, Quiet.Steps B img 24 ⟨c,ram⟩ ⟨d,memory ram frame dst ctptr body flag status ctlen⟩ ∧ d.pc=0x80003fd4#32 ∧
      d.get 5=13#32 ∧ d.get 6=(BitVec.ofNat 32 (48+(status/10)%10)) ∧ d.get 7=(((BitVec.ofNat 32 (status/100))) <<< 1) ∧ d.get 17=(BitVec.ofNat 32 (48+status%10)) ∧ (∀ r : Reg, r≠5 → r≠6 → r≠7 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  let r1 := ramWrite ram (dst+9#32) ((BitVec.ofNat 32 (48+status/100))) .b
  let c1 := c.goto 0x80003f86#32
  let c2 := c1.goto 0x80003f8a#32
  let c3 := c2.wr 5 (53248#32) 0x80003f8c#32
  let c4 := c3.wr 5 (52429#32) 0x80003f90#32
  let c5 := c4.wr 5 ((((BitVec.ofNat 32 status))*(52429#32))) 0x80003f94#32
  let c6 := c5.wr 6 (8192#32) 0x80003f96#32
  let c7 := c6.wr 5 ((BitVec.ofNat 32 (status/10))) 0x80003f9a#32
  let c8 := c7.wr 6 (6554#32) 0x80003f9e#32
  let c9 := c8.wr 6 ((((BitVec.ofNat 32 (status/10)))*(6554#32))) 0x80003fa2#32
  let c10 := c9.wr 6 ((BitVec.ofNat 32 (status/100))) 0x80003fa6#32
  let c11 := c10.wr 7 ((((BitVec.ofNat 32 (status/100))) <<< 1)) 0x80003faa#32
  let c12 := c11.wr 6 ((((BitVec.ofNat 32 (status/100))) <<< 3)) 0x80003fac#32
  let c13 := c12.wr 6 ((((((BitVec.ofNat 32 (status/100))) <<< 3)) + ((((BitVec.ofNat 32 (status/100))) <<< 1)))) 0x80003fae#32
  let c14 := c13.wr 6 ((HttpDecTensMath.word status)) 0x80003fb2#32
  let c15 := c14.wr 6 ((BitVec.ofNat 32 (48+(status/10)%10))) 0x80003fb6#32
  let r2 := ramWrite r1 (dst+10#32) ((BitVec.ofNat 32 (48+(status/10)%10))) .b
  let c16 := c15.goto 0x80003fba#32
  let c17 := c16.goto 0x80003fbe#32
  let c18 := c17.wr 17 ((((BitVec.ofNat 32 (status/10))) <<< 1)) 0x80003fc2#32
  let c19 := c18.wr 5 ((((BitVec.ofNat 32 (status/10))) <<< 3)) 0x80003fc4#32
  let c20 := c19.wr 17 ((((((BitVec.ofNat 32 (status/10))) <<< 1)) + ((((BitVec.ofNat 32 (status/10))) <<< 3)))) 0x80003fc6#32
  let c21 := c20.wr 17 ((ResponseHeadMath.ones status)) 0x80003fca#32
  let c22 := c21.wr 17 ((BitVec.ofNat 32 (48+status%10))) 0x80003fce#32
  let c23 := c22.wr 5 (13#32) 0x80003fd0#32
  let r3 := ramWrite r2 (dst+11#32) ((BitVec.ofNat 32 (48+status%10))) .b
  let c24 := c23.goto 0x80003fd4#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,r1⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147499906) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 r1 [],[]⟩
    have v10 : c.get 10=dst := by simp [Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    have v5 : c.get 5=(BitVec.ofNat 32 (48+status/100)) := by simp [Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_store,v10,v5]
    rw [Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hdst (off := 9) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,r1⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x80003f86#32).getLsbD 0=false;decide) rh2147499910 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) r1 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v11 : c1.get 11=192#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    have v17 : c1.get 17=11#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_branch,v11,v17,(by decide +kernel : taken .ltu (192#32) (11#32)=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r1⟩ := by
    refine Quiet.step_of (by change (0x80003f8a#32).getLsbD 0=false;decide) rh2147499914 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r1 [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r1⟩ ⟨c4,r1⟩ := by
    refine Quiet.step_of (by change (0x80003f8c#32).getLsbD 0=false;decide) rh2147499916 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r1 0 [] [] = ⟨.ok c4 r1 [],[]⟩
    have v5 : c3.get 5=53248#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_opimm,v5]
    change Observed.interp B img o (.done (c3.wr 5 (alu .add (53248#32) (4294966477#32)) (c3.pc+4#32))) r1 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t4 : Quiet.Step B img ⟨c4,r1⟩ ⟨c5,r1⟩ := by
    refine Quiet.step_of (by change (0x80003f90#32).getLsbD 0=false;decide) rh2147499920 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r1 0 [] [] = ⟨.ok c5 r1 [],[]⟩
    have v12 : c4.get 12=(BitVec.ofNat 32 status) := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    have v5 : c4.get 5=52429#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [HttpDecMath.exec_muldiv,v12,v5]
    change Observed.interp B img o (.done (c4.wr 5 (muldiv .mul ((BitVec.ofNat 32 status)) (52429#32)) (c4.pc+4#32))) r1 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t5 : Quiet.Step B img ⟨c5,r1⟩ ⟨c6,r1⟩ := by
    refine Quiet.step_of (by change (0x80003f94#32).getLsbD 0=false;decide) rh2147499924 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r1 0 [] [] = ⟨.ok c6 r1 [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r1⟩ ⟨c7,r1⟩ := by
    refine Quiet.step_of (by change (0x80003f96#32).getLsbD 0=false;decide) rh2147499926 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r1 0 [] [] = ⟨.ok c7 r1 [],[]⟩
    have v5 : c6.get 5=(((BitVec.ofNat 32 status))*(52429#32)) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_opimm,v5]
    change Observed.interp B img o (.done (c6.wr 5 (alu .srl ((((BitVec.ofNat 32 status))*(52429#32))) (19#32)) (c6.pc+4#32))) r1 0 [] [] = _
    rw [(show alu .srl ((((BitVec.ofNat 32 status))*(52429#32))) (19#32)=(BitVec.ofNat 32 (status/10)) from ResponseHeadMath.quotient10 status hhi)]
    first | rfl | (rw [hp]; rfl)
  have t7 : Quiet.Step B img ⟨c7,r1⟩ ⟨c8,r1⟩ := by
    refine Quiet.step_of (by change (0x80003f9a#32).getLsbD 0=false;decide) rh2147499930 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r1 0 [] [] = ⟨.ok c8 r1 [],[]⟩
    have v6 : c7.get 6=8192#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_opimm,v6]
    change Observed.interp B img o (.done (c7.wr 6 (alu .add (8192#32) (4294965658#32)) (c7.pc+4#32))) r1 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t8 : Quiet.Step B img ⟨c8,r1⟩ ⟨c9,r1⟩ := by
    refine Quiet.step_of (by change (0x80003f9e#32).getLsbD 0=false;decide) rh2147499934 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r1 0 [] [] = ⟨.ok c9 r1 [],[]⟩
    have v5 : c8.get 5=(BitVec.ofNat 32 (status/10)) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    have v6 : c8.get 6=6554#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [HttpDecMath.exec_muldiv,v5,v6]
    change Observed.interp B img o (.done (c8.wr 6 (muldiv .mul ((BitVec.ofNat 32 (status/10))) (6554#32)) (c8.pc+4#32))) r1 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t9 : Quiet.Step B img ⟨c9,r1⟩ ⟨c10,r1⟩ := by
    refine Quiet.step_of (by change (0x80003fa2#32).getLsbD 0=false;decide) rh2147499938 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r1 0 [] [] = ⟨.ok c10 r1 [],[]⟩
    have v6 : c9.get 6=(((BitVec.ofNat 32 (status/10)))*(6554#32)) := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_opimm,v6]
    change Observed.interp B img o (.done (c9.wr 6 (alu .srl ((((BitVec.ofNat 32 (status/10)))*(6554#32))) (16#32)) (c9.pc+4#32))) r1 0 [] [] = _
    rw [(show alu .srl ((((BitVec.ofNat 32 (status/10)))*(6554#32))) (16#32)=(BitVec.ofNat 32 (status/100)) from ResponseHeadMath.tens_quotient status hhi)]
    first | rfl | (rw [hp]; rfl)
  have t10 : Quiet.Step B img ⟨c10,r1⟩ ⟨c11,r1⟩ := by
    refine Quiet.step_of (by change (0x80003fa6#32).getLsbD 0=false;decide) rh2147499942 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r1 0 [] [] = ⟨.ok c11 r1 [],[]⟩
    have v6 : c10.get 6=(BitVec.ofNat 32 (status/100)) := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_opimm,v6]
    change Observed.interp B img o (.done (c10.wr 7 (alu .sll ((BitVec.ofNat 32 (status/100))) (1#32)) (c10.pc+4#32))) r1 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t11 : Quiet.Step B img ⟨c11,r1⟩ ⟨c12,r1⟩ := by
    refine Quiet.step_of (by change (0x80003faa#32).getLsbD 0=false;decide) rh2147499946 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r1 0 [] [] = ⟨.ok c12 r1 [],[]⟩
    have v6 : c11.get 6=(BitVec.ofNat 32 (status/100)) := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_opimm,v6]
    change Observed.interp B img o (.done (c11.wr 6 (alu .sll ((BitVec.ofNat 32 (status/100))) (3#32)) (c11.pc+2#32))) r1 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t12 : Quiet.Step B img ⟨c12,r1⟩ ⟨c13,r1⟩ := by
    refine Quiet.step_of (by change (0x80003fac#32).getLsbD 0=false;decide) rh2147499948 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r1 0 [] [] = ⟨.ok c13 r1 [],[]⟩
    have v6 : c12.get 6=(((BitVec.ofNat 32 (status/100))) <<< 3) := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    have v7 : c12.get 7=(((BitVec.ofNat 32 (status/100))) <<< 1) := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_op,v6,v7]
    change Observed.interp B img o (.done (c12.wr 6 (alu .add ((((BitVec.ofNat 32 (status/100))) <<< 3)) ((((BitVec.ofNat 32 (status/100))) <<< 1))) (c12.pc+2#32))) r1 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t13 : Quiet.Step B img ⟨c13,r1⟩ ⟨c14,r1⟩ := by
    refine Quiet.step_of (by change (0x80003fae#32).getLsbD 0=false;decide) rh2147499950 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r1 0 [] [] = ⟨.ok c14 r1 [],[]⟩
    have v5 : c13.get 5=(BitVec.ofNat 32 (status/10)) := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    have v6 : c13.get 6=(((((BitVec.ofNat 32 (status/100))) <<< 3)) + ((((BitVec.ofNat 32 (status/100))) <<< 1))) := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_op,v5,v6]
    change Observed.interp B img o (.done (c13.wr 6 (alu .sub ((BitVec.ofNat 32 (status/10))) ((((((BitVec.ofNat 32 (status/100))) <<< 3)) + ((((BitVec.ofNat 32 (status/100))) <<< 1))))) (c13.pc+4#32))) r1 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t14 : Quiet.Step B img ⟨c14,r1⟩ ⟨c15,r1⟩ := by
    refine Quiet.step_of (by change (0x80003fb2#32).getLsbD 0=false;decide) rh2147499954 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) r1 0 [] [] = ⟨.ok c15 r1 [],[]⟩
    have v6 : c14.get 6=(HttpDecTensMath.word status) := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_opimm,v6]
    change Observed.interp B img o (.done (c14.wr 6 (alu .or ((HttpDecTensMath.word status)) (48#32)) (c14.pc+4#32))) r1 0 [] [] = _
    rw [(by change (HttpDecTensMath.word status ||| 48#32)=_;rw [HttpDecTensMath.value status (by omega)];exact HttpDecMath.ascii_or _ (Nat.mod_lt _ (by decide)) : alu .or ((HttpDecTensMath.word status)) (48#32)=(BitVec.ofNat 32 (48+(status/10)%10)))]
    first | rfl | (rw [hp]; rfl)
  have t15 : Quiet.Step B img ⟨c15,r1⟩ ⟨c16,r2⟩ := by
    refine Quiet.step_of (by change (0x80003fb6#32).getLsbD 0=false;decide) rh2147499958 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) r1 0 [] [] = ⟨.ok c16 r2 [],[]⟩
    have v10 : c15.get 10=dst := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    have v6 : c15.get 6=(BitVec.ofNat 32 (48+(status/10)%10)) := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_store,v10,v6]
    rw [Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hdst (off := 10) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,r2⟩ ⟨c17,r2⟩ := by
    refine Quiet.step_of (by change (0x80003fba#32).getLsbD 0=false;decide) rh2147499962 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) r2 0 [] [] = ⟨.ok c17 r2 [],[]⟩
    have v11 : c16.get 11=192#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    have v17 : c16.get 17=11#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_branch,v11,v17,(by decide +kernel : taken .eq (192#32) (11#32)=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,r2⟩ ⟨c18,r2⟩ := by
    refine Quiet.step_of (by change (0x80003fbe#32).getLsbD 0=false;decide) rh2147499966 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) r2 0 [] [] = ⟨.ok c18 r2 [],[]⟩
    have v5 : c17.get 5=(BitVec.ofNat 32 (status/10)) := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_opimm,v5]
    change Observed.interp B img o (.done (c17.wr 17 (alu .sll ((BitVec.ofNat 32 (status/10))) (1#32)) (c17.pc+4#32))) r2 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t18 : Quiet.Step B img ⟨c18,r2⟩ ⟨c19,r2⟩ := by
    refine Quiet.step_of (by change (0x80003fc2#32).getLsbD 0=false;decide) rh2147499970 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) r2 0 [] [] = ⟨.ok c19 r2 [],[]⟩
    have v5 : c18.get 5=(BitVec.ofNat 32 (status/10)) := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_opimm,v5]
    change Observed.interp B img o (.done (c18.wr 5 (alu .sll ((BitVec.ofNat 32 (status/10))) (3#32)) (c18.pc+2#32))) r2 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t19 : Quiet.Step B img ⟨c19,r2⟩ ⟨c20,r2⟩ := by
    refine Quiet.step_of (by change (0x80003fc4#32).getLsbD 0=false;decide) rh2147499972 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) r2 0 [] [] = ⟨.ok c20 r2 [],[]⟩
    have v17 : c19.get 17=(((BitVec.ofNat 32 (status/10))) <<< 1) := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    have v5 : c19.get 5=(((BitVec.ofNat 32 (status/10))) <<< 3) := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_op,v17,v5]
    change Observed.interp B img o (.done (c19.wr 17 (alu .add ((((BitVec.ofNat 32 (status/10))) <<< 1)) ((((BitVec.ofNat 32 (status/10))) <<< 3))) (c19.pc+2#32))) r2 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t20 : Quiet.Step B img ⟨c20,r2⟩ ⟨c21,r2⟩ := by
    refine Quiet.step_of (by change (0x80003fc6#32).getLsbD 0=false;decide) rh2147499974 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) r2 0 [] [] = ⟨.ok c21 r2 [],[]⟩
    have v12 : c20.get 12=(BitVec.ofNat 32 status) := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    have v17 : c20.get 17=(((((BitVec.ofNat 32 (status/10))) <<< 1)) + ((((BitVec.ofNat 32 (status/10))) <<< 3))) := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_op,v12,v17]
    change Observed.interp B img o (.done (c20.wr 17 (alu .sub ((BitVec.ofNat 32 status)) ((((((BitVec.ofNat 32 (status/10))) <<< 1)) + ((((BitVec.ofNat 32 (status/10))) <<< 3))))) (c20.pc+4#32))) r2 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t21 : Quiet.Step B img ⟨c21,r2⟩ ⟨c22,r2⟩ := by
    refine Quiet.step_of (by change (0x80003fca#32).getLsbD 0=false;decide) rh2147499978 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) r2 0 [] [] = ⟨.ok c22 r2 [],[]⟩
    have v17 : c21.get 17=(ResponseHeadMath.ones status) := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_opimm,v17]
    change Observed.interp B img o (.done (c21.wr 17 (alu .or ((ResponseHeadMath.ones status)) (48#32)) (c21.pc+4#32))) r2 0 [] [] = _
    rw [(by change (ResponseHeadMath.ones status ||| 48#32)=_;rw [ResponseHeadMath.ones_value status hhi];exact HttpDecMath.ascii_or _ (Nat.mod_lt _ (by decide)) : alu .or ((ResponseHeadMath.ones status)) (48#32)=(BitVec.ofNat 32 (48+status%10)))]
    first | rfl | (rw [hp]; rfl)
  have t22 : Quiet.Step B img ⟨c22,r2⟩ ⟨c23,r2⟩ := by
    refine Quiet.step_of (by change (0x80003fce#32).getLsbD 0=false;decide) rh2147499982 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) r2 0 [] [] = ⟨.ok c23 r2 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c22.wr 5 (alu .add (0#32) (13#32)) (c22.pc+2#32))) r2 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t23 : Quiet.Step B img ⟨c23,r2⟩ ⟨c24,r3⟩ := by
    refine Quiet.step_of (by change (0x80003fd0#32).getLsbD 0=false;decide) rh2147499984 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) r2 0 [] [] = ⟨.ok c24 r3 [],[]⟩
    have v10 : c23.get 10=dst := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    have v17 : c23.get 17=(BitVec.ofNat 32 (48+status%10)) := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_store,v10,v17]
    rw [Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hdst (off := 11) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c24,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.single t23))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
  · simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
  · simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
  · simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
  · intro reg h5 h6 h7 h17;simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28,h5,h6,h7,h17]
end E5R.Thermostat.ResponseHeadPrefixPart1
