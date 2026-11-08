import Projects.thermostat.HttpDecCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HttpDecTensMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HttpDecBigTens
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) (n : Nat) :=
  ramWrite (ram) (sp+4#32) (BitVec.ofNat 32 (48+n/100)) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (n : Nat) (hn : n≤832) (hbig : 100≤n) (h2 : c.get 2=sp)
    (h13 : c.get 13=BitVec.ofNat 32 n) (h14 : c.get 14=BitVec.ofNat 32 (n/100)) (h15 : c.get 15=0#32)
    (hm : Memory.Block B sp 16)
    (hp : c.pc=0x8000435c#32) :
    ∃ d, Quiet.Steps B img 16 ⟨c,ram⟩ ⟨d,memory ram sp n⟩ ∧ d.pc=0x80004396#32 ∧
      d.get 16=HttpDecTensMath.word n ∧ d.get 17=(((BitVec.ofNat 32 (n/100)) <<< 3)+((BitVec.ofNat 32 (n/100)) <<< 1)) ∧ d.get 5=sp+4#32 ∧ d.get 14=1#32 ∧ d.get 6=((BitVec.ofNat 32 (n/100)) <<< 1) ∧ (∀ r : Reg, r≠16 → r≠17 → r≠5 → r≠14 → r≠6 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 16 (3435974656#32) 0x80004360#32
  let c2 := c1.wr 16 (3435973837#32) 0x80004364#32
  let c3 := c2.wr 16 (muldiv .mulhu (BitVec.ofNat 32 n) 3435973837#32) 0x80004368#32
  let c4 := c3.wr 17 (429498368#32) 0x8000436c#32
  let c5 := c4.wr 16 (BitVec.ofNat 32 (n/10)) 0x80004370#32
  let c6 := c5.wr 17 (429496730#32) 0x80004374#32
  let c7 := c6.wr 17 (BitVec.ofNat 32 (n/100)) 0x80004378#32
  let c8 := c7.wr 5 (sp+4#32) 0x8000437c#32
  let c9 := c8.wr 5 (sp+4#32) 0x8000437e#32
  let c10 := c9.wr 14 (BitVec.ofNat 32 (48+n/100)) 0x80004382#32
  let c11 := c10.wr 6 (((BitVec.ofNat 32 (n/100)) <<< 1)) 0x80004386#32
  let c12 := c11.wr 17 (((BitVec.ofNat 32 (n/100)) <<< 3)) 0x80004388#32
  let r1 := ramWrite ram (sp+4#32) (BitVec.ofNat 32 (48+n/100)) .b
  let c13 := c12.goto 0x8000438c#32
  let c14 := c13.wr 17 ((((BitVec.ofNat 32 (n/100)) <<< 3)+((BitVec.ofNat 32 (n/100)) <<< 1))) 0x8000438e#32
  let c15 := c14.wr 14 (1#32) 0x80004392#32
  let c16 := c15.wr 16 (HttpDecTensMath.word n) 0x80004396#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact de2147500892) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_lui,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80004360#32).getLsbD 0=false;decide) de2147500896 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v16 : c1.get 16=3435974656#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
    rw [exec_opimm,v16];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80004364#32).getLsbD 0=false;decide) de2147500900 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v13 : c2.get 13=BitVec.ofNat 32 n := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
    have v16 : c2.get 16=3435973837#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
    rw [HttpDecMath.exec_muldiv,v13,v16];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80004368#32).getLsbD 0=false;decide) de2147500904 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x8000436c#32).getLsbD 0=false;decide) de2147500908 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v16 : c4.get 16=muldiv .mulhu (BitVec.ofNat 32 n) 3435973837#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
    rw [exec_opimm,v16]
    change Observed.interp B img o (.done (c4.wr 16 ((muldiv .mulhu (BitVec.ofNat 32 n) 3435973837#32) >>> 3) 0x80004370#32)) ram 0 [] [] = _
    rw [HttpDecMath.quotient10 n hn];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80004370#32).getLsbD 0=false;decide) de2147500912 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v17 : c5.get 17=429498368#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
    rw [exec_opimm,v17];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80004374#32).getLsbD 0=false;decide) de2147500916 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v16 : c6.get 16=BitVec.ofNat 32 (n/10) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
    have v17 : c6.get 17=429496730#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
    rw [HttpDecMath.exec_muldiv,v16,v17,HttpDecTensMath.reciprocal n hn];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80004378#32).getLsbD 0=false;decide) de2147500920 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v2 : c7.get 2=sp := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x8000437c#32).getLsbD 0=false;decide) de2147500924 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v5 : c8.get 5=sp+4#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
    have v15 : c8.get 15=0#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
    rw [exec_op,v5,v15]
    change Observed.interp B img o (.done (c8.wr 5 ((sp+4#32)+0#32) 0x8000437e#32)) ram 0 [] [] = _
    rw [BitVec.add_zero];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x8000437e#32).getLsbD 0=false;decide) de2147500926 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v14 : c9.get 14=BitVec.ofNat 32 (n/100) := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c9.wr 14 ((BitVec.ofNat 32 (n/100)) ||| 48#32) 0x80004382#32)) ram 0 [] [] = _
    rw [HttpDecMath.ascii_or (n/100) (by omega)];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80004382#32).getLsbD 0=false;decide) de2147500930 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v17 : c10.get 17=BitVec.ofNat 32 (n/100) := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
    rw [exec_opimm,v17];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x80004386#32).getLsbD 0=false;decide) de2147500934 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v17 : c11.get 17=BitVec.ofNat 32 (n/100) := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
    rw [exec_opimm,v17];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,r1⟩ := by
    refine Quiet.step_of (by change (0x80004388#32).getLsbD 0=false;decide) de2147500936 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 r1 [],[]⟩
    have v5 : c12.get 5=sp+4#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
    have v14 : c12.get 14=BitVec.ofNat 32 (48+n/100) := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
    rw [exec_store,v5,v14,BitVec.add_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r1⟩ ⟨c14,r1⟩ := by
    refine Quiet.step_of (by change (0x8000438c#32).getLsbD 0=false;decide) de2147500940 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r1 0 [] [] = ⟨.ok c14 r1 [],[]⟩
    have v17 : c13.get 17=((BitVec.ofNat 32 (n/100)) <<< 3) := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
    have v6 : c13.get 6=((BitVec.ofNat 32 (n/100)) <<< 1) := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
    rw [exec_op,v17,v6];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,r1⟩ ⟨c15,r1⟩ := by
    refine Quiet.step_of (by change (0x8000438e#32).getLsbD 0=false;decide) de2147500942 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) r1 0 [] [] = ⟨.ok c15 r1 [],[]⟩
    have v15 : c14.get 15=0#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
    rw [exec_opimm,v15];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,r1⟩ ⟨c16,r1⟩ := by
    refine Quiet.step_of (by change (0x80004392#32).getLsbD 0=false;decide) de2147500946 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) r1 0 [] [] = ⟨.ok c16 r1 [],[]⟩
    have v16 : c15.get 16=BitVec.ofNat 32 (n/10) := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
    have v17 : c15.get 17=(((BitVec.ofNat 32 (n/100)) <<< 3)+((BitVec.ofNat 32 (n/100)) <<< 1)) := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
    rw [exec_op,v16,v17];first | rfl | (rw [hp];rfl)
  refine ⟨c16,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.single t15))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
  · simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
  · simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
  · simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
  · simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15]
  · intro reg h16 h17 h5 h14 h6;simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17,h5,h14,h6]
end E5R.Thermostat.HttpDecBigTens
