import Projects.thermostat.HttpDecCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HttpDecOnesMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HttpDecOnes
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) (n count : Nat) :=
  ramWrite (ram) (sp+BitVec.ofNat 32 (4+count)) (HttpDecOnesMath.byteWord n) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (n count : Nat) (hn : n≤832) (hc : count≤2) (h2 : c.get 2=sp) (h13 : c.get 13=BitVec.ofNat 32 n) (h15 : c.get 15=BitVec.ofNat 32 count) (hm : Memory.Block B sp 16)
    (hp : c.pc=0x800043a6#32) :
    ∃ d, Quiet.Steps B img 13 ⟨c,ram⟩ ⟨d,memory ram sp n count⟩ ∧ d.pc=0x800043d6#32 ∧
      d.get 14=0#32 ∧ d.get 16=sp+BitVec.ofNat 32 (4+count) ∧ d.get 17=((HttpDecOnesMath.high n) &&& 248#32) ∧ d.get 13=HttpDecOnesMath.byteWord n ∧ (∀ r : Reg, r≠14 → r≠16 → r≠17 → r≠13 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (0#32) 0x800043a8#32
  let c2 := c1.wr 16 (3435974656#32) 0x800043ac#32
  let c3 := c2.wr 16 (3435973837#32) 0x800043b0#32
  let c4 := c3.wr 16 ((HttpDecOnesMath.high n)) 0x800043b4#32
  let c5 := c4.wr 17 (((HttpDecOnesMath.high n) &&& 248#32)) 0x800043b8#32
  let c6 := c5.wr 16 (((HttpDecOnesMath.high n) >>> 2)) 0x800043bc#32
  let c7 := c6.wr 13 (((BitVec.ofNat 32 n)-((HttpDecOnesMath.high n) &&& 248#32))) 0x800043c0#32
  let c8 := c7.wr 16 ((((HttpDecOnesMath.high n) >>> 2) &&& 0xfffffffe#32)) 0x800043c4#32
  let c9 := c8.wr 13 ((((BitVec.ofNat 32 n)-((HttpDecOnesMath.high n) &&& 248#32))-(((HttpDecOnesMath.high n) >>> 2) &&& 0xfffffffe#32))) 0x800043c8#32
  let c10 := c9.wr 16 (sp+4#32) 0x800043cc#32
  let c11 := c10.wr 16 (sp+BitVec.ofNat 32 (4+count)) 0x800043ce#32
  let c12 := c11.wr 13 (HttpDecOnesMath.byteWord n) 0x800043d2#32
  let r1 := ramWrite ram (sp+BitVec.ofNat 32 (4+count)) (HttpDecOnesMath.byteWord n) .b
  let c13 := c12.goto 0x800043d6#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact de2147500966) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800043a8#32).getLsbD 0=false;decide) de2147500968 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800043ac#32).getLsbD 0=false;decide) de2147500972 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v16 : c2.get 16=3435974656#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15]
    rw [exec_opimm,v16];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800043b0#32).getLsbD 0=false;decide) de2147500976 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v13 : c3.get 13=(BitVec.ofNat 32 n) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15]
    have v16 : c3.get 16=3435973837#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15]
    rw [HttpDecMath.exec_muldiv,v13,v16];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800043b4#32).getLsbD 0=false;decide) de2147500980 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v16 : c4.get 16=(HttpDecOnesMath.high n) := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15]
    rw [exec_opimm,v16];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800043b8#32).getLsbD 0=false;decide) de2147500984 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v16 : c5.get 16=(HttpDecOnesMath.high n) := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15]
    rw [exec_opimm,v16];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x800043bc#32).getLsbD 0=false;decide) de2147500988 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v13 : c6.get 13=(BitVec.ofNat 32 n) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15]
    have v17 : c6.get 17=((HttpDecOnesMath.high n) &&& 248#32) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15]
    rw [exec_op,v13,v17];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x800043c0#32).getLsbD 0=false;decide) de2147500992 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v16 : c7.get 16=((HttpDecOnesMath.high n) >>> 2) := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15]
    rw [exec_opimm,v16];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x800043c4#32).getLsbD 0=false;decide) de2147500996 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v13 : c8.get 13=((BitVec.ofNat 32 n)-((HttpDecOnesMath.high n) &&& 248#32)) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15]
    have v16 : c8.get 16=(((HttpDecOnesMath.high n) >>> 2) &&& 0xfffffffe#32) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15]
    rw [exec_op,v13,v16];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x800043c8#32).getLsbD 0=false;decide) de2147501000 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v2 : c9.get 2=sp := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x800043cc#32).getLsbD 0=false;decide) de2147501004 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v16 : c10.get 16=sp+4#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15]
    have v15 : c10.get 15=BitVec.ofNat 32 count := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15]
    rw [exec_op,v16,v15]
    change Observed.interp B img o (.done (c10.wr 16 ((sp+4#32)+BitVec.ofNat 32 count) 0x800043ce#32)) ram 0 [] [] = _
    rw [BitVec.add_assoc,←BitVec.ofNat_add];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x800043ce#32).getLsbD 0=false;decide) de2147501006 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v13 : c11.get 13=(((BitVec.ofNat 32 n)-((HttpDecOnesMath.high n) &&& 248#32))-(((HttpDecOnesMath.high n) >>> 2) &&& 0xfffffffe#32)) := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15]
    rw [exec_opimm,v13];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,r1⟩ := by
    refine Quiet.step_of (by change (0x800043d2#32).getLsbD 0=false;decide) de2147501010 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 r1 [],[]⟩
    have v16 : c12.get 16=sp+BitVec.ofNat 32 (4+count) := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15]
    have v13 : c12.get 13=HttpDecOnesMath.byteWord n := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15]
    rw [exec_store,v16,v13,BitVec.add_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 4+count) (by decide) (by change 4+count+1≤16;omega))];first | rfl | (rw [hp];rfl)
  refine ⟨c13,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.single t12)))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15]
  · intro reg h14 h16 h17 h13;simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h15,h14,h16,h17,h13]
end E5R.Thermostat.HttpDecOnes
