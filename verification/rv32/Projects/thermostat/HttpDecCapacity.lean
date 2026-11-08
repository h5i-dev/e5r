import Projects.thermostat.HttpDecCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HttpDecMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HttpDecCapacity
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp dst : Word) (pos count : Nat) (hpos : pos≤94) (hcount : count≤2)
    (h2 : c.get 2=sp) (h10 : c.get 10=dst) (h11 : c.get 11=192#32)
    (h12 : c.get 12=BitVec.ofNat 32 pos) (h15 : c.get 15=BitVec.ofNat 32 count)
    (hp : c.pc=0x800043d6#32) :
    ∃ d, Quiet.Steps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800043ee#32 ∧
      d.get 13=sp+4#32 ∧ d.get 11=BitVec.ofNat 32 (pos+count) ∧ d.get 12=dst+BitVec.ofNat 32 pos ∧ d.get 10=dst+BitVec.ofNat 32 (pos+count+1) ∧ (∀ r : Reg, r≠13 → r≠11 → r≠12 → r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x800043da#32
  let c2 := c1.wr 13 (192#32-BitVec.ofNat 32 pos) 0x800043de#32
  let c3 := c2.goto 0x800043e2#32
  let c4 := c3.wr 11 (BitVec.ofNat 32 (pos+count)) 0x800043e6#32
  let c5 := c4.wr 12 (dst+BitVec.ofNat 32 pos) 0x800043e8#32
  let c6 := c5.wr 10 (dst+BitVec.ofNat 32 (pos+count)) 0x800043ea#32
  let c7 := c6.wr 10 (dst+BitVec.ofNat 32 (pos+count+1)) 0x800043ec#32
  let c8 := c7.wr 13 (sp+4#32) 0x800043ee#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact de2147501014) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_branch,h11,h12,(show taken .ltu 192#32 (BitVec.ofNat 32 pos)=false by rw [HttpDecMath.branch_ltu 192 pos (by decide) (by omega)];exact decide_eq_false (by omega))]
    simp only [Bool.false_eq_true,ite_false];rw [hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800043da#32).getLsbD 0=false;decide) de2147501018 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v11 : c1.get 11=192#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h15]
    have v12 : c1.get 12=BitVec.ofNat 32 pos := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h15]
    rw [exec_op,v11,v12];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800043de#32).getLsbD 0=false;decide) de2147501022 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v15 : c2.get 15=BitVec.ofNat 32 count := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h15]
    have v13 : c2.get 13=192#32-BitVec.ofNat 32 pos := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h15]
    rw [exec_branch,v15,v13,HttpDecMath.remaining_guard pos count hpos hcount]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800043e2#32).getLsbD 0=false;decide) de2147501026 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v15 : c3.get 15=BitVec.ofNat 32 count := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h15]
    have v12 : c3.get 12=BitVec.ofNat 32 pos := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h15]
    rw [exec_op,v15,v12]
    change Observed.interp B img o (.done (c3.wr 11 ((BitVec.ofNat 32 count)+(BitVec.ofNat 32 pos)) 0x800043e6#32)) ram 0 [] [] = _
    rw [←BitVec.ofNat_add,Nat.add_comm count pos];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800043e6#32).getLsbD 0=false;decide) de2147501030 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v12 : c4.get 12=BitVec.ofNat 32 pos := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h15]
    have v10 : c4.get 10=dst := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h15]
    rw [exec_op,v12,v10]
    change Observed.interp B img o (.done (c4.wr 12 ((BitVec.ofNat 32 pos)+dst) 0x800043e8#32)) ram 0 [] [] = _
    rw [BitVec.add_comm (BitVec.ofNat 32 pos) dst];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800043e8#32).getLsbD 0=false;decide) de2147501032 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v10 : c5.get 10=dst := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h15]
    have v11 : c5.get 11=BitVec.ofNat 32 (pos+count) := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h15]
    rw [exec_op,v10,v11];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x800043ea#32).getLsbD 0=false;decide) de2147501034 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v10 : c6.get 10=dst+BitVec.ofNat 32 (pos+count) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h15]
    rw [exec_opimm,v10]
    change Observed.interp B img o (.done (c6.wr 10 ((dst+BitVec.ofNat 32 (pos+count))+1#32) 0x800043ec#32)) ram 0 [] [] = _
    rw [BitVec.add_assoc,←BitVec.ofNat_add];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x800043ec#32).getLsbD 0=false;decide) de2147501036 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v2 : c7.get 2=sp := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h15]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  refine ⟨c8,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.single t7))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h15]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h15]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h15]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h15]
  · intro reg h13 h11 h12 h10;simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h11,h12,h15,h13,h11,h12,h10]
end E5R.Thermostat.HttpDecCapacity
