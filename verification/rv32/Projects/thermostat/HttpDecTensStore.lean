import Projects.thermostat.HttpDecCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HttpDecMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HttpDecTensStore
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) (n index : Nat) :=
  ramWrite (ram) (sp+BitVec.ofNat 32 (4+index)) (BitVec.ofNat 32 (48+(n/10)%10)) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (n index : Nat) (hi : index≤1) (h2 : c.get 2=sp)
    (h14 : c.get 14=BitVec.ofNat 32 index) (h16 : c.get 16=BitVec.ofNat 32 ((n/10)%10))
    (hm : Memory.Block B sp 16)
    (hp : c.pc=0x80004396#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,memory ram sp n index⟩ ∧ d.pc=0x800043a6#32 ∧
      d.get 15=BitVec.ofNat 32 (index+1) ∧ d.get 16=BitVec.ofNat 32 (48+(n/10)%10) ∧ (∀ r : Reg, r≠15 → r≠16 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 15 (sp+4#32) 0x80004398#32
  let c2 := c1.wr 15 (sp+BitVec.ofNat 32 (4+index)) 0x8000439a#32
  let c3 := c2.wr 16 (BitVec.ofNat 32 (48+(n/10)%10)) 0x8000439e#32
  let r1 := ramWrite ram (sp+BitVec.ofNat 32 (4+index)) (BitVec.ofNat 32 (48+(n/10)%10)) .b
  let c4 := c3.goto 0x800043a2#32
  let c5 := c4.wr 15 (BitVec.ofNat 32 (index+1)) 0x800043a6#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact de2147500950) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h2,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80004398#32).getLsbD 0=false;decide) de2147500952 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v15 : c1.get 15=sp+4#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h14,h16]
    have v14 : c1.get 14=BitVec.ofNat 32 index := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h14,h16]
    rw [exec_op,v15,v14]
    change Observed.interp B img o (.done (c1.wr 15 ((sp+4#32)+BitVec.ofNat 32 index) 0x8000439a#32)) ram 0 [] [] = _
    rw [BitVec.add_assoc,←BitVec.ofNat_add];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000439a#32).getLsbD 0=false;decide) de2147500954 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v16 : c2.get 16=BitVec.ofNat 32 ((n/10)%10) := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h14,h16]
    rw [exec_opimm,v16]
    change Observed.interp B img o (.done (c2.wr 16 ((BitVec.ofNat 32 ((n/10)%10)) ||| 48#32) 0x8000439e#32)) ram 0 [] [] = _
    rw [HttpDecMath.ascii_or ((n/10)%10) (Nat.mod_lt _ (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,r1⟩ := by
    refine Quiet.step_of (by change (0x8000439e#32).getLsbD 0=false;decide) de2147500958 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 r1 [],[]⟩
    have v15 : c3.get 15=sp+BitVec.ofNat 32 (4+index) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h14,h16]
    have v16 : c3.get 16=BitVec.ofNat 32 (48+(n/10)%10) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h14,h16]
    rw [exec_store,v15,v16,BitVec.add_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 4+index) (by decide) (by change 4+index+1≤16;omega))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r1⟩ ⟨c5,r1⟩ := by
    refine Quiet.step_of (by change (0x800043a2#32).getLsbD 0=false;decide) de2147500962 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r1 0 [] [] = ⟨.ok c5 r1 [],[]⟩
    have v14 : c4.get 14=BitVec.ofNat 32 index := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h14,h16]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c4.wr 15 ((BitVec.ofNat 32 index)+1#32) 0x800043a6#32)) r1 0 [] [] = _
    rw [←BitVec.ofNat_add];first | rfl | (rw [hp];rfl)
  refine ⟨c5,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h14,h16]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h14,h16]
  · intro reg h15 h16;simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h14,h16,h15,h16]
end E5R.Thermostat.HttpDecTensStore
