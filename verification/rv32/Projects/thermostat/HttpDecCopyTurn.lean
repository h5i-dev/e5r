import Projects.thermostat.HttpDecCode
import Projects.thermostat.QuietRam
import Projects.thermostat.ObservedByte
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HttpDecCopyTurn
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (src dst finish : Word) (v : BitVec 8) :=
  ramWrite (ram) (dst) (v.setWidth 32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst finish : Word) (v : BitVec 8) (last : Bool) (h12 : c.get 12=dst) (h13 : c.get 13=src) (h10 : c.get 10=finish)
    (hs : ReadBytes.Byte B img ram src v) (hm : B.inRam dst 1=true)
    (ht : taken .ne (dst+1#32) finish=(!last))
    (hp : c.pc=0x800043ee#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,memory ram src dst finish v⟩ ∧ d.pc=(if last then 0x800043fe#32 else 0x800043ee#32) ∧
      d.get 14=v.setWidth 32 ∧ d.get 12=dst+1#32 ∧ d.get 13=src+1#32 ∧ (∀ r : Reg, r≠14 → r≠12 → r≠13 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (v.setWidth 32) 0x800043f2#32
  let r1 := ramWrite ram (dst) (v.setWidth 32) .b
  let c2 := c1.goto 0x800043f6#32
  let c3 := c2.wr 12 (dst+1#32) 0x800043f8#32
  let c4 := c3.wr 13 (src+1#32) 0x800043fa#32
  let c5 := c4.goto (if last then 0x800043fe#32 else 0x800043ee#32)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact de2147501038) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h13,BitVec.add_zero,ObservedByte.load hs o _ 0 [] [],ReadBytes.extend_byte,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x800043f2#32).getLsbD 0=false;decide) de2147501042 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v12 : c1.get 12=dst := by simp [c1,Core.wr_get_ne,Core.wr_get,h12,h13,h10]
    have v14 : c1.get 14=v.setWidth 32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h12,h13,h10]
    rw [exec_store,v12,v14,BitVec.add_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hm];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r1⟩ := by
    refine Quiet.step_of (by change (0x800043f6#32).getLsbD 0=false;decide) de2147501046 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r1 [],[]⟩
    have hv : c2.get 12=dst := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h12,h13,h10]
    rw [exec_opimm,hv];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r1⟩ ⟨c4,r1⟩ := by
    refine Quiet.step_of (by change (0x800043f8#32).getLsbD 0=false;decide) de2147501048 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r1 0 [] [] = ⟨.ok c4 r1 [],[]⟩
    have hv : c3.get 13=src := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h13,h10]
    rw [exec_opimm,hv];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r1⟩ ⟨c5,r1⟩ := by
    refine Quiet.step_of (by change (0x800043fa#32).getLsbD 0=false;decide) de2147501050 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r1 0 [] [] = ⟨.ok c5 r1 [],[]⟩
    have v12 : c4.get 12=dst+1#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h13,h10]
    have v10 : c4.get 10=finish := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h13,h10]
    rw [exec_branch,v12,v10,ht]
    cases last with
    | false =>
      simp only [Bool.not_false,ite_true]
      rw [show c4.pc=0x800043fa#32 by rfl,show 0x800043fa#32+0xfffffff4#32=0x800043ee#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
    | true => rfl
  refine ⟨c5,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h13,h10]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h13,h10]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h13,h10]
  · intro reg h14 h12 h13;simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h13,h10,h14,h12,h13]
end E5R.Thermostat.HttpDecCopyTurn
