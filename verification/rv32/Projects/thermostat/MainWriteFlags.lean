import Projects.thermostat.MainWriteCode
import Projects.thermostat.SharedResponseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainWriteFlags
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (fp : Word) :=
  ramWrite (ram) (fp+532#32) (1#32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fp capacity used : Word) (h8 : c.get 8=fp) (h22 : c.get 22=1#32) (h20 : c.get 20=used) (hm : Memory.Block B fp 536) (ha : fp.toNat%4=0) (hcap : ramRead ram (fp+488#32) .w=capacity) (hfit : used.toNat≤capacity.toNat)
    (hp : c.pc=0x80001710#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,memory ram fp⟩ ∧ d.pc=0x80001728#32 ∧
      d.get 14=capacity ∧ (∀ r : Reg, r≠14 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (capacity) 0x80001714#32
  let r1 := ramWrite ram (fp+532#32) (1#32) .b
  let c2 := c1.goto 0x80001718#32
  let c3 := c2.goto 0x80001728#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact sr2147489552) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=fp := by simp [Core.wr_get_ne,Core.wr_get,h8,h22,h20]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 122 ha) (Memory.block_access hm (off := 488) (by decide) (by decide)),hcap];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x80001714#32).getLsbD 0=false;decide) sr2147489556 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v8 : c1.get 8=fp := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h22,h20]
    have v22 : c1.get 22=1#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h22,h20]
    rw [exec_store,v8,v22,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 532) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r1⟩ := by
    refine Quiet.step_of (by change (0x80001718#32).getLsbD 0=false;decide) sr2147489560 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r1 [],[]⟩
    have v14 : c2.get 14=capacity := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22,h20]
    have v20 : c2.get 20=used := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22,h20]
    have ht : taken .geu capacity used=true := by simp [taken,BitVec.ult,show ¬capacity.toNat<used.toNat by omega]
    rw [exec_branch,v14,v20,ht]
    simp only [ite_true]
    rw [show c2.pc=0x80001718#32 by rfl,show 0x80001718#32+16#32=0x80001728#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22,h20]
  · intro reg h14;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22,h20,h14]
end E5R.Thermostat.MainWriteFlags
