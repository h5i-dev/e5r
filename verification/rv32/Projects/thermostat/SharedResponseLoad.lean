import Projects.thermostat.SharedResponseCode
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.SharedResponseLoad
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fp extra : Word) (h8 : c.get 8=fp) (h13 : c.get 13=extra)
    (hm : Memory.Block B fp 484) (ha : fp.toNat%4=0)
    (hp : c.pc = 0x80001728#32) :
    ∃ d, DetSteps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80001740#32 ∧
      d.get 14 = (extend .b false (ramRead ram (fp+480#32) .b))+0xffffffff#32 ∧ d.get 15 = extend .b false (ramRead ram (fp+100#32) .b) ∧ d.get 16 = extend .w true (ramRead ram (fp+64#32) .w) ∧ d.get 17 = extend .w true (ramRead ram (fp+68#32) .w) ∧ d.get 5 = extend .w true (ramRead ram (fp+72#32) .w) ∧ d.get 13 = extra ||| (extend .b false (ramRead ram (fp+100#32) .b)) ∧ (∀ r : Reg, r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 → r ≠ 5 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (extend .b false (ramRead ram (fp+480#32) .b)) 0x8000172c#32
  let c2 := c1.wr 15 (extend .b false (ramRead ram (fp+100#32) .b)) 0x80001730#32
  let c3 := c2.wr 16 (extend .w true (ramRead ram (fp+64#32) .w)) 0x80001734#32
  let c4 := c3.wr 17 (extend .w true (ramRead ram (fp+68#32) .w)) 0x80001738#32
  let c5 := c4.wr 5 (extend .w true (ramRead ram (fp+72#32) .w)) 0x8000173c#32
  let c6 := c5.wr 13 (extra ||| (extend .b false (ramRead ram (fp+100#32) .b))) 0x8000173e#32
  let c7 := c6.wr 14 ((extend .b false (ramRead ram (fp+480#32) .b))+0xffffffff#32) 0x80001740#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact sr2147489576) fun o => ?_
    have hf : c.get 8=fp := by simp [Core.wr_get_ne,Core.wr_get,h8,h13]
    rw [exec_load,hf,interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 480) (by decide) (by decide))];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x8000172c#32).getLsbD 0 = false;decide) sr2147489580 fun o => ?_
    have hf : c1.get 8=fp := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h13]
    rw [exec_load,hf,interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 100) (by decide) (by decide))];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80001730#32).getLsbD 0 = false;decide) sr2147489584 fun o => ?_
    have hf : c2.get 8=fp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h13]
    rw [exec_load,hf,interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 16 ha) (Memory.block_access hm (off := 64) (by decide) (by decide))];first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80001734#32).getLsbD 0 = false;decide) sr2147489588 fun o => ?_
    have hf : c3.get 8=fp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h13]
    rw [exec_load,hf,interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 17 ha) (Memory.block_access hm (off := 68) (by decide) (by decide))];first | rfl | (rw [hp]; rfl)
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80001738#32).getLsbD 0 = false;decide) sr2147489592 fun o => ?_
    have hf : c4.get 8=fp := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h13]
    rw [exec_load,hf,interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 18 ha) (Memory.block_access hm (off := 72) (by decide) (by decide))];first | rfl | (rw [hp]; rfl)
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x8000173c#32).getLsbD 0 = false;decide) sr2147489596 fun o => ?_
    have v13 : c5.get 13=extra := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h13]
    have v15 : c5.get 15=extend .b false (ramRead ram (fp+100#32) .b) := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h13]
    rw [exec_op,v13,v15];first | rfl | (rw [hp]; rfl)
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine detStep_of (by change (0x8000173e#32).getLsbD 0 = false;decide) sr2147489598 fun o => ?_
    have v14 : c6.get 14=extend .b false (ramRead ram (fp+480#32) .b) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h13]
    rw [exec_opimm,v14];first | rfl | (rw [hp]; rfl)
  refine ⟨c7,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.single s6)))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h13]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h13]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h13]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h13]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h13]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h13]
  · intro r h14 h15 h16 h17 h5 h13
    simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h13,h14,h15,h16,h17,h5,h13]
end E5R.Thermostat.SharedResponseLoad
