import Projects.thermostat.WriteHandlerCode
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.StatusResponse
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (out f status : Word) : Word → BitVec 8 := ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (out+0#32) (1#32) .w) (out+4#32) (0#32) .w) (out+8#32) (0#32) .w) (out+12#32) (status) .h) (out+14#32) (0#32) .b) (f+36#32) (1#32) .b) (f+40#32) (1#32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (out f status : Word)
    (hp : c.pc = 0x800005aa#32) (h8 : c.get 8 = f) (h9 : c.get 9 = out)
    (h10 : c.get 10 = 0#32) (h18 : c.get 18 = 0#32) (h20 : c.get 20 = status) (h22 : c.get 22 = 1#32)
    (ho : Memory.Block B out 15) (ha : out.toNat%4 = 0) (hf : Memory.Block B f 41) :
    ∃ d, DetSteps B img 8 ⟨c,ram⟩ ⟨d,memory ram out f status⟩ ∧ d.pc = 0x800005c4#32 ∧
      (∀ r : Reg, r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 1#32 0x800005ac#32
  let c2 := c1.goto 0x800005ae#32
  let c3 := c2.goto 0x800005b0#32
  let c4 := c3.goto 0x800005b4#32
  let c5 := c4.goto 0x800005b8#32
  let c6 := c5.goto 0x800005bc#32
  let c7 := c6.goto 0x800005c0#32
  let c8 := c7.goto 0x800005c4#32
  let r1 := ramWrite ram (out+0#32) (1#32) .w
  let r2 := ramWrite r1 (out+4#32) (0#32) .w
  let r3 := ramWrite r2 (out+8#32) (0#32) .w
  let r4 := ramWrite r3 (out+12#32) (status) .h
  let r5 := ramWrite r4 (out+14#32) (0#32) .b
  let r6 := ramWrite r5 (f+36#32) (1#32) .b
  let r7 := ramWrite r6 (f+40#32) (1#32) .b
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wh2147485098) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine detStep_of (by change (0x800005ac#32).getLsbD 0 = false;decide) wh2147485100 fun o => ?_
    have hb : c1.get 9 = out := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    have hv : c1.get 12 = 1#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    rw [exec_store,hb,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned out 0 ha) (Memory.block_access ho (off := 0) (width := 4) (by decide) (by decide))];rfl
  have s2 : DetStep B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine detStep_of (by change (0x800005ae#32).getLsbD 0 = false;decide) wh2147485102 fun o => ?_
    have hb : c2.get 9 = out := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    have hv : c2.get 10 = 0#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    rw [exec_store,hb,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned out 1 ha) (Memory.block_access ho (off := 4) (width := 4) (by decide) (by decide))];rfl
  have s3 : DetStep B img ⟨c3,r2⟩ ⟨c4,r3⟩ := by
    refine detStep_of (by change (0x800005b0#32).getLsbD 0 = false;decide) wh2147485104 fun o => ?_
    have hb : c3.get 9 = out := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    have hv : c3.get 18 = 0#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    rw [exec_store,hb,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned out 2 ha) (Memory.block_access ho (off := 8) (width := 4) (by decide) (by decide))];rfl
  have s4 : DetStep B img ⟨c4,r3⟩ ⟨c5,r4⟩ := by
    refine detStep_of (by change (0x800005b4#32).getLsbD 0 = false;decide) wh2147485108 fun o => ?_
    have hb : c4.get 9 = out := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    have hv : c4.get 20 = status := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    rw [exec_store,hb,hv,interp_store_ram (B := B) (img := img) (w := .h) o
      (Memory.half_aligned out 6 (by omega)) (Memory.block_access ho (off := 12) (width := 2) (by decide) (by decide))];rfl
  have s5 : DetStep B img ⟨c5,r4⟩ ⟨c6,r5⟩ := by
    refine detStep_of (by change (0x800005b8#32).getLsbD 0 = false;decide) wh2147485112 fun o => ?_
    have hb : c5.get 9 = out := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    have hv : c5.get 0 = 0#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    rw [exec_store,hb,hv,interp_store_ram (B := B) (img := img) (w := .b) o
      (by exact Nat.mod_one _) (Memory.block_access ho (off := 14) (width := 1) (by decide) (by decide))];rfl
  have s6 : DetStep B img ⟨c6,r5⟩ ⟨c7,r6⟩ := by
    refine detStep_of (by change (0x800005bc#32).getLsbD 0 = false;decide) wh2147485116 fun o => ?_
    have hb : c6.get 8 = f := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    have hv : c6.get 22 = 1#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    rw [exec_store,hb,hv,interp_store_ram (B := B) (img := img) (w := .b) o
      (by exact Nat.mod_one _) (Memory.block_access hf (off := 36) (width := 1) (by decide) (by decide))];rfl
  have s7 : DetStep B img ⟨c7,r6⟩ ⟨c8,r7⟩ := by
    refine detStep_of (by change (0x800005c0#32).getLsbD 0 = false;decide) wh2147485120 fun o => ?_
    have hb : c7.get 8 = f := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    have hv : c7.get 22 = 1#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    rw [exec_store,hb,hv,interp_store_ram (B := B) (img := img) (w := .b) o
      (by exact Nat.mod_one _) (Memory.block_access hf (off := 40) (width := 1) (by decide) (by decide))];rfl
  refine ⟨c8,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.single s7))))))),rfl,?_,by rfl⟩
  intro r hr
  simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hr]
end E5R.Thermostat.StatusResponse
