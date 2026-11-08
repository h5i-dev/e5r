import Projects.thermostat.WireCallerCode
import Projects.thermostat.WireCallerBytes
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.WireCallerStore
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p w : Word)
    (hp : c.pc = 0x80000604#32) (hsp : c.get 2 = p) (h10 : c.get 10 = w) (h20 : c.get 20 = w >>> 16)
    (hm : Memory.Block B p 16) (ha : p.toNat%2 = 0) :
    ∃ d, DetSteps B img 4 ⟨c,ram⟩ ⟨d,WireCallerBytes.memory ram p w⟩ ∧ d.pc = 0x80000614#32 ∧
      (∀ r : Reg, r ≠ 11 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (w >>> 8) 0x80000608#32
  let c2 := c1.goto 0x8000060c#32
  let c3 := c2.goto 0x80000610#32
  let d := c3.goto 0x80000614#32
  let r1 := ramWrite ram (p+10#32) w .b
  let r2 := ramWrite r1 (p+11#32) (w >>> 8) .b
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wc2147485188) fun o => ?_
    rw [exec_opimm,h10,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine detStep_of (by change (0x80000608#32).getLsbD 0 = false;decide) wc2147485192 fun o => ?_
    have hv2 : c1.get 2 = p := by simp [c1,Core.wr_get_ne,hsp]
    have hv10 : c1.get 10 = w := by simp [c1,Core.wr_get_ne,h10]
    rw [exec_store,hv2,hv10,interp_store_ram (B := B) (img := img) (w := .b) o
      (by change (p+10#32).toNat%1 = 0;omega) (Memory.block_access hm (off := 10) (by decide) (by decide))];rfl
  have s2 : DetStep B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine detStep_of (by change (0x8000060c#32).getLsbD 0 = false;decide) wc2147485196 fun o => ?_
    have hv2 : c2.get 2 = p := by simp [c2,c1,Core.wr_get_ne,hsp]
    have hv11 : c2.get 11 = w >>> 8 := by simp [c2,c1,Core.wr_get]
    rw [exec_store,hv2,hv11,interp_store_ram (B := B) (img := img) (w := .b) o
      (by change (p+11#32).toNat%1 = 0;omega) (Memory.block_access hm (off := 11) (by decide) (by decide))];rfl
  have s3 : DetStep B img ⟨c3,r2⟩ ⟨d,WireCallerBytes.memory ram p w⟩ := by
    refine detStep_of (by change (0x80000610#32).getLsbD 0 = false;decide) wc2147485200 fun o => ?_
    have hv2 : c3.get 2 = p := by simp [c3,c2,c1,Core.wr_get_ne,hsp]
    have hv20 : c3.get 20 = w >>> 16 := by simp [c3,c2,c1,Core.wr_get_ne,h20]
    rw [exec_store,hv2,hv20,interp_store_ram (B := B) (img := img) (w := .h) o
      (Memory.half_aligned p 6 ha) (Memory.block_access hm (off := 12) (by decide) (by decide))];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.single s3))),rfl,?_,by rfl⟩
  intro r hr;simp [d,c3,c2,c1,Core.wr_get_ne,hr]
end E5R.Thermostat.WireCallerStore
