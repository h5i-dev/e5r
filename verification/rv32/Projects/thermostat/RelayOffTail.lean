import Projects.thermostat.RelayFinish
import Projects.thermostat.ModeFinish
import Projects.thermostat.Literal
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.RelayOffTail
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p idx : Word) (b : BitVec 8)
    (hp : c.pc = 0x800021f6#32) (h8 : c.get 8 = p) (h14 : c.get 14 = 102#32)
    (hi : idx.toNat < 256) (h12 : c.get 12 = idx) (htag : c.get 10 = 255#32)
    (hstatus : c.get 11 = 400#32) (hm : B.inRam (p+2#32) 1 = true) (hb : ram (p+2#32) = b) :
    ∃ d n, n ≤ 10 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (if b = 102#8 then .ok (.relay (idx.setWidth 8) false) else .error 400) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 15 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 15 (BitVec.ofNat 32 b.toNat) 0x800021fa#32
  let c2 := c1.wr 13 0#32 0x800021fc#32
  let c3 := c2.goto (if b = 102#8 then 0x80002200#32 else 0x8000220a#32)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wd2147492342) fun o => ?_
    rw [exec_load,h8,interp_load_ram (B := B) (img := img) (w := .b) o (by change (p+2#32).toNat%1 = 0;omega) hm,Memory.load_byte]
    change interp B img o (.done (c.wr 15 (BitVec.ofNat 32 (ram (p+2#32)).toNat) (c.pc+4#32))) ram 0 [] = _
    rw [hb,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x800021fa#32).getLsbD 0 = false;decide) wd2147492346 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x800021fc#32).getLsbD 0 = false;decide) wd2147492348 fun o => ?_
    have v15 : c2.get 15 = BitVec.ofNat 32 b.toNat := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    have v14 : c2.get 14 = 102#32 := by simp [c2,c1,Core.wr_get_ne,h14]
    rw [exec_branch,v15,v14]
    have ht : taken .ne (BitVec.ofNat 32 b.toNat) 102#32 = decide (b ≠ 102#8) := by
      change decide (BitVec.ofNat 32 b.toNat ≠ BitVec.ofNat 32 (102#8).toNat) = _
      simp only [ne_eq,Literal.byte_injective]
    rw [ht]
    by_cases he : b = 102#8
    · simp only [he,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false,c3];rfl
    · simp only [he,ne_eq,not_false_eq_true,decide_true,ite_true,c3,ite_false]
      change interp B img o (jump c2 (0x800021fc#32+14#32)) ram 0 [] = _
      rw [show 0x800021fc#32+14#32 = 0x8000220a#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have pre : DetSteps B img 3 ⟨c,ram⟩ ⟨c3,ram⟩ := .step s0 (.step s1 (.single s2))
  by_cases he : b = 102#8
  · obtain ⟨d,td,pcd,vd,rd,cd⟩ := RelayFinish.success B c3 ram idx false (by simp [c3,he]) hi
      (by simp [c3,c2,c1,Core.wr_get_ne,h12]) (by simp [c3,c2,Core.wr_get])
    refine ⟨d,10,by omega,pre.trans td,pcd,by simpa only [ite_eq_left he] using vd,?_,cd⟩
    intro r h1 h2 h3 h4 h5
    rw [rd r h1 h2 h3];simp [c3,c2,c1,Core.wr_get_ne,h4,h5]
  · obtain ⟨d,td,pcd,vd,rd,cd⟩ := ModeFinish.error B c3 ram (by simp [c3,he])
      (by simp [c3,c2,c1,Core.wr_get_ne,htag]) (by simp [c3,c2,c1,Core.wr_get_ne,hstatus])
    refine ⟨d,7,by omega,pre.trans td,pcd,by simpa only [ite_eq_right he] using vd,?_,cd⟩
    intro r h1 h2 h3 h4 h5
    rw [rd r h1 h2 h3];simp [c3,c2,c1,Core.wr_get_ne,h4,h5]
end E5R.Thermostat.RelayOffTail
