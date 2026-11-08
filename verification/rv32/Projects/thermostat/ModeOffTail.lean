import Projects.thermostat.ModeFinish
import Projects.thermostat.Literal
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ModeOffTail
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (b : BitVec 8)
    (hp : c.pc = 0x80002186#32) (h8 : c.get 8 = p) (h12 : c.get 12 = 102#32)
    (hstatus : c.get 11 = 400#32) (hm : B.inRam (p+2#32) 1 = true) (hb : ram (p+2#32) = b) :
    ∃ d n, n ≤ 8 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (if b = 102#8 then .ok (.mode .off) else .error 400) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (BitVec.ofNat 32 b.toNat) 0x8000218a#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wd2147492230) fun o => ?_
    rw [exec_load,h8,interp_load_ram (B := B) (img := img) (w := .b) o (by change (p+2#32).toNat%1 = 0;omega) hm,Memory.load_byte]
    change interp B img o (.done (c.wr 10 (BitVec.ofNat 32 (ram (p+2#32)).toNat) (c.pc+4#32))) ram 0 [] = _
    rw [hb,hp];rfl
  have v10 : c1.get 10 = BitVec.ofNat 32 b.toNat := by simp [c1,Core.wr_get]
  have v12 : c1.get 12 = 102#32 := by simp [c1,Core.wr_get_ne,h12]
  have ht : taken .eq (BitVec.ofNat 32 b.toNat) 102#32 = decide (b = 102#8) := by
    change decide (BitVec.ofNat 32 b.toNat = BitVec.ofNat 32 (102#8).toNat) = _
    simp only [Literal.byte_injective]
  by_cases he : b = 102#8
  · let c2 := c1.goto 0x80002288#32
    have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
      refine detStep_of (by change (0x8000218a#32).getLsbD 0 = false;decide) wd2147492234 fun o => ?_
      rw [exec_branch,v10,v12,ht,decide_eq_true he]
      simp only [ite_true]
      change interp B img o (jump c1 (0x8000218a#32+0xfe#32)) ram 0 [] = _
      rw [show 0x8000218a#32+0xfe#32 = 0x80002288#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    obtain ⟨d,hd,hpc,hval,hregs,hcsr⟩ := ModeFinish.off B c2 ram rfl
    refine ⟨d,8,by omega,(DetSteps.step s0 (.single s1)).trans hd,hpc,by simpa only [ite_eq_left he] using hval,?_,hcsr⟩
    intro r h1 h2 h3
    rw [hregs r h1 h2 h3];simp [c2,c1,Core.wr_get_ne,h1]
  · let c2 := c1.goto 0x8000218e#32
    let c3 := c2.wr 10 255#32 0x80002192#32
    let c4 := c3.goto 0x8000220a#32
    have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
      refine detStep_of (by change (0x8000218a#32).getLsbD 0 = false;decide) wd2147492234 fun o => ?_
      rw [exec_branch,v10,v12,ht,decide_eq_false he];rfl
    have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
      refine detStep_of (by change (0x8000218e#32).getLsbD 0 = false;decide) wd2147492238 fun o => ?_
      rw [exec_opimm,Core.get_zero];rfl
    have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
      refine detStep_of (by change (0x80002192#32).getLsbD 0 = false;decide) wd2147492242 fun o => ?_
      rw [exec_jal]
      change interp B img o (jump c3 (0x80002192#32+0x78#32)) ram 0 [] = _
      rw [show 0x80002192#32+0x78#32 = 0x8000220a#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    obtain ⟨d,hd,hpc,hval,hregs,hcsr⟩ := ModeFinish.error B c4 ram rfl (by simp [c4,c3,Core.wr_get]) (by simp [c4,c3,c2,c1,Core.wr_get_ne,hstatus])
    refine ⟨d,8,by omega,(DetSteps.step s0 (.step s1 (.step s2 (.single s3)))).trans hd,hpc,by simpa only [ite_eq_right he] using hval,?_,hcsr⟩
    intro r h1 h2 h3
    rw [hregs r h1 h2 h3];simp [c4,c3,c2,c1,Core.wr_get_ne,h1]
end E5R.Thermostat.ModeOffTail
