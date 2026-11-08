-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.AuthStop
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.AuthStop
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (v : BitVec 8)
    (hp : c.pc = 0x80000596#32) (hsp : c.get 2 = p) (h10 : c.get 10 = v.setWidth 32)
    (hm : Memory.Block B p 25) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ramPut ram (p+24#32) v⟩ ∧
      d.pc = (if v = 0#8 then 0x800005e2#32 else 0x800005a2#32) ∧ d.get 10 = v.setWidth 32 ∧
      (∀ r : Reg, r ≠ 10 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x8000059a#32
  let c2 := c1.wr 10 (p+24#32) 0x8000059c#32
  let c3 := c2.wr 10 (v.setWidth 32) 0x800005a0#32
  let d := c3.goto (if v = 0#8 then 0x800005e2#32 else 0x800005a2#32)
  let r := ramPut ram (p+24#32) v
  have hr : B.inRam (p+24#32) 1 = true := Memory.block_access hm (off := 24) (by decide) (by decide)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,r⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact au2147485078) fun o => ?_
    rw [exec_store,hsp,h10,interp_store_ram (B := B) (img := img) (w := .b) o (by change (p+24#32).toNat%1 = 0;omega) hr]
    change Result.ok (c.goto (c.pc+4#32)) (ramPut ram (p+24#32) (byteOf (v.setWidth 32) 0)) [] = _
    rw [low,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,r⟩ ⟨c2,r⟩ := by
    refine QuietDet.step_of (by change (0x8000059a#32).getLsbD 0 = false;decide) au2147485082 fun o => ?_
    have hv : c1.get 2 = p := hsp
    rw [exec_opimm,hv];rfl
  have s2 : Quiet.Step B img ⟨c2,r⟩ ⟨c3,r⟩ := by
    refine QuietDet.step_of (by change (0x8000059c#32).getLsbD 0 = false;decide) au2147485084 fun o => ?_
    have hv : c2.get 2 = p := by simp [c2,c1,Core.wr_get_ne,hsp]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .b) o (by change (p+24#32).toNat%1 = 0;omega) hr,Memory.load_byte]
    have hb : r (p+24#32) = v := ramPut_eq _ _ _
    change interp B img o (.done (c2.wr 10 (BitVec.ofNat 32 (r (p+24#32)).toNat) 0x800005a0#32)) r 0 [] = _
    rw [hb,Memory.ofNat_width];rfl
  have s3 : Quiet.Step B img ⟨c3,r⟩ ⟨d,r⟩ := by
    refine QuietDet.step_of (by change (0x800005a0#32).getLsbD 0 = false;decide) au2147485088 fun o => ?_
    have hv : c3.get 10 = v.setWidth 32 := by simp [c3,Core.wr_get]
    rw [exec_branch,hv,Core.get_zero,←Memory.ofNat_width]
    have ht : taken .eq (BitVec.ofNat 32 v.toNat) (0 : Word) = decide (v = 0#8) := by
      change decide (BitVec.ofNat 32 v.toNat = BitVec.ofNat 32 (0#8).toNat) = _
      simp only [Literal.byte_injective]
    rw [ht]
    by_cases he : v = 0#8
    · rw [decide_eq_true he];simp only [ite_true,d,ite_eq_left he]
      change interp B img o (jump c3 (0x800005a0#32+0x42#32)) r 0 [] = _
      rw [show 0x800005a0#32+0x42#32 = 0x800005e2#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    · rw [decide_eq_false he];simp only [Bool.false_eq_true,ite_false,d,ite_eq_right he];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.single s3))),rfl,?_,?_,by rfl⟩
  · simp [d,c3,Core.wr_get]
  · intro r hr;simp [d,c3,c2,c1,Core.wr_get_ne,hr]

end E5R.Thermostat.AuthStop
