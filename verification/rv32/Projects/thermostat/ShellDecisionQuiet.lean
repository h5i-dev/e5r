-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ShellDecision
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.ShellDecision
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (res : Except Spec.Error Spec.Success)
    (hp : c.pc = 0x8000063a) (hblock : Memory.Block B (c.get 2+24#32) 20)
    (hres : Outcome.At ram (c.get 2+24#32) res) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if success res then 0x80000678 else 0x80000648) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 21 → d.get r = c.get r) ∧ d.sameCsr c ∧ d.get 10 = BitVec.ofNat 32 (ram (c.get 2+24#32)).toNat ∧ d.get 21 = BitVec.ofNat 32 (ram (c.get 2+34#32)).toNat := by
  let out := c.get 2+24#32
  let tagWord := BitVec.ofNat 32 (ram (out+10#32)).toNat
  let first := BitVec.ofNat 32 (ram out).toNat
  let c1 := c.wr 21 tagWord 0x8000063e
  let c2 := c1.wr 10 first 0x80000642
  let c3 := c2.wr 11 2 0x80000644
  let d := c3.goto (if success res then 0x80000678 else 0x80000648)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact s2147485242) fun o => ?_
    have hm : B.inRam (c.get 2+34#32) 1 = true := by
      simpa [out,BitVec.add_assoc] using Memory.block_access (B := B) (p := out) (n := 20) (off := 10) (width := 1) hblock (by decide) (by decide)
    rw [exec_load,interp_load_ram (B := B) (img := img) (w := .b) (a := c.get 2+34#32) o (by exact Nat.mod_one _) hm,Memory.load_byte,hp]
    simp [c1,tagWord,out,BitVec.add_assoc]
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000063e : Word).getLsbD 0 = false;decide) s2147485246 fun o => ?_
    have hs : c1.get 2 = c.get 2 := by simp [c1,Core.wr_get_ne]
    have hm : B.inRam out 1 = true := by
      simpa using Memory.block_access (B := B) (p := out) (n := 20) (off := 0) (width := 1) hblock (by decide) (by decide)
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .b) (a := out) o (by exact Nat.mod_one _) hm,Memory.load_byte]
    rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80000642 : Word).getLsbD 0 = false;decide) s2147485250 fun o => ?_
    rw [exec_opimm];rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x80000644 : Word).getLsbD 0 = false;decide) s2147485252 fun o => ?_
    have h21 : c3.get 21 = tagWord := by simp [c3,c2,c1,Core.wr_get]
    have h11 : c3.get 11 = 2 := by simp [c3,Core.wr_get]
    have htaken : taken .ne tagWord (2 : Word) = success res := by exact tag ram out res hres
    rw [exec_branch,h21,h11,htaken]
    cases hs : success res <;> simp [d,hs,jump,c3,Core.wr] <;> rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.single s3))),rfl,?_,by rfl,?_,?_⟩
  · intro r h10 h11 h21
    simp [d,c3,c2,c1,Core.wr_get_ne,h10,h11,h21]
  · simp [d,c3,c2,first,out,Core.wr_get]
  · simp [d,c3,c2,c1,tagWord,out,Core.wr_get,BitVec.add_assoc]

end E5R.Thermostat.ShellDecision
