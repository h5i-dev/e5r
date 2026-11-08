import Projects.thermostat.MainQueryCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainQueryLoad
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (byte : BitVec 8)
(h12 : c.get 12=p+1#32) (hm : B.inRam p 1=true) (hb : ram p=byte)
    (hp : c.pc=0x80000be0#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000be4#32 ∧
      d.get 13=BitVec.ofNat 32 byte.toNat ∧ (∀ r : Reg, r≠13 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 13 (BitVec.ofNat 32 byte.toNat) 0x80000be4#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147486688) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v12 : c.get 12=p+1#32 := by simp [Core.wr_get_ne,Core.wr_get,h12]
    rw [exec_load,v12,BitVec.add_assoc,show 1#32+0xffffffff#32=0#32 by decide +kernel,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) hm,Memory.load_byte,hb];rw [hp];rfl
  refine ⟨c1,.single t0,rfl,?_ ,?_ ,by rfl⟩
  · simp [c1,Core.wr_get_ne,Core.wr_get,h12]
  · intro reg h13;simp [c1,Core.wr_get_ne,Core.wr_get,h12,h13]
end E5R.Thermostat.MainQueryLoad
