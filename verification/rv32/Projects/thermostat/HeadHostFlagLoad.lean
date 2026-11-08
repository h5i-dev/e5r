import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadHostFlagLoad
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (byte : BitVec 8) (h2 : c.get 2=sp) (hm : B.inRam (sp+324#32) 1=true) (hbyte : ram (sp+324#32)=byte)
    (hp : c.pc=0x80003182#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003186#32 ∧
      d.get 10=BitVec.ofNat 32 byte.toNat ∧ (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (BitVec.ofNat 32 byte.toNat) 0x80003186#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496322) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h2,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hm,Memory.load_byte,hbyte];first | rfl | (rw [hp];rfl)
  refine ⟨c1,.single t0,rfl,?_ ,?_ ,by rfl⟩
  · simp [c1,Core.wr_get_ne,Core.wr_get,h2]
  · intro reg h10;simp [c1,Core.wr_get_ne,Core.wr_get,h2,h10]
end E5R.Thermostat.HeadHostFlagLoad
