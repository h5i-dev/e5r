-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.WriteErrorStore
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.WriteErrorStore
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (e : Spec.Error)
    (hp : c.pc=0x80000652#32) (hs : c.get 2=sp) (h10 : c.get 10=BitVec.ofNat 32 (Errors.code e).toNat)
    (hm : Memory.Block B sp 25) :
    Quiet.Step B img ⟨c,ram⟩ ⟨c.goto 0x80000656#32,memory ram sp e⟩ := by
  refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact er2147485266) fun o => ?_
  rw [exec_store,hs,h10,interp_store_ram (B := B) (img := img) (w := .b) o
    (by exact Nat.mod_one _) (Memory.block_access hm (off := 24) (by decide) (by decide)),hp]
  rfl

end E5R.Thermostat.WriteErrorStore
