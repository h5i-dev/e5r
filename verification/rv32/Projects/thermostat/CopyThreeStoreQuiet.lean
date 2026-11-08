-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CopyThreeStore
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.CopyThreeStore
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc=0x80005228#32) (h6 : c.get 6=sp+15#32)
    (h16 : c.get 16=0x7b#32) (hm : Memory.Block B sp 16) :
    Quiet.Step B img ⟨c,CopyUnalignedScratch.memory ram sp⟩ ⟨c.goto 0x8000522c#32,CopyInitData.byteRam ram sp⟩ := by
  refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact cp2147504680) fun o => ?_
  rw [exec_store,h6,h16,BitVec.add_zero,interp_store_ram (B := B) (img := img) (w := .b) o
    (by exact Nat.mod_one _) (Memory.block_access hm (off := 15) (by decide) (by decide)),hp]
  rfl

end E5R.Thermostat.CopyThreeStore
