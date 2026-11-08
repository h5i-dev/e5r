import Projects.thermostat.CopyInitData
namespace E5R.Thermostat.CopyThreeStore
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc=0x80005228#32) (h6 : c.get 6=sp+15#32)
    (h16 : c.get 16=0x7b#32) (hm : Memory.Block B sp 16) :
    DetStep B img ⟨c,CopyUnalignedScratch.memory ram sp⟩ ⟨c.goto 0x8000522c#32,CopyInitData.byteRam ram sp⟩ := by
  refine detStep_of (by rw [hp];decide) (by rw [hp];exact cp2147504680) fun o => ?_
  rw [exec_store,h6,h16,BitVec.add_zero,interp_store_ram (B := B) (img := img) (w := .b) o
    (by exact Nat.mod_one _) (Memory.block_access hm (off := 15) (by decide) (by decide)),hp]
  rfl
end E5R.Thermostat.CopyThreeStore
