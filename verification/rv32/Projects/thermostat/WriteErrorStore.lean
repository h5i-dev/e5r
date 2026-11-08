import Projects.thermostat.WriteErrorCode
import Projects.thermostat.Memory
import Projects.thermostat.Errors
import Projects.thermostat.ReadBytes
import Projects.thermostat.StoreBytes
namespace E5R.Thermostat.WriteErrorStore
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) (e : Spec.Error) := ramWrite ram (sp+24#32) (BitVec.ofNat 32 (Errors.code e).toNat) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (e : Spec.Error)
    (hp : c.pc=0x80000652#32) (hs : c.get 2=sp) (h10 : c.get 10=BitVec.ofNat 32 (Errors.code e).toNat)
    (hm : Memory.Block B sp 25) :
    DetStep B img ⟨c,ram⟩ ⟨c.goto 0x80000656#32,memory ram sp e⟩ := by
  refine detStep_of (by rw [hp];decide) (by rw [hp];exact er2147485266) fun o => ?_
  rw [exec_store,hs,h10,interp_store_ram (B := B) (img := img) (w := .b) o
    (by exact Nat.mod_one _) (Memory.block_access hm (off := 24) (by decide) (by decide)),hp]
  rfl

theorem byte (B : Board) (ram : Word → BitVec 8) (sp : Word) (e : Spec.Error) (hm : Memory.Block B sp 25) :
    ReadBytes.Byte B img (memory ram sp e) (sp+24#32) (Errors.code e) := by
  apply ReadBytes.Byte.ram (Memory.block_access hm (off := 24) (by decide) (by decide))
  cases e <;> simp [memory,ramRead,ramWrite,ramPut,Errors.code,byteOf]

theorem frame (ram : Word → BitVec 8) (sp : Word) (e : Spec.Error) (x : Word) (hx : x≠sp+24#32) : memory ram sp e x=ram x := by
  exact ramPut_ne _ hx
end E5R.Thermostat.WriteErrorStore
