import Projects.thermostat.FormatData
import Projects.thermostat.ReadBytes
namespace E5R.Thermostat.DigitTable
open E5R E5R.Thermostat

def address (i : Fin 100) (unit : Bool) : Word :=
  0x80005e10#32+BitVec.ofNat 32 (2*i.val+(if unit then 1 else 0))

theorem bounds (i : Fin 100) (unit : Bool) :
    0x800056a8 ≤ (address i unit).toNat ∧ (address i unit).toNat < 0x80005f18 := by
  have hi := i.isLt
  cases unit <;> simp only [address,Bool.false_eq_true,ite_true,ite_false,BitVec.toNat_add,BitVec.toNat_ofNat] <;> omega

theorem value (i : Fin 100) (unit : Bool) :
    PackedData.dataByte (address i unit).toNat = 48+(if unit then i.val%10 else i.val/10) := by
  cases unit with
  | false => simpa only [address,Bool.false_eq_true,ite_false,Nat.add_zero] using FormatData.pair_tens i
  | true => simpa only [address,ite_true] using FormatData.pair_units i

theorem byte (B : Board) (ram : Word → BitVec 8) (i : Fin 100) (unit : Bool)
    (ho : B.inRam (address i unit) 1 = false) :
    ReadBytes.Byte B img ram (address i unit) (BitVec.ofNat 8 (48+(if unit then i.val%10 else i.val/10))) := by
  apply ReadBytes.Byte.rom ho
  rw [PackedData.read_byte _ (bounds i unit).1 (bounds i unit).2,value]
  have hi := i.isLt
  congr 1
  simp only [BitVec.toNat_ofNat]
  have hlt : 48+(if unit then i.val%10 else i.val/10) < 256 := by
    cases unit <;> simp only [Bool.false_eq_true,ite_true,ite_false] <;> omega
  rw [Nat.mod_eq_of_lt hlt]

theorem outside (i : Fin 100) (unit : Bool) : UartPlatform.board.inRam (address i unit) 1 = false := by
  have hn : ¬2147507992 ≤ (address i unit).toNat := by have hb := (bounds i unit).2;omega
  unfold UartPlatform.board QemuVirtRv32.board Board.inRam
  rw [ThermostatImage.image_rwBase]
  simp only [hn,decide_false,Bool.false_and]
end E5R.Thermostat.DigitTable
