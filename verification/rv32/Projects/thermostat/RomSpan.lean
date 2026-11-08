import Projects.thermostat.PackedData
import Projects.thermostat.ReadBytes
namespace E5R.Thermostat.ReadBytes
open E5R E5R.Thermostat

theorem of_data (B : Board) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (hl : xs.length < 2^32) (hw : p.toNat+xs.length ≤ 2^32)
    (hb : ∀ i : Fin xs.length, 0x800056a8 ≤ (p+BitVec.ofNat 32 i.val).toNat ∧ (p+BitVec.ofNat 32 i.val).toNat < 0x80005f18)
    (ho : ∀ i : Fin xs.length, B.inRam (p+BitVec.ofNat 32 i.val) 1 = false)
    (hv : ∀ i : Fin xs.length, BitVec.ofNat 32 (PackedData.dataByte (p+BitVec.ofNat 32 i.val).toNat) = BitVec.ofNat 32 xs[i.val].toNat) :
    Span B img ram p xs := by
  refine ⟨hl,hw,?_⟩
  intro i
  apply Byte.rom (ho i)
  rw [PackedData.read_byte _ (hb i).1 (hb i).2]
  exact congrArg some (hv i)
end E5R.Thermostat.ReadBytes
