import Projects.thermostat.PackedFetch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.PackedData
open E5R E5R.Thermostat E5R.RamElf E5R.Thermostat.PackedSlice

def dataByte (a : Nat) : Nat := rawByte PackedFetch.elf.words (26280+(a-0x800056a8))

theorem romByte_data (a : Nat) (hlo : 0x800056a8 ≤ a) (hhi : a < 0x80005f18) :
    romByte? img a false = some (dataByte a) := by
  unfold romByte?
  rw [PackedFetch.ro_eq]
  have hlen0 : (PackedFetch.elf.slice 4096 782 ++ List.replicate 0 0).length = 782 := by simp [slice_length]
  have hlen1 : (PackedFetch.elf.slice 4878 21402 ++ List.replicate 0 0).length = 21402 := by simp [slice_length]
  have hlen2 : (PackedFetch.elf.slice 26280 2160 ++ List.replicate 0 0).length = 2160 := by simp [slice_length]
  simp only [List.find?,hlen0,hlen1,hlen2]
  have h0 : (0x80000000 ≤ a && decide (a < 0x80000000+782) && (!false || true)) = false := by simp [show ¬a < 0x80000000+782 by omega]
  have h1 : (0x8000030e ≤ a && decide (a < 0x8000030e+21402) && (!false || true)) = false := by simp [show ¬a < 0x8000030e+21402 by omega]
  have h2 : (0x800056a8 ≤ a && decide (a < 0x800056a8+2160) && (!false || false)) = true := by simp [hlo,hhi]
  rw [h0,h1,h2]
  simp only [Segment.byte?,hlo,ite_true]
  rw [List.getElem?_append_left (by rw [slice_length];omega),slice_get _ _ _ _ (by omega)]
  rfl

theorem romRead_go {byte : Nat → Nat} {lo hi : Nat}
    (hb : ∀ x, lo ≤ x → x < hi → romByte? img x false = some (byte x)) (a : Nat) :
    ∀ n, lo ≤ a → a+n ≤ hi → romRead?.go img a false n = some (PackedFetch.rd byte a n)
  | 0,_,_ => rfl
  | n+1,h1,h2 => by
    simp only [romRead?.go]
    rw [hb (a+n) (by omega) (by omega),romRead_go hb a n h1 (by omega)]
    rfl

theorem read_data (a n : Nat) (hlo : 0x800056a8 ≤ a) (hhi : a+n ≤ 0x80005f18) :
    romRead? img a n false = some (BitVec.ofNat 32 (PackedFetch.rd dataByte a n)) := by
  unfold romRead?
  rw [romRead_go romByte_data a n hlo hhi]
  rfl

theorem read_byte (a : Nat) (hlo : 0x800056a8 ≤ a) (hhi : a < 0x80005f18) :
    romRead? img a 1 false = some (BitVec.ofNat 32 (dataByte a)) := by
  simpa only [PackedFetch.rd,Nat.add_zero,Nat.pow_zero,Nat.mul_one,Nat.zero_add] using read_data a 1 hlo (by omega)
end E5R.Thermostat.PackedData
