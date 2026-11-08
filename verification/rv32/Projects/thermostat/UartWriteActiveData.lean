import Projects.thermostat.StoreWords
namespace E5R.Thermostat.UartWriteActiveData
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (obj io src len : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite ram (obj+24#32) io .w) (obj+28#32) src .w) (obj+32#32) len .w) (obj+36#32) 0#32 .b

theorem length (ram : Word → BitVec 8) (obj io src len : Word) : ramRead (memory ram obj io src len) (obj+32#32) .w=len := by
  unfold memory
  rw [StoreWords.read_other _ _ _ _ .b (StoreWords.offsets obj 32 4 36 1 (by decide) (by decide) (Or.inl (by decide)))]
  exact ramRead_ramWrite_w _ _ _

theorem source (ram : Word → BitVec 8) (obj io src len : Word) : ramRead (memory ram obj io src len) (obj+28#32) .w=src := by
  unfold memory
  rw [StoreWords.read_other _ _ _ _ .b (StoreWords.offsets obj 28 4 36 1 (by decide) (by decide) (Or.inl (by decide)))]
  rw [StoreWords.read_other _ _ _ _ .w (StoreWords.offsets obj 28 4 32 4 (by decide) (by decide) (Or.inl (by decide)))]
  exact ramRead_ramWrite_w _ _ _
end E5R.Thermostat.UartWriteActiveData
