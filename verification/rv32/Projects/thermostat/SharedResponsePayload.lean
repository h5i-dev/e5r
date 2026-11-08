import Projects.thermostat.SharedResponseMemory
import Projects.thermostat.BodyMemory
namespace E5R.Thermostat.SharedResponsePayload
open E5R E5R.Thermostat

def byte (mime mimeLength used status close : Word) (i : Fin 15) : BitVec 8 :=
  if i.val=14 then byteOf close 0 else BodyMemory.responseByte mime mimeLength used status i

def At (ram : Word → BitVec 8) (fp mime mimeLength used status close : Word) : Prop :=
  ∀ i : Fin 15, ram ((fp+128#32)+BitVec.ofNat 32 i.val)=byte mime mimeLength used status close i

theorem of_stored {ram fp io0 io1 io2 saved status mimeLength mime close methodMinus used}
    (h : SharedResponseMemory.At ram fp io0 io1 io2 saved status mimeLength mime close methodMinus used) :
    At ram fp mime mimeLength used status close := by
  intro i
  have hi := i.isLt
  have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 ∨ i.val=6 ∨ i.val=7 ∨
    i.val=8 ∨ i.val=9 ∨ i.val=10 ∨ i.val=11 ∨ i.val=12 ∨ i.val=13 ∨ i.val=14 := by omega
  have hs := h ⟨20+i.val,by omega⟩
  rcases hc with he|he|he|he|he|he|he|he|he|he|he|he|he|he|he
  all_goals simp only [SharedResponseMemory.liveByte,he] at hs
  all_goals simp at hs
  all_goals simpa [byte,BodyMemory.responseByte,he,BitVec.add_assoc] using hs
end E5R.Thermostat.SharedResponsePayload
