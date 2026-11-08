import Projects.thermostat.StoreRead
import Projects.thermostat.ReadFrame
namespace E5R.Thermostat.ReadRegion
open E5R E5R.Thermostat

theorem read {before after p n} (h : ViewFrame.Region before after p n) (off : Nat) (w : Width) (ho : off+w.bytes≤n) :
    ramRead after (p+BitVec.ofNat 32 off) w=ramRead before (p+BitVec.ofNat 32 off) w := by
  apply StoreRead.congr
  intro i
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  exact h ⟨off+i.val,by have := i.isLt;omega⟩
end E5R.Thermostat.ReadRegion
