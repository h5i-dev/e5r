import Projects.thermostat.WordRegions
namespace E5R.Thermostat.WordRegions
open E5R E5R.Thermostat

theorem outside_ram {B a n b m} (ho : ∀ i : Fin n, B.inRam (a+BitVec.ofNat 32 i.val) 1 = false)
    (hr : Memory.Block B b m) : Disjoint a n b m := by
  intro i j he
  have hj : B.inRam (b+BitVec.ofNat 32 j.val) 1 = true := Memory.block_access hr (by decide) (by have := j.isLt;omega)
  rw [←he,ho i] at hj
  contradiction
end E5R.Thermostat.WordRegions
