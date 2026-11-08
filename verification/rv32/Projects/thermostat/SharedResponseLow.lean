import Projects.thermostat.SharedResponse
import Projects.thermostat.WordZero
import Projects.thermostat.ViewFrame
namespace E5R.Thermostat.SharedResponseFlags
open E5R E5R.Thermostat

theorem low (ram : Word → BitVec 8) (fp : Word) : ViewFrame.Region ram (memory ram fp) fp 532 := by
  intro i
  unfold memory first
  have ne (off : Nat) (hlo : 532≤off) (hhi : off<2^32) : fp+BitVec.ofNat 32 i.val≠fp+BitVec.ofNat 32 off :=
    WordZero.offset_ne fp i.val off (by have := i.isLt;omega) hhi (by have := i.isLt;omega)
  simp only [ramWrite,ramPut,ite_eq_right (ne 532 (by decide) (by decide)),ite_eq_right (ne 576 (by decide) (by decide)),
    ite_eq_right (ne 620 (by decide) (by decide)),ite_eq_right (ne 664 (by decide) (by decide))]
end E5R.Thermostat.SharedResponseFlags
