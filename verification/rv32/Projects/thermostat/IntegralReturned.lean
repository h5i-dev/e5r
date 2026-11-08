import Projects.thermostat.IntegralReady
import Projects.thermostat.FormatCursor
namespace E5R.Thermostat.IntegralReady
open E5R E5R.Thermostat

theorem returned {c a d : Core} {writer src len} (h : Ready c a writer src len)
    (hr : CursorExit.Returned a d) (hh : HighFrame.Frame a d) : FormatCursor.Returned c d := by
  refine ⟨by rw [hr.pc,h.x1],hr.sp.trans h.sp,hr.csr.trans h.csr,
    hr.x1.trans h.x1,hr.x8.trans h.x8,hr.x9.trans h.x9,hr.x18.trans h.x18,hr.x19.trans h.x19,
    (hh 20 (by decide)).trans h.x20,(hh 21 (by decide)).trans h.x21,(hh 22 (by decide)).trans h.x22,
    (hh 23 (by decide)).trans h.x23,(hh 24 (by decide)).trans h.x24,(hh 25 (by decide)).trans h.x25,
    (hh 26 (by decide)).trans h.x26,(hh 27 (by decide)).trans h.x27⟩
end E5R.Thermostat.IntegralReady
