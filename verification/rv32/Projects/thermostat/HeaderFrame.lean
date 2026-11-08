import Projects.thermostat.ViewFrame
import Projects.thermostat.Header
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HeaderFrame
open E5R E5R.Thermostat

theorem cell {B before after p n e} (h : HeaderInput.Cell B before p n e)
    (hr : ViewFrame.Region before after p 16) : HeaderInput.Cell B after p n e := by
  refine ⟨h.block,h.aligned,?_,(ViewFrame.word hr 4 (by decide)).trans h.nameEnd,
    (ViewFrame.word hr 8 (by decide)).trans h.valueStart,(ViewFrame.word hr 12 (by decide)).trans h.valueEnd,h.bounds⟩
  have hh := ViewFrame.word hr 0 (by decide)
  simpa only [BitVec.add_zero] using hh.trans (by simpa only [BitVec.add_zero] using h.nameStart)

theorem header {B before after req p raw entries} (h : Header.Pre B before req p raw entries)
    (ho : ViewFrame.Region before after req 372) (hb : ViewFrame.Region before after p raw.length) :
    Header.Pre B after req p raw entries := by
  refine ⟨h.object,h.aligned,(ViewFrame.word ho 288 (by decide)).trans h.count,
    (ViewFrame.word ho 328 (by decide)).trans h.pointer,(ViewFrame.word ho 332 (by decide)).trans h.length,
    ViewFrame.span h.bytes hb,h.positive,h.nowrap,⟨h.table.bounded,?_⟩⟩
  intro i
  apply cell (h.table.cells i)
  intro j
  have hi := i.isLt
  have hj := j.isLt
  have hn := h.table.bounded
  have hk : 32+16*i.val+j.val < 372 := by omega
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using ho ⟨32+16*i.val+j.val,hk⟩
end E5R.Thermostat.HeaderFrame
