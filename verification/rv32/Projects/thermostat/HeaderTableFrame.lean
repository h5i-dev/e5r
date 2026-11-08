import Projects.thermostat.HeaderFrame
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HeaderTableFrame
open E5R E5R.Thermostat

theorem table {B before after req n entries} (h : HeaderInput.Table B before (req+32#32) n entries)
    (ho : ViewFrame.Region before after req 372) : HeaderInput.Table B after (req+32#32) n entries := by
  refine ⟨h.bounded,?_⟩
  intro i
  apply HeaderFrame.cell (h.cells i)
  intro j
  have hi := i.isLt
  have hj := j.isLt
  have hn := h.bounded
  have hk : 32+16*i.val+j.val < 372 := by omega
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using ho ⟨32+16*i.val+j.val,hk⟩

/-- Checked metadata is transferred separately from replaced raw-buffer bytes. -/
theorem replace {B before after req p raw entries ys} (h : Header.Pre B before req p raw entries)
    (ho : ViewFrame.Region before after req 372) (hb : Bytes.Span B after p ys) (hl : ys.length = raw.length) :
    Header.Pre B after req p ys entries := by
  refine ⟨h.object,h.aligned,(ViewFrame.word ho 288 (by decide)).trans h.count,
    (ViewFrame.word ho 328 (by decide)).trans h.pointer,?_,hb,h.positive,?_,?_⟩
  · rw [hl];exact (ViewFrame.word ho 332 (by decide)).trans h.length
  · rw [hl];exact h.nowrap
  · rw [hl];exact table h.table ho
end E5R.Thermostat.HeaderTableFrame
