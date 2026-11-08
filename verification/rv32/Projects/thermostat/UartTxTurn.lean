import Projects.thermostat.UartTxWait
import Projects.thermostat.UartTxByte
namespace E5R.Thermostat.UartTxTurn
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

/-- One actual byte, with any finite not-ready prefix and a ready status.
    The trace records each status and exactly one output byte; no input byte
    or RAM change is hidden behind a UART summary. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (src finish : Word) (v : BitVec 8)
    (statuses : List Word) (readyStatus : Word) (last : Bool)
    (hp : c.pc=0x800007f4#32) (h12 : c.get 12=src) (h14 : c.get 14=finish)
    (h13 : c.get 13=0x10000000#32) (h15 : c.get 15=0x10000000#32)
    (hs : ReadBytes.Byte B img ram src v)
    (hz : ∀ s ∈ statuses, UartTxPoll.mask s=0#32) (hr : UartTxPoll.mask readyStatus≠0#32)
    (ht : taken .eq (src+1#32) finish=last) :
    ∃ d, Observed.Steps B img (5*statuses.length+7) ⟨c,ram⟩ ⟨d,ram⟩
      (UartTxWait.log (statuses++[readyStatus])) [⟨0x10000000#32,UartTxByte.word v⟩] ∧
      d.pc=(if last then 0x8000080a#32 else 0x800007f4#32) ∧ d.get 12=src+1#32 ∧
      (∀ r : Reg, r≠12 → r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 16 (UartTxByte.word v) 0x800007f8#32
  have ta := UartTxByte.load c ram src v hp h12 hs
  have a12 : a.get 12=src := by simp [a,Core.wr_get_ne,h12]
  have a13 : a.get 13=0x10000000#32 := by simp [a,Core.wr_get_ne,h13]
  have a14 : a.get 14=finish := by simp [a,Core.wr_get_ne,h14]
  have a15 : a.get 15=0x10000000#32 := by simp [a,Core.wr_get_ne,h15]
  have a16 : a.get 16=UartTxByte.word v := by simp [a,Core.wr_get]
  obtain ⟨b,tb,pb,_,br,bc⟩ := UartTxWait.ready_after a ram statuses readyStatus rfl a13 hz hr
  obtain ⟨d,td,pd,d12,dr,dc⟩ := UartTxByte.emit b ram src finish v last pb
    ((br 12 (by decide)).trans a12) ((br 14 (by decide)).trans a14)
    ((br 15 (by decide)).trans a15) ((br 16 (by decide)).trans a16) ht
  refine ⟨d,?_,pd,d12,?_,dc.trans bc⟩
  · have tt := ((Observed.Steps.single ta).trans tb).trans td
    rw [show 1+(5*statuses.length+3)+3=5*statuses.length+7 by omega] at tt
    simpa only [List.nil_append,List.append_nil] using tt
  · intro reg h12 h16 h17
    exact (dr reg h12).trans ((br reg h17).trans (by simp [a,Core.wr_get_ne,h16]))
end E5R.Thermostat.UartTxTurn
