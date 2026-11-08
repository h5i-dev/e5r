-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.WriteInput
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.WriteStartQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.WriteInput
theorem establishes_quiet {B c ram p f response req eng rawPtr pathPtr bodyPtr raw path body entries first admin s}
    (h : Pre B c ram p f response req eng rawPtr pathPtr bodyPtr raw path body entries first admin s) :
    ∃ d, Quiet.Steps B img 31 ⟨c,ram⟩ ⟨d,WriteStart.memory ram (p+80#32) f c⟩ ∧
      TxnInput.Pre B d (WriteStart.memory ram (p+80#32) f c) p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s ∧
      d.get 8 = f ∧ d.get 9 = response ∧
      d.get 19 = ramRead ram (f+12#32) .w ∧ d.get 18 = ramRead ram (f+16#32) .w ∧ d.sameCsr c := by
  obtain ⟨d,td,dpc,dsp,d8,d9,d21,d23,d19,d18,dcsr⟩ := E5R.Thermostat.WriteStart.contract_quiet B c ram (p+80#32) f response
    h.pc h.sp h.future h.response h.stack (Memory.word_aligned p 20 h.layout.aligned)
    h.futureBlock h.futureAligned h.futureSeparate h.fresh
  have hl := layout_frame h.layout (region h.appAvoid ram c) (region h.requestAvoid ram c)
    (region h.rawAvoid ram c) (region h.pathAvoid ram c) (region h.bodyAvoid ram c)
  exact ⟨d,td,to_txn hl dpc dsp (d21.trans h.request) (d23.trans h.engine),d8,d9,d19,d18,dcsr⟩

end E5R.Thermostat.WriteInput
