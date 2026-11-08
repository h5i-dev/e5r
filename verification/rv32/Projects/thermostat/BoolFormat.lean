import Projects.thermostat.BoolFormatBranch
import Projects.thermostat.BoolFormatTail
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.BoolFormat
open E5R E5R.Thermostat

/-- Actual bool Display routes exactly to this ELF's lowercase true/false
    literals and real Formatter::write_str, without allocating a stack frame. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src fmt : Word) (b : Bool)
    (hp : c.pc = 0x80005112#32) (h10 : c.get 10 = src) (h11 : c.get 11 = fmt)
    (hb : ReadBytes.Byte B img ram src (Encoding.boolByte b)) :
    ∃ d, DetSteps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004790#32 ∧ d.get 10 = fmt ∧
      d.get 11 = FormatLiterals.boolPointer b ∧ d.get 12 = BitVec.ofNat 32 (ReplyJson.boolean b).length ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 10 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,ta,apc,a10,aframe,acsr⟩ := BoolFormatBranch.contract B c ram src fmt b hp h10 h11 hb
  obtain ⟨d,td,dpc,d11,d12,dframe,dcsr⟩ := BoolFormatTail.contract B a ram b apc
  refine ⟨d,ta.trans td,dpc,(dframe 10 (by decide) (by decide) (by decide)).trans a10,d11,d12,?_,dcsr.trans acsr⟩
  intro r h6 h10 h11 h12
  exact (dframe r h6 h11 h12).trans (aframe r h10 h12)
end E5R.Thermostat.BoolFormat
