-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.FormatBool
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.BoolFormatQuiet
import Projects.thermostat.FormatCursorQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.FormatBool
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp fmt obj boolSrc dst flags : Word)
    (cap pos : Nat) (b : Bool)
    (hp : c.pc = 0x80005112#32) (hsp : c.get 2 = sp+64#32) (h10 : c.get 10 = boolSrc) (h11 : c.get 11 = fmt)
    (hb : ReadBytes.Byte B img ram boolSrc (Encoding.boolByte b))
    (h : FormatInput.Data B ram sp fmt obj (FormatLiterals.boolPointer b) dst flags cap pos (ReplyJson.boolean b))
    (hrom : B.inRam 0x80005c10#32 4 = false) :
    ∃ d n r, n ≤ 6*(ReplyJson.boolean b).length+86 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      FormatCursor.Post B c d ram r sp obj dst cap pos (ReplyJson.boolean b) := by
  obtain ⟨a,ta,apc,a10,a11,a12,aframe,acsr⟩ := E5R.Thermostat.BoolFormat.contract_quiet B c ram boolSrc fmt b hp h10 h11 hb
  have asp : a.get 2 = sp+64#32 := (aframe 2 (by decide) (by decide) (by decide) (by decide)).trans hsp
  have pre := FormatInput.to_pre h apc asp a10 a11 a12
  obtain ⟨d,n,r,hn,td,hd⟩ := E5R.Thermostat.FormatCursor.contract_quiet B a ram sp fmt obj (FormatLiterals.boolPointer b) dst flags cap pos (ReplyJson.boolean b) pre hrom
  have a1 : a.get 1 = c.get 1 := aframe 1 (by decide) (by decide) (by decide) (by decide)
  have asp' : a.get 2 = c.get 2 := aframe 2 (by decide) (by decide) (by decide) (by decide)
  refine ⟨d,8+n,r,by omega,ta.trans td,?_,hd.result,hd.pointer,hd.capacity,hd.position,hd.written,hd.refused,hd.frame⟩
  refine ⟨by rw [hd.returned.pc,a1],hd.returned.sp.trans asp',hd.returned.csr.trans acsr,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact hd.returned.x1 |>.trans (aframe 1 (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x8 |>.trans (aframe 8 (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x9 |>.trans (aframe 9 (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x18 |>.trans (aframe 18 (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x19 |>.trans (aframe 19 (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x20 |>.trans (aframe 20 (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x21 |>.trans (aframe 21 (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x22 |>.trans (aframe 22 (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x23 |>.trans (aframe 23 (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x24 |>.trans (aframe 24 (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x25 |>.trans (aframe 25 (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x26 |>.trans (aframe 26 (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x27 |>.trans (aframe 27 (by decide) (by decide) (by decide) (by decide))

end E5R.Thermostat.FormatBool
