-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.FormatSlice
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.FormatCursorQuiet
import Projects.thermostat.SliceDisplayQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.FormatSlice
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp fmt obj tuple src dst flags : Word)
    (cap pos : Nat) (xs : List (BitVec 8))
    (hp : c.pc = 0x8000228c#32) (hsp : c.get 2 = sp+64#32) (h10 : c.get 10 = tuple) (h11 : c.get 11 = fmt)
    (hm : Memory.Block B tuple 8) (ha : tuple.toNat%4 = 0)
    (hsrc : ramRead ram tuple .w = src) (hlen : ramRead ram (tuple+4#32) .w = BitVec.ofNat 32 xs.length)
    (h : FormatInput.Data B ram sp fmt obj src dst flags cap pos xs)
    (hrom : B.inRam 0x80005c10#32 4 = false) :
    ∃ d n r, n ≤ 6*xs.length+92 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      FormatCursor.Post B c d ram r sp obj dst cap pos xs := by
  obtain ⟨a,ta,apc,a10,a11,a12,aframe,acsr⟩ := E5R.Thermostat.SliceDisplay.contract_quiet B c ram tuple src (BitVec.ofNat 32 xs.length) fmt hp h10 h11 hm ha hsrc hlen
  have asp : a.get 2 = sp+64#32 := (aframe 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsp
  have pre := FormatInput.to_pre h apc asp a10 a11 a12
  obtain ⟨d,n,r,hn,td,hd⟩ := E5R.Thermostat.FormatCursor.contract_quiet B a ram sp fmt obj src dst flags cap pos xs pre hrom
  have a1 : a.get 1 = c.get 1 := aframe 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have asp' : a.get 2 = c.get 2 := aframe 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨d,14+n,r,by omega,ta.trans td,?_,hd.result,hd.pointer,hd.capacity,hd.position,hd.written,hd.refused,hd.frame⟩
  refine ⟨by rw [hd.returned.pc,a1],hd.returned.sp.trans asp',hd.returned.csr.trans acsr,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact hd.returned.x1 |>.trans (aframe 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x8 |>.trans (aframe 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x9 |>.trans (aframe 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x18 |>.trans (aframe 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x19 |>.trans (aframe 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x20 |>.trans (aframe 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x21 |>.trans (aframe 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x22 |>.trans (aframe 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x23 |>.trans (aframe 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x24 |>.trans (aframe 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x25 |>.trans (aframe 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x26 |>.trans (aframe 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hd.returned.x27 |>.trans (aframe 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))

end E5R.Thermostat.FormatSlice
