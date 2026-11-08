import Projects.thermostat.CursorMemory
import Projects.thermostat.CursorCall
import Projects.thermostat.CursorFinish
import Projects.thermostat.SmallCopy
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.CursorWritten
open E5R E5R.Thermostat

/-- Capacity-checked actual Cursor body calls actual memcpy, then stores the
    advanced position. Slice panic branches are proved untaken by the bounds. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp obj src dst : Word) (cap pos : Nat) (xs : List (BitVec 8))
    (h : CursorInput.Layout B ram sp obj src dst cap pos xs)
    (hp : c.pc = 0x800022ba#32) (hsp : c.get 2 = sp) (h10 : c.get 10 = obj) (h11 : c.get 11 = src)
    (h8 : c.get 8 = BitVec.ofNat 32 xs.length) (h12 : c.get 12 = BitVec.ofNat 32 cap) (h14 : c.get 14 = BitVec.ofNat 32 pos)
    (hf : xs.length ≤ cap-pos) :
    ∃ d n, n ≤ 6*xs.length+22 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,CursorMemory.memory ram obj dst pos xs⟩ ∧
      d.pc = 0x800022dc#32 ∧ d.get 2 = sp ∧ d.get 8 = BitVec.ofNat 32 xs.length ∧ d.get 18 = c.get 18 ∧ d.sameCsr c := by
  obtain ⟨a,ta,apc,a1,a10,a12,a9,a19,aframe,acsr⟩ := CursorCall.contract B c ram obj dst cap pos xs.length hp h10 h8 h12 h14
    h.object h.objectAligned h.pointerWord h.capacity h.position hf
  have a11 : a.get 11 = src := (aframe 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h11
  have asp : a.get 2 = sp := (aframe 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsp
  have a8 : a.get 8 = BitVec.ofNat 32 xs.length := (aframe 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8
  have a18 : a.get 18 = c.get 18 := aframe 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hfit : pos+xs.length ≤ cap := by have := h.position;omega
  obtain ⟨u,n,hn,tu,upc,usp,_,uframe,ucsr,_⟩ := SmallCopy.contract B a ram src (dst+BitVec.ofNat 32 pos) xs apc a10 a11 a12 h.short h.source
    (Subregion.block h.output h.capacity h.nowrap pos xs.length hfit) (Subregion.nowrap h.nowrap pos xs.length hfit)
    (Subregion.right h.sourceOutput pos xs.length hfit)
  have upc' : u.pc = 0x800022d8#32 := by rw [upc,a1];decide +kernel
  have u19 : u.get 19 = obj := (uframe 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a19
  have u9 : u.get 9 = BitVec.ofNat 32 (pos+xs.length) := (uframe 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a9
  have u8 : u.get 8 = BitVec.ofNat 32 xs.length := (uframe 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a8
  have u18 : u.get 18 = c.get 18 := (uframe 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a18
  have ts := CursorFinish.store B u (ByteWrite.write ram (dst+BitVec.ofNat 32 pos) xs) obj (pos+xs.length) upc' u19 u9 h.object h.objectAligned
  exact ⟨u.goto 0x800022dc#32,10+n+1,by omega,(ta.trans tu).trans (.single ts),rfl,usp.trans asp,u8,u18,ucsr.trans acsr⟩
end E5R.Thermostat.CursorWritten
