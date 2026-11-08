-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CursorWrittenFull
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.CursorCallQuiet
import Projects.thermostat.CursorFinishQuiet
import Projects.thermostat.SmallCopyQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.CursorWritten
theorem contract_full_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp obj src dst : Word) (cap pos : Nat) (xs : List (BitVec 8))
    (h : CursorInput.Layout B ram sp obj src dst cap pos xs)
    (hp : c.pc = 0x800022ba#32) (hsp : c.get 2 = sp) (h10 : c.get 10 = obj) (h11 : c.get 11 = src)
    (h8 : c.get 8 = BitVec.ofNat 32 xs.length) (h12 : c.get 12 = BitVec.ofNat 32 cap) (h14 : c.get 14 = BitVec.ofNat 32 pos)
    (hf : xs.length ≤ cap-pos) :
    ∃ d n, n ≤ 6*xs.length+22 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,CursorMemory.memory ram obj dst pos xs⟩ ∧
      d.pc = 0x800022dc#32 ∧ d.get 2 = sp ∧ d.get 8 = BitVec.ofNat 32 xs.length ∧ d.get 18 = c.get 18 ∧ d.sameCsr c ∧ HighFrame.Frame c d := by
  obtain ⟨a,ta,apc,a1,a10,a12,a9,a19,aframe,acsr⟩ := E5R.Thermostat.CursorCall.contract_quiet B c ram obj dst cap pos xs.length hp h10 h8 h12 h14
    h.object h.objectAligned h.pointerWord h.capacity h.position hf
  have a11 : a.get 11 = src := (aframe 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h11
  have asp : a.get 2 = sp := (aframe 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsp
  have a8 : a.get 8 = BitVec.ofNat 32 xs.length := (aframe 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8
  have a18 : a.get 18 = c.get 18 := aframe 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hfit : pos+xs.length ≤ cap := by have := h.position;omega
  obtain ⟨u,n,hn,tu,upc,usp,_,uframe,ucsr,_⟩ := E5R.Thermostat.SmallCopy.contract_quiet B a ram src (dst+BitVec.ofNat 32 pos) xs apc a10 a11 a12 h.short h.source
    (Subregion.block h.output h.capacity h.nowrap pos xs.length hfit) (Subregion.nowrap h.nowrap pos xs.length hfit)
    (Subregion.right h.sourceOutput pos xs.length hfit)
  have upc' : u.pc = 0x800022d8#32 := by rw [upc,a1];decide +kernel
  have u19 : u.get 19 = obj := (uframe 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a19
  have u9 : u.get 9 = BitVec.ofNat 32 (pos+xs.length) := (uframe 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a9
  have u8 : u.get 8 = BitVec.ofNat 32 xs.length := (uframe 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a8
  have u18 : u.get 18 = c.get 18 := (uframe 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a18
  have ts := E5R.Thermostat.CursorFinish.store_quiet B u (ByteWrite.write ram (dst+BitVec.ofNat 32 pos) xs) obj (pos+xs.length) upc' u19 u9 h.object h.objectAligned
  refine ⟨u.goto 0x800022dc#32,10+n+1,by omega,(ta.trans tu).trans (.single ts),rfl,usp.trans asp,u8,u18,ucsr.trans acsr,?_⟩
  intro r hr
  have hn (k : Reg) (hk : k.val < 20) : r ≠ k := HighFrame.ne r k hr hk
  exact (uframe r (hn 2 (by decide)) (hn 6 (by decide)) (hn 11 (by decide)) (hn 12 (by decide)) (hn 13 (by decide)) (hn 14 (by decide))).trans
    (aframe r (hn 1 (by decide)) (hn 9 (by decide)) (hn 10 (by decide)) (hn 12 (by decide)) (hn 13 (by decide)) (hn 19 (by decide)))

end E5R.Thermostat.CursorWritten
