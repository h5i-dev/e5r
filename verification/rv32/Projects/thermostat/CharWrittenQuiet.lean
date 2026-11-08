-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CharWritten
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.CharCallQuiet
import Projects.thermostat.CharFinishQuiet
import Projects.thermostat.SmallCopyQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.CharWritten
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp obj dst : Word) (cap pos : Nat) (b : BitVec 8)
    (h : CharInput.Data B ram sp obj dst cap pos)
    (hp : c.pc = 0x80002394#32) (hsp : c.get 2 = sp) (h10 : c.get 10 = obj) (h8 : c.get 8 = 1#32)
    (h12 : c.get 12 = BitVec.ofNat 32 cap) (h11 : c.get 11 = BitVec.ofNat 32 pos)
    (hs : ReadBytes.Span B img ram (sp+8#32) [b]) (hf : 1 ≤ cap-pos) :
    ∃ d n, n ≤ 29 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,CharMemory.memory ram obj dst pos [b]⟩ ∧
      d.pc = 0x800023b8#32 ∧ d.get 2 = sp ∧ d.get 8 = 1#32 ∧ d.get 18 = c.get 18 ∧ d.sameCsr c ∧ HighFrame.Frame c d := by
  obtain ⟨a,ta,apc,a1,a10,a11,a12,a9,a19,aframe,acsr⟩ := E5R.Thermostat.CharCall.contract_quiet B c ram sp obj dst cap pos 1 hp hsp h10 h8 h12 h11
    h.object h.objectAligned h.pointerWord h.capacity h.position hf
  have asp : a.get 2 = sp := (aframe 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsp
  have a8 : a.get 8 = 1#32 := (aframe 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8
  have a18 : a.get 18 = c.get 18 := aframe 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hfit : pos+1 ≤ cap := by have := h.position;omega
  have sep : WordRegions.Disjoint (sp+8#32) 1 (dst+BitVec.ofNat 32 pos) 1 :=
    WordRegions.symm (Subregion.right (Subregion.left h.outputStack pos 1 hfit) 8 1 (by decide))
  obtain ⟨u,n,hn,tu,upc,usp,_,uframe,ucsr,_⟩ := E5R.Thermostat.SmallCopy.contract_quiet B a ram (sp+8#32) (dst+BitVec.ofNat 32 pos) [b]
    apc a10 a11 a12 (by change 1 < 16;decide) hs (Subregion.block h.output h.capacity h.nowrap pos 1 hfit)
    (Subregion.nowrap h.nowrap pos 1 hfit) sep
  have upc' : u.pc = 0x800023b4#32 := by rw [upc,a1];decide +kernel
  have u19 : u.get 19 = obj := (uframe 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a19
  have u9 : u.get 9 = BitVec.ofNat 32 (pos+1) := (uframe 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a9
  have u8 : u.get 8 = 1#32 := (uframe 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a8
  have u18 : u.get 18 = c.get 18 := (uframe 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a18
  have ts := E5R.Thermostat.CharFinish.store_quiet B u (ByteWrite.write ram (dst+BitVec.ofNat 32 pos) [b]) obj (pos+1) upc' u19 u9 h.object h.objectAligned
  refine ⟨u.goto 0x800023b8#32,11+n+1,by change n ≤ 6*1+11 at hn;omega,(ta.trans tu).trans (.single ts),rfl,usp.trans asp,u8,u18,ucsr.trans acsr,?_⟩
  intro r hr
  have hn (k : Reg) (hk : k.val < 20) : r ≠ k := HighFrame.ne r k hr hk
  exact (uframe r (hn 2 (by decide)) (hn 6 (by decide)) (hn 11 (by decide)) (hn 12 (by decide)) (hn 13 (by decide)) (hn 14 (by decide))).trans
    (aframe r (hn 1 (by decide)) (hn 9 (by decide)) (hn 10 (by decide)) (hn 11 (by decide)) (hn 12 (by decide)) (hn 19 (by decide)))

end E5R.Thermostat.CharWritten
