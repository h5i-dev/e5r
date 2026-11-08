import Projects.thermostat.SmallCopyStart
import Projects.thermostat.SmallCopyLoop
import Projects.thermostat.SmallCopyReturn
import Projects.thermostat.Interrupt
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.SmallCopy
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r ≠ 2 → r ≠ 6 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → d.get r = c.get r

/-- Full real memcpy for <16 checked source bytes, including trampoline,
    empty input, byte loop and realRET. The source and destination do not alias. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst : Word) (xs : List (BitVec 8))
    (hp : c.pc = 0x80005182#32) (h10 : c.get 10 = dst) (h11 : c.get 11 = src)
    (h12 : c.get 12 = BitVec.ofNat 32 xs.length) (hn : xs.length < 16)
    (hs : ReadBytes.Span B img ram src xs) (hd : Memory.Block B dst xs.length)
    (hw : dst.toNat+xs.length < 2^32) (hsep : WordRegions.Disjoint src xs.length dst xs.length) :
    ∃ d n, n ≤ 6*xs.length+11 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ByteWrite.write ram dst xs⟩ ∧
      d.pc = c.get 1 &&& ~~~1 ∧ d.get 2 = c.get 2 ∧ d.get 10 = dst ∧ Frame c d ∧ d.sameCsr c ∧
      Bytes.Span B (ByteWrite.write ram dst xs) dst xs := by
  obtain ⟨a,k,hk,ta,apc,asp,a13,a12,aframe,acsr⟩ := SmallCopyStart.contract B c ram dst xs.length hp h10 h12 hn hw
  have a1 : a.get 1 = c.get 1 := aframe 1 (by decide) (by decide) (by decide) (by decide)
  have a11 : a.get 11 = src := (aframe 11 (by decide) (by decide) (by decide) (by decide)).trans h11
  cases xs with
  | nil =>
    have apc' : a.pc = 0x8000530c#32 := by simpa only [List.length_nil,ite_true] using apc
    obtain ⟨d,td,dpc,dsp,dframe,dcsr⟩ := SmallCopyReturn.contract B a ram apc'
    refine ⟨d,k+2,by simp only [List.length_nil];omega,ta.trans td,by rw [dpc,a1],?_,?_,?_,dcsr.trans acsr,ByteWrite.span hd hs.length⟩
    · rw [dsp,asp,BitVec.add_assoc,show 0xfffffff0#32+16#32 = 0#32 by decide +kernel,BitVec.add_zero]
    · exact ((dframe 10 (by decide)).trans (aframe 10 (by decide) (by decide) (by decide) (by decide))).trans h10
    · intro r h2 h6 h11 h12 h13 h14
      exact (dframe r h2).trans (aframe r h2 h6 h13 h14)
  | cons b bs =>
    have apc' : a.pc = 0x800052fc#32 := by
      have hne : (b::bs).length ≠ 0 := by simp
      simpa only [ite_eq_right hne] using apc
    obtain ⟨u,tu,upc,_,_,_,uframe,ucsr⟩ := SmallCopyLoop.contract B ram (b::bs) src dst hs hd (by simp) hsep a apc' a11 a13 a12
    have u1 : u.get 1 = c.get 1 := (uframe 1 (by decide) (by decide) (by decide) (by decide)).trans a1
    have usp : u.get 2 = c.get 2+0xfffffff0#32 := (uframe 2 (by decide) (by decide) (by decide) (by decide)).trans asp
    obtain ⟨d,td,dpc,dsp,dframe,dcsr⟩ := SmallCopyReturn.contract B u (ByteWrite.write ram dst (b::bs)) upc
    refine ⟨d,k+6*(b::bs).length+2,by omega,(ta.trans tu).trans td,by rw [dpc,u1],?_,?_,?_,(dcsr.trans ucsr).trans acsr,ByteWrite.span hd hs.length⟩
    · rw [dsp,usp,BitVec.add_assoc,show 0xfffffff0#32+16#32 = 0#32 by decide +kernel,BitVec.add_zero]
    · exact ((dframe 10 (by decide)).trans ((uframe 10 (by decide) (by decide) (by decide) (by decide)).trans
        (aframe 10 (by decide) (by decide) (by decide) (by decide)))).trans h10
    · intro r h2 h6 h11 h12 h13 h14
      exact (dframe r h2).trans ((uframe r h11 h12 h13 h14).trans (aframe r h2 h6 h13 h14))
end E5R.Thermostat.SmallCopy
