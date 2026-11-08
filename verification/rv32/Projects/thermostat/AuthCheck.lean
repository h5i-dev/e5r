import Projects.thermostat.AuthSetup
import Projects.thermostat.AuthCompare
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.AuthCheck
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) (xs ys : List (BitVec 8)) : Word → BitVec 8 :=
  if xs.length = 7 then ramPut ram (sp+24#32) (AuthSpec.diff xs ys 0#8) else ram

/-- Actual configured-key length guard, pointer setup, exhaustive byte loop,
    black_box stack roundtrip and acceptance branch. Header lookup and prefix
    stripping must establish these actual token bytes upstream. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (eng sp header key : Word)
    (xs ys : List (BitVec 8)) (hys : ys.length = 7) (hl : xs.length+7 < 2^32)
    (hx : ReadBytes.Span B img ram (header+7#32) xs) (hy : ReadBytes.Span B img ram key ys)
    (hp : c.pc = 0x80000568#32) (hsp : c.get 2 = sp)
    (h23 : c.get 23 = eng) (h24 : c.get 24 = header) (h25 : c.get 25 = BitVec.ofNat 32 (xs.length+7))
    (hm : Memory.Block B eng 24) (ha : eng.toNat%4 = 0) (hs : Memory.Block B sp 25)
    (hlen : ramRead ram (eng+20#32) .w = 7#32) (hkey : ramRead ram (eng+16#32) .w = key) :
    ∃ d n, n ≤ 61 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,memory ram sp xs ys⟩ ∧
      d.pc = (if xs = ys then 0x800005e2#32 else 0x800005a2#32) ∧
      (∀ r : Reg, r.val < 10 ∨ 15 < r.val → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,n,hn,ta,apc,fields,aframe,acsr⟩ := AuthSetup.contract B c ram eng header key xs.length hl hp h23 h24 h25 hm ha hlen hkey
  have ne (r k : Reg) (hr : r.val < 10 ∨ 15 < r.val) (hk : 10 ≤ k.val ∧ k.val ≤ 15) : r ≠ k := by
    intro he;have hv := congrArg Fin.val he;omega
  by_cases he : xs.length = 7
  · have apc' : a.pc = 0x80000582#32 := by simpa only [ite_eq_left he] using apc
    obtain ⟨a10,a11,a12,a13⟩ := fields he
    have hend : a.get 13 = key+BitVec.ofNat 32 xs.length := by simpa only [he] using a13
    have hne : xs ≠ [] := by intro hh;rw [hh] at he;contradiction
    obtain ⟨d,td,dpc,dframe,dcsr⟩ := AuthCompare.contract B a ram sp (header+7#32) key xs ys
      (he.trans hys.symm) hne hx hy apc'
      ((aframe 2 (by decide) (by decide) (by decide) (by decide)).trans hsp) hs a10 a11 a12 hend
    refine ⟨d,n+(7*xs.length+4),by rw [he];omega,?_,dpc,?_,dcsr.trans acsr⟩
    · simpa only [memory,ite_eq_left he] using ta.trans td
    · intro r hr
      exact (dframe r (ne r 10 hr (by decide)) (ne r 11 hr (by decide)) (ne r 12 hr (by decide))
        (ne r 14 hr (by decide)) (ne r 15 hr (by decide))).trans
        (aframe r (ne r 10 hr (by decide)) (ne r 11 hr (by decide)) (ne r 12 hr (by decide)) (ne r 13 hr (by decide)))
  · have hneq : xs ≠ ys := by intro hh;apply he;rw [hh];exact hys
    refine ⟨a,n,by omega,?_,?_,?_,acsr⟩
    · simpa only [memory,ite_eq_right he] using ta
    · simpa only [ite_eq_right hneq,ite_eq_right he] using apc
    · intro r hr
      exact aframe r (ne r 10 hr (by decide)) (ne r 11 hr (by decide)) (ne r 12 hr (by decide)) (ne r 13 hr (by decide))
theorem closed_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (eng sp header key : Word)
    (xs ys : List (BitVec 8)) (hys : ys.length = 7) (hl : xs.length+7 < 2^32)
    (hx : ReadBytes.Span B img ram (header+7#32) xs) (hy : ReadBytes.Span B img ram key ys)
    (hp : c.pc = 0x80000568#32) (hsp : c.get 2 = sp)
    (h23 : c.get 23 = eng) (h24 : c.get 24 = header) (h25 : c.get 25 = BitVec.ofNat 32 (xs.length+7))
    (hm : Memory.Block B eng 24) (ha : eng.toNat%4 = 0) (hs : Memory.Block B sp 25)
    (hlen : ramRead ram (eng+20#32) .w = 7#32) (hkey : ramRead ram (eng+16#32) .w = key) (hmask : c.mie_ = false) :
    ∃ d n, n ≤ 61 ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,memory ram sp xs ys⟩ ∧
      d.pc = (if xs = ys then 0x800005e2#32 else 0x800005a2#32) ∧
      (∀ r : Reg, r.val < 10 ∨ 15 < r.val → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,n,hn,ht,hpc,hframe,hcsr⟩ := contract B c ram eng sp header key xs ys hys hl hx hy hp hsp h23 h24 h25 hm ha hs hlen hkey
  exact ⟨d,n,hn,Interrupt.close ht hmask,hpc,hframe,hcsr⟩
end E5R.Thermostat.AuthCheck
