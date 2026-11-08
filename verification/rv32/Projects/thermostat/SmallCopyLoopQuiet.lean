-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.SmallCopyLoop
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.SmallCopyTurnQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.SmallCopyLoop
theorem contract_quiet (B : Board) (ram : Word → BitVec 8) (xs : List (BitVec 8)) (src dst : Word)
    (hs : ReadBytes.Span B img ram src xs) (hd : Memory.Block B dst xs.length) (hne : xs ≠ [])
    (hsep : WordRegions.Disjoint src xs.length dst xs.length)
    (c : Core) (hp : c.pc = 0x800052fc#32) (h11 : c.get 11 = src) (h13 : c.get 13 = dst)
    (h12 : c.get 12 = BitVec.ofNat 32 xs.length) :
    ∃ d, Quiet.Steps B img (6*xs.length) ⟨c,ram⟩ ⟨d,ByteWrite.write ram dst xs⟩ ∧ d.pc = 0x8000530c#32 ∧
      d.get 11 = src+BitVec.ofNat 32 xs.length ∧ d.get 13 = dst+BitVec.ofNat 32 xs.length ∧
      d.get 12 = 0#32 ∧ Frame c d ∧ d.sameCsr c := by
  induction xs generalizing ram src dst c with
  | nil => contradiction
  | cons a as ih =>
    have hr : B.inRam dst 1 = true := by
      simpa only [BitVec.add_zero] using Memory.block_access hd (off := 0) (width := 1) (by decide) (by simp)
    obtain ⟨u,tu,upc,u11,u13,u12,uframe,ucsr⟩ := E5R.Thermostat.SmallCopyTurn.contract_quiet B c ram src dst a (a::as).length
      (by simp) hs.length hp h11 h13 h12 (ReadBytes.head hs) hr
    cases as with
    | nil =>
      exact ⟨u,tu,by simpa only [List.length_cons,List.length_nil,ite_true] using upc,u11,u13,u12,uframe,ucsr⟩
    | cons b bs =>
      have hxs : (b::bs).length < 2^32 := by have := hs.length;simp only [List.length_cons] at this ⊢;omega
      have hs' : ReadBytes.Span B img (ramPut ram dst a) (src+1#32) (b::bs) := by
        apply ReadFrame.span (ReadBytes.tail hs)
        intro i
        apply ramPut_ne
        have hh := hsep ⟨i.val+1,by have := i.isLt;simp only [List.length_cons] at this ⊢;omega⟩ ⟨0,by simp⟩
        simpa only [BitVec.add_zero,BitVec.ofNat_add,BitVec.add_assoc,show i.val+1 = 1+i.val by omega] using hh
      have hd' : Memory.Block B (dst+1#32) (b::bs).length := Memory.sub_block hd (by simp) (by simp;omega)
      have hsep' : WordRegions.Disjoint (src+1#32) (b::bs).length (dst+1#32) (b::bs).length := by
        intro i j
        have hh := hsep ⟨1+i.val,by have := i.isLt;simp only [List.length_cons] at this ⊢;omega⟩
          ⟨1+j.val,by have := j.isLt;simp only [List.length_cons] at this ⊢;omega⟩
        simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hh
      have upc' : u.pc = 0x800052fc#32 := by
        have hn : (a::b::bs).length ≠ 1 := by simp
        simpa only [ite_eq_right hn] using upc
      have u12' : u.get 12 = BitVec.ofNat 32 (b::bs).length := by simpa only [List.length_cons,Nat.add_sub_cancel] using u12
      obtain ⟨d,td,dpc,d11,d13,d12,dframe,dcsr⟩ := ih (ramPut ram dst a) (src+1#32) (dst+1#32) hs' hd' (by simp) hsep' u upc' u11 u13 u12'
      refine ⟨d,?_,dpc,?_,?_,d12,?_,dcsr.trans ucsr⟩
      · have he : 6*(a::b::bs).length = 6+6*(b::bs).length := by simp;omega
        rw [he];exact tu.trans td
      · rw [d11,BitVec.add_assoc,←BitVec.ofNat_add,show 1+(b::bs).length = (a::b::bs).length by simp;omega]
      · rw [d13,BitVec.add_assoc,←BitVec.ofNat_add,show 1+(b::bs).length = (a::b::bs).length by simp;omega]
      · intro r h11 h12 h13 h14
        exact (dframe r h11 h12 h13 h14).trans (uframe r h11 h12 h13 h14)

end E5R.Thermostat.SmallCopyLoop
