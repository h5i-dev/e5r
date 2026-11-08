import Projects.thermostat.MainCloseCode
import Projects.thermostat.TrimAdvanceProgram
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseTrimAdvance
open E5R E5R.Thermostat

theorem leftCertificate : TrimAdvanceProgram.Certificate img 0x800025cc#32 0x1#32 0xffffffe4#32 24 15 := by
  refine ⟨by decide,by decide,by decide,by decide,re2147493324,?_,?_⟩
  · simpa only [show 0x800025cc#32+2#32=0x800025ce#32 by decide +kernel] using re2147493326
  · simpa only [show 0x800025cc#32+4#32=0x800025d0#32 by decide +kernel] using re2147493328

theorem left (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (n : Nat)
    (positive : 0<n) (bound : n<2^32) (hp : c.pc=0x800025cc#32)
    (count : c.get 24=BitVec.ofNat 32 n) (pointer : c.get 15=p) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if n=1 then 0x800025d4#32 else 0x800025b4#32) ∧ d.get 24=BitVec.ofNat 32 (n-1) ∧ d.get 15=p+0x1#32 ∧
      (∀ r : Reg, r≠24 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [show 0x800025cc#32+8#32=0x800025d4#32 by decide +kernel,
    show 0x800025cc#32+4#32+0xffffffe4#32=0x800025b4#32 by decide +kernel] using
    TrimAdvanceProgram.contract B img c ram 0x800025cc#32 0x1#32 0xffffffe4#32 p 24 15 n leftCertificate
      (by decide) (by decide) (by decide) positive bound hp count pointer

theorem rightCertificate : TrimAdvanceProgram.Certificate img 0x800025fe#32 0xffffffff#32 0xffffffe6#32 24 22 := by
  refine ⟨by decide,by decide,by decide,by decide,re2147493374,?_,?_⟩
  · simpa only [show 0x800025fe#32+2#32=0x80002600#32 by decide +kernel] using re2147493376
  · simpa only [show 0x800025fe#32+4#32=0x80002602#32 by decide +kernel] using re2147493378

theorem right (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (n : Nat)
    (positive : 0<n) (bound : n<2^32) (hp : c.pc=0x800025fe#32)
    (count : c.get 24=BitVec.ofNat 32 n) (pointer : c.get 22=p) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if n=1 then 0x80002606#32 else 0x800025e8#32) ∧ d.get 24=BitVec.ofNat 32 (n-1) ∧ d.get 22=p+0xffffffff#32 ∧
      (∀ r : Reg, r≠24 → r≠22 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [show 0x800025fe#32+8#32=0x80002606#32 by decide +kernel,
    show 0x800025fe#32+4#32+0xffffffe6#32=0x800025e8#32 by decide +kernel] using
    TrimAdvanceProgram.contract B img c ram 0x800025fe#32 0xffffffff#32 0xffffffe6#32 p 24 22 n rightCertificate
      (by decide) (by decide) (by decide) positive bound hp count pointer
end E5R.Thermostat.MainCloseTrimAdvance
