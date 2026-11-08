import Projects.thermostat.MainCloseCode
import Projects.thermostat.AsciiWhitespaceProgram
import Projects.thermostat.QuietByteLoad
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.MainCloseWhitespace
open E5R E5R.Thermostat

theorem left : AsciiWhitespaceProgram.Certificate img 0x800025b8#32 4#32 0x28#32 0x1c#32 25 26 9 21 := by
  refine ⟨by decide,by decide,by decide,by decide,by decide,by decide,by decide,re2147493304,?_,?_,?_,?_⟩
  · simpa only [show 0x800025b8#32+4#32=0x800025bc#32 by decide +kernel] using re2147493308
  · simpa only [show 0x800025b8#32+4#32+4#32=0x800025c0#32 by decide +kernel] using re2147493312
  · simpa only [show 0x800025b8#32+4#32+8#32=0x800025c4#32 by decide +kernel] using re2147493316
  · simpa only [show 0x800025b8#32+4#32+12#32=0x800025c8#32 by decide +kernel] using re2147493320

theorem right : AsciiWhitespaceProgram.Certificate img 0x800025ec#32 2#32 0x1a#32 0xe#32 23 23 9 21 := by
  refine ⟨by decide,by decide,by decide,by decide,by decide,by decide,by decide,re2147493356,?_,?_,?_,?_⟩
  · simpa only [show 0x800025ec#32+2#32=0x800025ee#32 by decide +kernel] using re2147493358
  · simpa only [show 0x800025ec#32+2#32+4#32=0x800025f2#32 by decide +kernel] using re2147493362
  · simpa only [show 0x800025ec#32+2#32+8#32=0x800025f6#32 by decide +kernel] using re2147493366
  · simpa only [show 0x800025ec#32+2#32+12#32=0x800025fa#32 by decide +kernel] using re2147493370

/-- Real left-trim load and classification, retaining the loaded byte for the
    optimized first-character close comparison. -/
theorem leftTest (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (byte : BitVec 8)
    (hp : c.pc=0x800025b4#32) (h15 : c.get 15=p) (h9 : c.get 9=23#32) (h21 : c.get 21=0x80001b#32)
    (memory : B.inRam p 1=true) (data : ram p=byte) :
    ∃ n d, n≤6 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if TrimMath.white byte then 0x800025cc#32 else 0x800025e4#32) ∧
      d.get 25=BitVec.ofNat 32 byte.toNat ∧
      (∀ r : Reg, r≠25 → r≠26 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,load,pa,av,ar,ac⟩ := QuietByteLoad.contract B img c ram 0x800025b4#32 p 0#32 25 15 byte
    hp (by decide) (by decide) re2147493300 h15 (by simpa only [BitVec.add_zero] using memory) (by simpa only [BitVec.add_zero] using data)
  have pa' : a.pc=0x800025b8#32 := by simpa only [show 0x800025b4#32+4#32=0x800025b8#32 by decide +kernel] using pa
  obtain ⟨n,d,nb,tests,pd,dr,dc⟩ := AsciiWhitespaceProgram.contract B img a ram 0x800025b8#32 4#32 0x28#32 0x1c#32 25 26 9 21 byte left
    (by decide) (by decide) (by decide) pa' av ((ar 9 (by decide)).trans h9) ((ar 21 (by decide)).trans h21)
  refine ⟨1+n,d,by omega,load.trans tests,?_,(dr 25 (by decide)).trans av,?_,dc.trans ac⟩
  · simpa only [show 0x800025b8#32+4#32+16#32=0x800025cc#32 by decide +kernel,
      show 0x800025b8#32+4#32+0x28#32=0x800025e4#32 by decide +kernel] using pd
  · intro r n25 n26
    exact (dr r n26).trans (ar r n25)

/-- The backwards test loads its byte into the same register used by its
    classifier, unlike the cached forward test. -/
theorem rightTest (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (byte : BitVec 8)
    (hp : c.pc=0x800025e8#32) (h22 : c.get 22=p) (h9 : c.get 9=23#32) (h21 : c.get 21=0x80001b#32)
    (memory : B.inRam p 1=true) (data : ram p=byte) :
    ∃ n d, n≤6 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if TrimMath.white byte then 0x800025fe#32 else 0x80002608#32) ∧
      (∀ r : Reg, r≠23 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,load,pa,av,ar,ac⟩ := QuietByteLoad.contract B img c ram 0x800025e8#32 p 0#32 23 22 byte
    hp (by decide) (by decide) re2147493352 h22 (by simpa only [BitVec.add_zero] using memory) (by simpa only [BitVec.add_zero] using data)
  have pa' : a.pc=0x800025ec#32 := by simpa only [show 0x800025e8#32+4#32=0x800025ec#32 by decide +kernel] using pa
  obtain ⟨n,d,nb,tests,pd,dr,dc⟩ := AsciiWhitespaceProgram.contract B img a ram 0x800025ec#32 2#32 0x1a#32 0xe#32 23 23 9 21 byte right
    (by decide) (by decide) (by decide) pa' av ((ar 9 (by decide)).trans h9) ((ar 21 (by decide)).trans h21)
  refine ⟨1+n,d,by omega,load.trans tests,?_,fun r ne => (dr r ne).trans (ar r ne),dc.trans ac⟩
  simpa only [show 0x800025ec#32+2#32+16#32=0x800025fe#32 by decide +kernel,
    show 0x800025ec#32+2#32+0x1a#32=0x80002608#32 by decide +kernel] using pd
end E5R.Thermostat.MainCloseWhitespace
