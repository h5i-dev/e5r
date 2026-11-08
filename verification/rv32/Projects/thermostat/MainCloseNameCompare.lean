import Projects.thermostat.MainCloseCode
import Projects.thermostat.MainCloseFoldCertificates
import Projects.thermostat.AsciiFoldCompare
set_option autoImplicit false
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainCloseNameCompare
open E5R E5R.Thermostat

theorem at2147493018 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x8000249a#32) (h15 : c.get 15=base) (hliteral : c.get 6=99#32)
    (memory : B.inRam (base+0#32) 1=true) (data : ram (base+0#32)=byte) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.lower byte≠99#8 then 0x80002474#32 else 0x800024b0#32) ∧
      d.get 14=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat ∧
      (∀ r : Reg, r≠14 → r≠22 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [show 0x8000249a#32+4#32+10#32+4#32+0xffffffc8#32=0x80002474#32 by decide +kernel,
      show 0x8000249a#32+4#32+10#32+4#32+4#32=0x800024b0#32 by decide +kernel] using
    AsciiFoldCompare.contract B img c ram 0x8000249a#32 base 0#32 4#32 0xffffffc8#32 15 14 22 6 false byte 99#8
      hp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h15 hliteral memory data re2147493018
      (by simpa only [show 0x8000249a#32+4#32=0x8000249e#32 by decide +kernel] using MainCloseFoldCertificates.at2147493022)
      (by decide) (by decide)
      (by simpa only [show 0x8000249a#32+4#32+10#32+4#32=0x800024ac#32 by decide +kernel] using re2147493036)

theorem at2147493040 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x800024b0#32) (h15 : c.get 15=base) (hliteral : c.get 7=111#32)
    (memory : B.inRam (base+1#32) 1=true) (data : ram (base+1#32)=byte) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.lower byte≠111#8 then 0x80002474#32 else 0x800024c6#32) ∧
      d.get 14=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat ∧
      (∀ r : Reg, r≠14 → r≠22 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [show 0x800024b0#32+4#32+10#32+4#32+0xffffffb2#32=0x80002474#32 by decide +kernel,
      show 0x800024b0#32+4#32+10#32+4#32+4#32=0x800024c6#32 by decide +kernel] using
    AsciiFoldCompare.contract B img c ram 0x800024b0#32 base 1#32 4#32 0xffffffb2#32 15 14 22 7 false byte 111#8
      hp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h15 hliteral memory data re2147493040
      (by simpa only [show 0x800024b0#32+4#32=0x800024b4#32 by decide +kernel] using MainCloseFoldCertificates.at2147493044)
      (by decide) (by decide)
      (by simpa only [show 0x800024b0#32+4#32+10#32+4#32=0x800024c2#32 by decide +kernel] using re2147493058)

theorem at2147493062 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x800024c6#32) (h15 : c.get 15=base) (hliteral : c.get 28=110#32)
    (memory : B.inRam (base+2#32) 1=true) (data : ram (base+2#32)=byte) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.lower byte≠110#8 then 0x80002474#32 else 0x800024dc#32) ∧
      d.get 14=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat ∧
      (∀ r : Reg, r≠14 → r≠22 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [show 0x800024c6#32+4#32+10#32+4#32+0xffffff9c#32=0x80002474#32 by decide +kernel,
      show 0x800024c6#32+4#32+10#32+4#32+4#32=0x800024dc#32 by decide +kernel] using
    AsciiFoldCompare.contract B img c ram 0x800024c6#32 base 2#32 4#32 0xffffff9c#32 15 14 22 28 false byte 110#8
      hp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h15 hliteral memory data re2147493062
      (by simpa only [show 0x800024c6#32+4#32=0x800024ca#32 by decide +kernel] using MainCloseFoldCertificates.at2147493066)
      (by decide) (by decide)
      (by simpa only [show 0x800024c6#32+4#32+10#32+4#32=0x800024d8#32 by decide +kernel] using re2147493080)

theorem at2147493084 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x800024dc#32) (h15 : c.get 15=base) (hliteral : c.get 28=110#32)
    (memory : B.inRam (base+3#32) 1=true) (data : ram (base+3#32)=byte) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.lower byte≠110#8 then 0x80002474#32 else 0x800024f2#32) ∧
      d.get 14=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat ∧
      (∀ r : Reg, r≠14 → r≠22 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [show 0x800024dc#32+4#32+10#32+4#32+0xffffff86#32=0x80002474#32 by decide +kernel,
      show 0x800024dc#32+4#32+10#32+4#32+4#32=0x800024f2#32 by decide +kernel] using
    AsciiFoldCompare.contract B img c ram 0x800024dc#32 base 3#32 4#32 0xffffff86#32 15 14 22 28 false byte 110#8
      hp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h15 hliteral memory data re2147493084
      (by simpa only [show 0x800024dc#32+4#32=0x800024e0#32 by decide +kernel] using MainCloseFoldCertificates.at2147493088)
      (by decide) (by decide)
      (by simpa only [show 0x800024dc#32+4#32+10#32+4#32=0x800024ee#32 by decide +kernel] using re2147493102)

theorem at2147493106 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x800024f2#32) (h15 : c.get 15=base) (hliteral : c.get 29=101#32)
    (memory : B.inRam (base+4#32) 1=true) (data : ram (base+4#32)=byte) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.lower byte≠101#8 then 0x80002474#32 else 0x80002508#32) ∧
      d.get 14=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat ∧
      (∀ r : Reg, r≠14 → r≠22 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [show 0x800024f2#32+4#32+10#32+4#32+0xffffff70#32=0x80002474#32 by decide +kernel,
      show 0x800024f2#32+4#32+10#32+4#32+4#32=0x80002508#32 by decide +kernel] using
    AsciiFoldCompare.contract B img c ram 0x800024f2#32 base 4#32 4#32 0xffffff70#32 15 14 22 29 false byte 101#8
      hp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h15 hliteral memory data re2147493106
      (by simpa only [show 0x800024f2#32+4#32=0x800024f6#32 by decide +kernel] using MainCloseFoldCertificates.at2147493110)
      (by decide) (by decide)
      (by simpa only [show 0x800024f2#32+4#32+10#32+4#32=0x80002504#32 by decide +kernel] using re2147493124)

theorem at2147493128 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x80002508#32) (h15 : c.get 15=base) (hliteral : c.get 6=99#32)
    (memory : B.inRam (base+5#32) 1=true) (data : ram (base+5#32)=byte) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.lower byte≠99#8 then 0x80002474#32 else 0x8000251e#32) ∧
      d.get 14=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat ∧
      (∀ r : Reg, r≠14 → r≠22 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [show 0x80002508#32+4#32+10#32+4#32+0xffffff5a#32=0x80002474#32 by decide +kernel,
      show 0x80002508#32+4#32+10#32+4#32+4#32=0x8000251e#32 by decide +kernel] using
    AsciiFoldCompare.contract B img c ram 0x80002508#32 base 5#32 4#32 0xffffff5a#32 15 14 22 6 false byte 99#8
      hp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h15 hliteral memory data re2147493128
      (by simpa only [show 0x80002508#32+4#32=0x8000250c#32 by decide +kernel] using MainCloseFoldCertificates.at2147493132)
      (by decide) (by decide)
      (by simpa only [show 0x80002508#32+4#32+10#32+4#32=0x8000251a#32 by decide +kernel] using re2147493146)

theorem at2147493150 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x8000251e#32) (h15 : c.get 15=base) (hliteral : c.get 30=116#32)
    (memory : B.inRam (base+6#32) 1=true) (data : ram (base+6#32)=byte) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.lower byte≠116#8 then 0x80002474#32 else 0x80002534#32) ∧
      d.get 14=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat ∧
      (∀ r : Reg, r≠14 → r≠22 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [show 0x8000251e#32+4#32+10#32+4#32+0xffffff44#32=0x80002474#32 by decide +kernel,
      show 0x8000251e#32+4#32+10#32+4#32+4#32=0x80002534#32 by decide +kernel] using
    AsciiFoldCompare.contract B img c ram 0x8000251e#32 base 6#32 4#32 0xffffff44#32 15 14 22 30 false byte 116#8
      hp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h15 hliteral memory data re2147493150
      (by simpa only [show 0x8000251e#32+4#32=0x80002522#32 by decide +kernel] using MainCloseFoldCertificates.at2147493154)
      (by decide) (by decide)
      (by simpa only [show 0x8000251e#32+4#32+10#32+4#32=0x80002530#32 by decide +kernel] using re2147493168)

theorem at2147493172 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x80002534#32) (h15 : c.get 15=base) (hliteral : c.get 31=105#32)
    (memory : B.inRam (base+7#32) 1=true) (data : ram (base+7#32)=byte) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.lower byte≠105#8 then 0x80002474#32 else 0x8000254a#32) ∧
      d.get 14=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat ∧
      (∀ r : Reg, r≠14 → r≠22 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [show 0x80002534#32+4#32+10#32+4#32+0xffffff2e#32=0x80002474#32 by decide +kernel,
      show 0x80002534#32+4#32+10#32+4#32+4#32=0x8000254a#32 by decide +kernel] using
    AsciiFoldCompare.contract B img c ram 0x80002534#32 base 7#32 4#32 0xffffff2e#32 15 14 22 31 false byte 105#8
      hp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h15 hliteral memory data re2147493172
      (by simpa only [show 0x80002534#32+4#32=0x80002538#32 by decide +kernel] using MainCloseFoldCertificates.at2147493176)
      (by decide) (by decide)
      (by simpa only [show 0x80002534#32+4#32+10#32+4#32=0x80002546#32 by decide +kernel] using re2147493190)

theorem at2147493194 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x8000254a#32) (h15 : c.get 15=base) (hliteral : c.get 7=111#32)
    (memory : B.inRam (base+8#32) 1=true) (data : ram (base+8#32)=byte) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.lower byte≠111#8 then 0x80002474#32 else 0x80002560#32) ∧
      d.get 14=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat ∧
      (∀ r : Reg, r≠14 → r≠22 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [show 0x8000254a#32+4#32+10#32+4#32+0xffffff18#32=0x80002474#32 by decide +kernel,
      show 0x8000254a#32+4#32+10#32+4#32+4#32=0x80002560#32 by decide +kernel] using
    AsciiFoldCompare.contract B img c ram 0x8000254a#32 base 8#32 4#32 0xffffff18#32 15 14 22 7 false byte 111#8
      hp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h15 hliteral memory data re2147493194
      (by simpa only [show 0x8000254a#32+4#32=0x8000254e#32 by decide +kernel] using MainCloseFoldCertificates.at2147493198)
      (by decide) (by decide)
      (by simpa only [show 0x8000254a#32+4#32+10#32+4#32=0x8000255c#32 by decide +kernel] using re2147493212)

theorem at2147493216 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x80002560#32) (h15 : c.get 15=base) (hliteral : c.get 28=110#32)
    (memory : B.inRam (base+9#32) 1=true) (data : ram (base+9#32)=byte) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.lower byte≠110#8 then 0x80002474#32 else 0x80002574#32) ∧
      d.get 14=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat ∧
      (∀ r : Reg, r≠14 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [show 0x80002560#32+4#32+10#32+2#32+0xffffff04#32=0x80002474#32 by decide +kernel,
      show 0x80002560#32+4#32+10#32+2#32+4#32=0x80002574#32 by decide +kernel] using
    AsciiFoldCompare.contract B img c ram 0x80002560#32 base 9#32 2#32 0xffffff04#32 15 14 15 28 true byte 110#8
      hp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h15 hliteral memory data re2147493216
      (by simpa only [show 0x80002560#32+4#32=0x80002564#32 by decide +kernel] using MainCloseFoldCertificates.at2147493220)
      (by decide) (by decide)
      (by simpa only [show 0x80002560#32+4#32+10#32+2#32=0x80002570#32 by decide +kernel] using re2147493232)
end E5R.Thermostat.MainCloseNameCompare
