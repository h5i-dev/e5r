import Projects.thermostat.MainMethodDecodeCode
import Projects.thermostat.MainMethodByteTest
import Projects.thermostat.MainMethodByteMath
namespace E5R.Thermostat.MainMethodTests
open E5R E5R.Thermostat

theorem at2147487090 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x80000d72#32) (h15 : c.get 15=base)
    (memory : B.inRam (base+0#32) 1=true) (data : ram (base+0#32)=byte) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat=80 then 0x8000111e#32 else 0x80000d7e#32) ∧
      d.get 16=BitVec.ofNat 32 byte.toNat ∧ d.get 17=80#32 ∧
      (∀ r : Reg, r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [decide_eq_true_eq,show 0x80000d72#32+8#32+0x3a4#32=0x8000111e#32 by decide +kernel,show 0x80000d72#32+12#32=0x80000d7e#32 by decide +kernel] using MainMethodByteTest.contract B img c ram 0x80000d72#32 base 0#32 80#32 0x3a4#32 byte .eq (decide (byte.toNat=80)) hp h15 memory data
    (by decide) (by decide) (by decide) (by decide) re2147487090 re2147487094 re2147487098
    (MainMethodByteMath.eqTest byte 80 (by decide))

theorem at2147487110 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x80000d86#32) (h15 : c.get 15=base)
    (memory : B.inRam (base+1#32) 1=true) (data : ram (base+1#32)=byte) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat≠69 then 0x80001160#32 else 0x80000d92#32) ∧
      d.get 16=BitVec.ofNat 32 byte.toNat ∧ d.get 17=69#32 ∧
      (∀ r : Reg, r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [decide_eq_true_eq,show 0x80000d86#32+8#32+0x3d2#32=0x80001160#32 by decide +kernel,show 0x80000d86#32+12#32=0x80000d92#32 by decide +kernel] using MainMethodByteTest.contract B img c ram 0x80000d86#32 base 1#32 69#32 0x3d2#32 byte .ne (decide (byte.toNat≠69)) hp h15 memory data
    (by decide) (by decide) (by decide) (by decide) re2147487110 re2147487114 re2147487118
    (MainMethodByteMath.neTest byte 69 (by decide))

theorem at2147487122 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x80000d92#32) (h15 : c.get 15=base)
    (memory : B.inRam (base+2#32) 1=true) (data : ram (base+2#32)=byte) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat≠65 then 0x80001160#32 else 0x80000d9e#32) ∧
      d.get 16=BitVec.ofNat 32 byte.toNat ∧ d.get 17=65#32 ∧
      (∀ r : Reg, r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [decide_eq_true_eq,show 0x80000d92#32+8#32+0x3c6#32=0x80001160#32 by decide +kernel,show 0x80000d92#32+12#32=0x80000d9e#32 by decide +kernel] using MainMethodByteTest.contract B img c ram 0x80000d92#32 base 2#32 65#32 0x3c6#32 byte .ne (decide (byte.toNat≠65)) hp h15 memory data
    (by decide) (by decide) (by decide) (by decide) re2147487122 re2147487126 re2147487130
    (MainMethodByteMath.neTest byte 65 (by decide))

theorem at2147487152 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x80000db0#32) (h15 : c.get 15=base)
    (memory : B.inRam (base+0#32) 1=true) (data : ram (base+0#32)=byte) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat≠68 then 0x80001160#32 else 0x80000dbc#32) ∧
      d.get 16=BitVec.ofNat 32 byte.toNat ∧ d.get 17=68#32 ∧
      (∀ r : Reg, r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [decide_eq_true_eq,show 0x80000db0#32+8#32+0x3a8#32=0x80001160#32 by decide +kernel,show 0x80000db0#32+12#32=0x80000dbc#32 by decide +kernel] using MainMethodByteTest.contract B img c ram 0x80000db0#32 base 0#32 68#32 0x3a8#32 byte .ne (decide (byte.toNat≠68)) hp h15 memory data
    (by decide) (by decide) (by decide) (by decide) re2147487152 re2147487156 re2147487160
    (MainMethodByteMath.neTest byte 68 (by decide))

theorem at2147487164 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x80000dbc#32) (h15 : c.get 15=base)
    (memory : B.inRam (base+1#32) 1=true) (data : ram (base+1#32)=byte) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat≠69 then 0x80001160#32 else 0x80000dc8#32) ∧
      d.get 16=BitVec.ofNat 32 byte.toNat ∧ d.get 17=69#32 ∧
      (∀ r : Reg, r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [decide_eq_true_eq,show 0x80000dbc#32+8#32+0x39c#32=0x80001160#32 by decide +kernel,show 0x80000dbc#32+12#32=0x80000dc8#32 by decide +kernel] using MainMethodByteTest.contract B img c ram 0x80000dbc#32 base 1#32 69#32 0x39c#32 byte .ne (decide (byte.toNat≠69)) hp h15 memory data
    (by decide) (by decide) (by decide) (by decide) re2147487164 re2147487168 re2147487172
    (MainMethodByteMath.neTest byte 69 (by decide))

theorem at2147487176 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x80000dc8#32) (h15 : c.get 15=base)
    (memory : B.inRam (base+2#32) 1=true) (data : ram (base+2#32)=byte) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat≠76 then 0x80001160#32 else 0x80000dd4#32) ∧
      d.get 16=BitVec.ofNat 32 byte.toNat ∧ d.get 17=76#32 ∧
      (∀ r : Reg, r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [decide_eq_true_eq,show 0x80000dc8#32+8#32+0x390#32=0x80001160#32 by decide +kernel,show 0x80000dc8#32+12#32=0x80000dd4#32 by decide +kernel] using MainMethodByteTest.contract B img c ram 0x80000dc8#32 base 2#32 76#32 0x390#32 byte .ne (decide (byte.toNat≠76)) hp h15 memory data
    (by decide) (by decide) (by decide) (by decide) re2147487176 re2147487180 re2147487184
    (MainMethodByteMath.neTest byte 76 (by decide))

theorem at2147487188 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x80000dd4#32) (h15 : c.get 15=base)
    (memory : B.inRam (base+3#32) 1=true) (data : ram (base+3#32)=byte) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat≠69 then 0x80001160#32 else 0x80000de0#32) ∧
      d.get 16=BitVec.ofNat 32 byte.toNat ∧ d.get 17=69#32 ∧
      (∀ r : Reg, r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [decide_eq_true_eq,show 0x80000dd4#32+8#32+0x384#32=0x80001160#32 by decide +kernel,show 0x80000dd4#32+12#32=0x80000de0#32 by decide +kernel] using MainMethodByteTest.contract B img c ram 0x80000dd4#32 base 3#32 69#32 0x384#32 byte .ne (decide (byte.toNat≠69)) hp h15 memory data
    (by decide) (by decide) (by decide) (by decide) re2147487188 re2147487192 re2147487196
    (MainMethodByteMath.neTest byte 69 (by decide))

theorem at2147487200 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x80000de0#32) (h15 : c.get 15=base)
    (memory : B.inRam (base+4#32) 1=true) (data : ram (base+4#32)=byte) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat≠84 then 0x80001160#32 else 0x80000dec#32) ∧
      d.get 16=BitVec.ofNat 32 byte.toNat ∧ d.get 17=84#32 ∧
      (∀ r : Reg, r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [decide_eq_true_eq,show 0x80000de0#32+8#32+0x378#32=0x80001160#32 by decide +kernel,show 0x80000de0#32+12#32=0x80000dec#32 by decide +kernel] using MainMethodByteTest.contract B img c ram 0x80000de0#32 base 4#32 84#32 0x378#32 byte .ne (decide (byte.toNat≠84)) hp h15 memory data
    (by decide) (by decide) (by decide) (by decide) re2147487200 re2147487204 re2147487208
    (MainMethodByteMath.neTest byte 84 (by decide))

theorem at2147487222 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x80000df6#32) (h15 : c.get 15=base)
    (memory : B.inRam (base+0#32) 1=true) (data : ram (base+0#32)=byte) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat=80 then 0x80001140#32 else 0x80000e02#32) ∧
      d.get 16=BitVec.ofNat 32 byte.toNat ∧ d.get 17=80#32 ∧
      (∀ r : Reg, r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [decide_eq_true_eq,show 0x80000df6#32+8#32+0x342#32=0x80001140#32 by decide +kernel,show 0x80000df6#32+12#32=0x80000e02#32 by decide +kernel] using MainMethodByteTest.contract B img c ram 0x80000df6#32 base 0#32 80#32 0x342#32 byte .eq (decide (byte.toNat=80)) hp h15 memory data
    (by decide) (by decide) (by decide) (by decide) re2147487222 re2147487226 re2147487230
    (MainMethodByteMath.eqTest byte 80 (by decide))

theorem at2147487242 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x80000e0a#32) (h15 : c.get 15=base)
    (memory : B.inRam (base+1#32) 1=true) (data : ram (base+1#32)=byte) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat≠69 then 0x80001160#32 else 0x80000e16#32) ∧
      d.get 16=BitVec.ofNat 32 byte.toNat ∧ d.get 17=69#32 ∧
      (∀ r : Reg, r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [decide_eq_true_eq,show 0x80000e0a#32+8#32+0x34e#32=0x80001160#32 by decide +kernel,show 0x80000e0a#32+12#32=0x80000e16#32 by decide +kernel] using MainMethodByteTest.contract B img c ram 0x80000e0a#32 base 1#32 69#32 0x34e#32 byte .ne (decide (byte.toNat≠69)) hp h15 memory data
    (by decide) (by decide) (by decide) (by decide) re2147487242 re2147487246 re2147487250
    (MainMethodByteMath.neTest byte 69 (by decide))

theorem at2147487258 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x80000e1a#32) (h15 : c.get 15=base)
    (memory : B.inRam (base+0#32) 1=true) (data : ram (base+0#32)=byte) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat≠80 then 0x80001160#32 else 0x80000e26#32) ∧
      d.get 16=BitVec.ofNat 32 byte.toNat ∧ d.get 17=80#32 ∧
      (∀ r : Reg, r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [decide_eq_true_eq,show 0x80000e1a#32+8#32+0x33e#32=0x80001160#32 by decide +kernel,show 0x80000e1a#32+12#32=0x80000e26#32 by decide +kernel] using MainMethodByteTest.contract B img c ram 0x80000e1a#32 base 0#32 80#32 0x33e#32 byte .ne (decide (byte.toNat≠80)) hp h15 memory data
    (by decide) (by decide) (by decide) (by decide) re2147487258 re2147487262 re2147487266
    (MainMethodByteMath.neTest byte 80 (by decide))

theorem at2147487270 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x80000e26#32) (h15 : c.get 15=base)
    (memory : B.inRam (base+1#32) 1=true) (data : ram (base+1#32)=byte) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat≠65 then 0x80001160#32 else 0x80000e32#32) ∧
      d.get 16=BitVec.ofNat 32 byte.toNat ∧ d.get 17=65#32 ∧
      (∀ r : Reg, r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [decide_eq_true_eq,show 0x80000e26#32+8#32+0x332#32=0x80001160#32 by decide +kernel,show 0x80000e26#32+12#32=0x80000e32#32 by decide +kernel] using MainMethodByteTest.contract B img c ram 0x80000e26#32 base 1#32 65#32 0x332#32 byte .ne (decide (byte.toNat≠65)) hp h15 memory data
    (by decide) (by decide) (by decide) (by decide) re2147487270 re2147487274 re2147487278
    (MainMethodByteMath.neTest byte 65 (by decide))

theorem at2147487282 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x80000e32#32) (h15 : c.get 15=base)
    (memory : B.inRam (base+2#32) 1=true) (data : ram (base+2#32)=byte) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat≠84 then 0x80001160#32 else 0x80000e3e#32) ∧
      d.get 16=BitVec.ofNat 32 byte.toNat ∧ d.get 17=84#32 ∧
      (∀ r : Reg, r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [decide_eq_true_eq,show 0x80000e32#32+8#32+0x326#32=0x80001160#32 by decide +kernel,show 0x80000e32#32+12#32=0x80000e3e#32 by decide +kernel] using MainMethodByteTest.contract B img c ram 0x80000e32#32 base 2#32 84#32 0x326#32 byte .ne (decide (byte.toNat≠84)) hp h15 memory data
    (by decide) (by decide) (by decide) (by decide) re2147487282 re2147487286 re2147487290
    (MainMethodByteMath.neTest byte 84 (by decide))

theorem at2147487294 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x80000e3e#32) (h15 : c.get 15=base)
    (memory : B.inRam (base+3#32) 1=true) (data : ram (base+3#32)=byte) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat≠67 then 0x80001160#32 else 0x80000e4a#32) ∧
      d.get 16=BitVec.ofNat 32 byte.toNat ∧ d.get 17=67#32 ∧
      (∀ r : Reg, r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [decide_eq_true_eq,show 0x80000e3e#32+8#32+0x31a#32=0x80001160#32 by decide +kernel,show 0x80000e3e#32+12#32=0x80000e4a#32 by decide +kernel] using MainMethodByteTest.contract B img c ram 0x80000e3e#32 base 3#32 67#32 0x31a#32 byte .ne (decide (byte.toNat≠67)) hp h15 memory data
    (by decide) (by decide) (by decide) (by decide) re2147487294 re2147487298 re2147487302
    (MainMethodByteMath.neTest byte 67 (by decide))

theorem at2147488030 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x8000111e#32) (h15 : c.get 15=base)
    (memory : B.inRam (base+1#32) 1=true) (data : ram (base+1#32)=byte) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat≠79 then 0x80001160#32 else 0x8000112a#32) ∧
      d.get 16=BitVec.ofNat 32 byte.toNat ∧ d.get 17=79#32 ∧
      (∀ r : Reg, r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [decide_eq_true_eq,show 0x8000111e#32+8#32+0x3a#32=0x80001160#32 by decide +kernel,show 0x8000111e#32+12#32=0x8000112a#32 by decide +kernel] using MainMethodByteTest.contract B img c ram 0x8000111e#32 base 1#32 79#32 0x3a#32 byte .ne (decide (byte.toNat≠79)) hp h15 memory data
    (by decide) (by decide) (by decide) (by decide) re2147488030 re2147488034 re2147488038
    (MainMethodByteMath.neTest byte 79 (by decide))

theorem at2147488042 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x8000112a#32) (h15 : c.get 15=base)
    (memory : B.inRam (base+2#32) 1=true) (data : ram (base+2#32)=byte) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat≠83 then 0x80001160#32 else 0x80001136#32) ∧
      d.get 16=BitVec.ofNat 32 byte.toNat ∧ d.get 17=83#32 ∧
      (∀ r : Reg, r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [decide_eq_true_eq,show 0x8000112a#32+8#32+0x2e#32=0x80001160#32 by decide +kernel,show 0x8000112a#32+12#32=0x80001136#32 by decide +kernel] using MainMethodByteTest.contract B img c ram 0x8000112a#32 base 2#32 83#32 0x2e#32 byte .ne (decide (byte.toNat≠83)) hp h15 memory data
    (by decide) (by decide) (by decide) (by decide) re2147488042 re2147488046 re2147488050
    (MainMethodByteMath.neTest byte 83 (by decide))

theorem at2147488064 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x80001140#32) (h15 : c.get 15=base)
    (memory : B.inRam (base+1#32) 1=true) (data : ram (base+1#32)=byte) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat≠85 then 0x80001160#32 else 0x8000114c#32) ∧
      d.get 16=BitVec.ofNat 32 byte.toNat ∧ d.get 17=85#32 ∧
      (∀ r : Reg, r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [decide_eq_true_eq,show 0x80001140#32+8#32+0x18#32=0x80001160#32 by decide +kernel,show 0x80001140#32+12#32=0x8000114c#32 by decide +kernel] using MainMethodByteTest.contract B img c ram 0x80001140#32 base 1#32 85#32 0x18#32 byte .ne (decide (byte.toNat≠85)) hp h15 memory data
    (by decide) (by decide) (by decide) (by decide) re2147488064 re2147488068 re2147488072
    (MainMethodByteMath.neTest byte 85 (by decide))
end E5R.Thermostat.MainMethodTests
