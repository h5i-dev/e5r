import Projects.thermostat.HeadResultView
namespace E5R.Thermostat.HeadLineReady
open E5R E5R.Thermostat

/-- Concrete cutpoint/layout needed by the actual header-field initializer.
    This is not a completed HeadR result. -/
structure At (c : Core) (ram : Word → BitVec 8) (sp : Word) (m te j minor length cap : Nat) : Prop where
  pc : c.pc=0x80002f0e#32
  stack : c.get 2=sp
  firstLine : c.get 9=BitVec.ofNat 32 j
  version : c.get 8=BitVec.ofNat 32 minor
  inverse : c.get 18=BitVec.ofNat 32 (1-minor)
  limits : c.get 20=sp+3664#32
  methodEnd : ramRead ram (sp+20#32) .w=BitVec.ofNat 32 m
  targetStart : ramRead ram (sp+24#32) .w=BitVec.ofNat 32 (m+1)
  targetEnd : ramRead ram (sp+28#32) .w=BitVec.ofNat 32 te
  tcharMask : ramRead ram (sp+32#32) .w=9409#32
  maxHead : ramRead ram (sp+36#32) .w=1024#32
  cap : ramRead ram (sp+40#32) .w=BitVec.ofNat 32 cap
  buffer : ramRead ram (sp+44#32) .w=sp+516#32
  lengthWord : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length
  output : ramRead ram (sp+52#32) .w=sp+4904#32
end E5R.Thermostat.HeadLineReady
