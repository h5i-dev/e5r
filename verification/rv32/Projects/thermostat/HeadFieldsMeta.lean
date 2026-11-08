import Projects.thermostat.HeadNameMemory
namespace E5R.Thermostat.HeadFieldsMeta
open E5R E5R.Thermostat

/-- Stable metadata populated by the real request-line/header setup, including
    the three scratch words that the value/name loops actually load. -/
structure At (ram : Word → BitVec 8) (sp : Word) (length cap : Nat) : Prop where
  body : ramRead ram (sp+8#32) .w=1024#32
  before : ramRead ram (sp+12#32) .w=BitVec.ofNat 32 length+0xffffffff#32
  next : ramRead ram (sp+16#32) .w=(sp+516#32)+1#32
  mask : ramRead ram (sp+32#32) .w=9409#32
  maximum : ramRead ram (sp+36#32) .w=1024#32
  limit : ramRead ram (sp+40#32) .w=BitVec.ofNat 32 cap
  buffer : ramRead ram (sp+44#32) .w=sp+516#32
  raw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length
  output : ramRead ram (sp+52#32) .w=sp+4904#32

theorem preserve {ram after : Word → BitVec 8} {sp : Word} {length cap k : Nat}
    (h : At ram sp length cap) (effect : after=ram ∨ after=ramWrite ram (sp+4#32) (BitVec.ofNat 32 k) .w) :
    At after sp length cap := by
  exact ⟨(HeadNameMemory.word_frame ram after sp k 8 effect (by decide) (by decide)).trans h.body,
    (HeadNameMemory.word_frame ram after sp k 12 effect (by decide) (by decide)).trans h.before,
    (HeadNameMemory.word_frame ram after sp k 16 effect (by decide) (by decide)).trans h.next,
    (HeadNameMemory.word_frame ram after sp k 32 effect (by decide) (by decide)).trans h.mask,
    (HeadNameMemory.word_frame ram after sp k 36 effect (by decide) (by decide)).trans h.maximum,
    (HeadNameMemory.word_frame ram after sp k 40 effect (by decide) (by decide)).trans h.limit,
    (HeadNameMemory.word_frame ram after sp k 44 effect (by decide) (by decide)).trans h.buffer,
    (HeadNameMemory.word_frame ram after sp k 48 effect (by decide) (by decide)).trans h.raw,
    (HeadNameMemory.word_frame ram after sp k 52 effect (by decide) (by decide)).trans h.output⟩
end E5R.Thermostat.HeadFieldsMeta
