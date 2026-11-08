import Projects.thermostat.MainRamHalves
import Projects.thermostat.HeadCompletedView
namespace E5R.Thermostat.MainNextLengthWords
open E5R E5R.Thermostat HttpRequestSpec

structure At (ram : Word → BitVec 8) (sp : Word) (amount : Nat) : Prop where
  tag : ramRead ram (sp+3320#32) .w=1#32
  padding : ramRead ram (sp+3324#32) .w=0#32
  low : extend .h false (ramRead ram (sp+3328#32) .h)=BitVec.ofNat 32 amount
  half0 : extend .h false (ramRead ram (sp+3330#32) .h)=0#32
  half1 : extend .h false (ramRead ram (sp+3332#32) .h)=0#32
  half2 : extend .h true (ramRead ram (sp+3334#32) .h)=0#32

/-- The actual mixed word/halfword loads used by fixed-length Next setup
    derive from the successful Head object and the parser's bounded length. -/
theorem contract (ram : Word → BitVec 8) (sp : Word) (head : Head) (amount : Nat)
    (view : HeadCompletedView.At ram (sp+3320#32) head) (kind : head.framing=.length amount) (bound : amount≤1024) : At ram sp amount := by
  have payload := view.framing amount kind
  have low : ramRead ram (sp+3328#32) .w=BitVec.ofNat 32 amount := by
    simpa only [BitVec.add_assoc,show 3320#32+8#32=3328#32 by decide +kernel] using payload.1
  have high : ramRead ram (sp+3332#32) .w=0#32 := by
    have div : amount/4294967296=0 := by omega
    simpa only [div,BitVec.add_assoc,show 3320#32+12#32=3332#32 by decide +kernel] using payload.2
  have small : (BitVec.ofNat 32 amount).toNat<65536 := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)];omega
  refine ⟨by simpa only [kind,HeadCompletedView.framingTag] using view.tag,?_,MainRamHalves.low ram _ _ low small,?_,MainRamHalves.zero_low ram _ high false,?_⟩
  · simpa only [BitVec.add_assoc,show 3320#32+4#32=3324#32 by decide +kernel] using view.padding
  · simpa only [BitVec.add_assoc,show 3328#32+2#32=3330#32 by decide +kernel] using MainRamHalves.high ram _ _ low small false
  · simpa only [BitVec.add_assoc,show 3332#32+2#32=3334#32 by decide +kernel] using MainRamHalves.high ram _ 0#32 high (by decide +kernel) true
end E5R.Thermostat.MainNextLengthWords
