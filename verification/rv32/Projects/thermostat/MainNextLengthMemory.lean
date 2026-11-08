import Projects.thermostat.MainNextLengthPrefix
import Projects.thermostat.MainNextLengthFinish
namespace E5R.Thermostat.MainNextLengthMemory
open E5R E5R.Thermostat HttpRequestSpec

def memory (ram : Word → BitVec 8) (sp : Word) (head : Head) (amount : Nat) :=
  MainNextLengthFinish.memory (MainNextLengthPrefix.memory ram sp head) sp head (BitVec.ofNat 32 (head.len+amount))

theorem frame (ram : Word → BitVec 8) (sp : Word) (head : Head) (amount off size : Nat)
    (lo : 44≤off) (hi : off+size≤4896) : ViewFrame.Region ram (memory ram sp head amount) (sp+BitVec.ofNat 32 off) size := by
  apply HeadRegionFrame.trans (MainNextLengthStoreMemory.region ram sp _ _ _ _ off size (by omega) (by omega))
  apply HeadRegionFrame.trans (MainNextCopy264.frame (MainNextLengthPrefix.stored ram sp head) sp 3352 off size (by omega) (Or.inl (by omega)))
  exact MainNextLengthTailMemory.region (MainNextLengthPrefix.memory ram sp head) sp (BitVec.ofNat 32 head.len) (BitVec.ofNat 32 (head.len+amount)) (BitVec.ofNat 32 head.minor) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 0) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 1) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 2) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 3) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 4) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 5) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 6) off size (by omega) (Or.inr lo) (Or.inl hi)

theorem kept_word (ram : Word → BitVec 8) (sp : Word) (head : Head) (amount off : Nat) (bound : off+4≤40) :
    ramRead (memory ram sp head amount) (sp+BitVec.ofNat 32 off) .w=
      ramRead (MainNextLengthPrefix.stored ram sp head) (sp+BitVec.ofNat 32 off) .w := by
  have copy := MainNextCopy264.frame (MainNextLengthPrefix.stored ram sp head) sp 3352 off 4 (by omega) (Or.inl (by omega))
  have tail := MainNextLengthTailMemory.region (MainNextLengthPrefix.memory ram sp head) sp (BitVec.ofNat 32 head.len) (BitVec.ofNat 32 (head.len+amount)) (BitVec.ofNat 32 head.minor) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 0) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 1) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 2) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 3) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 4) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 5) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 6) off 4 (by omega) (Or.inl bound) (Or.inl (by omega))
  simpa only [memory,MainNextLengthFinish.memory,BitVec.add_zero] using ViewFrame.word (HeadRegionFrame.trans copy tail) 0 (by decide)

theorem methodStart (ram : Word → BitVec 8) (sp : Word) (head : Head) (amount : Nat) :
    ramRead (memory ram sp head amount) (sp+28#32) .w=BitVec.ofNat 32 head.method.1 :=
  (kept_word ram sp head amount 28 (by decide)).trans (MainNextLengthStoreMemory.methodStart ram sp _ _ _ _)

theorem methodEnd (ram : Word → BitVec 8) (sp : Word) (head : Head) (amount : Nat) :
    ramRead (memory ram sp head amount) (sp+24#32) .w=BitVec.ofNat 32 head.method.2 :=
  (kept_word ram sp head amount 24 (by decide)).trans (MainNextLengthStoreMemory.methodEnd ram sp _ _ _ _)

theorem targetStart (ram : Word → BitVec 8) (sp : Word) (head : Head) (amount : Nat) :
    ramRead (memory ram sp head amount) (sp+36#32) .w=BitVec.ofNat 32 head.target.1 :=
  (kept_word ram sp head amount 36 (by decide)).trans (MainNextLengthStoreMemory.targetStart ram sp _ _ _ _)

theorem targetEnd (ram : Word → BitVec 8) (sp : Word) (head : Head) (amount : Nat) :
    ramRead (memory ram sp head amount) (sp+32#32) .w=BitVec.ofNat 32 head.target.2 :=
  (kept_word ram sp head amount 32 (by decide)).trans (MainNextLengthStoreMemory.targetEnd ram sp _ _ _ _)

theorem minor (ram : Word → BitVec 8) (sp : Word) (head : Head) (amount : Nat) :
    ramRead (memory ram sp head amount) (sp+40#32) .w=BitVec.ofNat 32 head.minor := MainNextLengthTailMemory.minor_word (MainNextLengthPrefix.memory ram sp head) sp (BitVec.ofNat 32 head.len) (BitVec.ofNat 32 (head.len+amount)) (BitVec.ofNat 32 head.minor) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 0) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 1) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 2) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 3) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 4) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 5) (MainNextLengthFinish.pad (MainNextLengthPrefix.memory ram sp head) sp 6)
end E5R.Thermostat.MainNextLengthMemory
