import Projects.thermostat.MainCompletionClose
import Projects.thermostat.MainCompletionKeep
import Projects.thermostat.ResponseHeadBodyMath
namespace E5R.Thermostat.MainCompletion
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fp : Word) (close : Bool)
    (h8 : c.get 8=fp) (h24 : c.get 24=0xfffffffe#32) (hm : Memory.Block B fp 1324) (ha : fp.toNat%4=0)
    (htag : ramRead ram (fp+1316#32) .w=0xffffffff#32)
    (hclose : ramRead ram (fp+1320#32) .w=ResponseHeadBodyMath.boolWord close) (hp : c.pc=0x80001784#32) :
    ∃ d, Quiet.Steps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧
      d.get 10=ResponseHeadBodyMath.boolWord close ∧ d.get 21=0xffffffff#32 ∧
      (∀ r : Reg, r≠10 → r≠21 → d.get r=c.get r) ∧ d.sameCsr c := by
  cases close with
  | false => exact MainCompletionKeep.contract B c ram fp h8 h24 hm ha htag hclose hp
  | true => exact MainCompletionClose.contract B c ram fp h8 h24 hm ha htag hclose hp
end E5R.Thermostat.MainCompletion
