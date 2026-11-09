import Projects.thermostat.RuntimeStored
import Projects.thermostat.RuntimeRequestInputs
import Projects.thermostat.MainCloseSpec
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeCloseReady
open E5R E5R.Thermostat HttpRequestSpec
abbrev sp := MainRequestBuild.sp
abbrev fp := MainRequestBuild.fp

structure At (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) (head : Head) (amount rawUsed served : Nat) (lowValue : Word) (close : Bool) : Prop where
  pc : c.pc=0x8000129a#32
  stable : MainTransactionStable.At c ram input s
  stored : RuntimeStored.At ram input head amount rawUsed
  serve : MainServeLayout.At ram served
  countBound : served≤100
  positive : 0<served
  countReg : c.get 18=BitVec.ofNat 32 served
  minorReg : c.get 9=BitVec.ofNat 32 head.minor
  future : c.get 23=0x80fff9f0#32
  three : c.get 26=3#32
  low : c.get 27=lowValue
  five : c.get 20=5#32
  six : c.get 21=6#32
  firstSlot : c.get 24=sp+3740#32
  secondSlot : c.get 25=sp+3784#32
  capacityReg : c.get 12=1024#32
  threshold : c.get 10=191#32
  usedWord : ramRead ram (fp+92#32) .w=BitVec.ofNat 32 rawUsed
  flag : ram (sp+3304#32)=Encoding.boolByte close
  spec : close=MainCloseSpec.mustClose head.minor served (RuntimeRequestSpans.raw input rawUsed) (RuntimeRequestInputs.entries head)

theorem forced {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat} {lowValue : Word} {close : Bool}
    (h : At c ram input s head amount rawUsed served lowValue close) (force : head.minor=0 ∨ 100≤served) : close=true := by
  rw [h.spec]
  rcases force with version|count
  · rw [version];exact MainCloseSpec.http10 _ _ _
  · exact MainCloseSpec.limit _ _ count _ _
end E5R.Thermostat.RuntimeCloseReady
