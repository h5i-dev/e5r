import Projects.thermostat.HeadVersionSpec
import Projects.thermostat.HeadVersionTail
import Projects.thermostat.HeadLineScanSpec
namespace E5R.Thermostat.HeadVersionInputSpec
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

theorem address (buf : Word) (te k : Nat) (ht : 0<te) :
    buf+BitVec.ofNat 32 (te-1)+BitVec.ofNat 32 (k+1)=buf+BitVec.ofNat 32 (te+k) := by
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  congr 2
  omega

theorem prefix_iff (ram : Word → BitVec 8) (buf : Word) (te : Nat) (ht : 0<te) :
    HeadVersionSpec.Prefix (bytes ram buf) (te+1) ↔
      ram (buf+BitVec.ofNat 32 (te-1)+2#32)=72#8 ∧ HeadVersionTail.Good ram (buf+BitVec.ofNat 32 (te-1)) := by
  have byte_eq (b v : BitVec 8) : b.toNat=v.toNat ↔ b=v := BitVec.toNat_inj
  unfold HeadVersionSpec.Prefix HeadVersionTail.Good
  rw [address buf te 1 ht,address buf te 2 ht,address buf te 3 ht,address buf te 4 ht,address buf te 5 ht]
  have b72 (a : BitVec 8) : a.toNat=72 ↔ a=72#8 := byte_eq a 72#8
  have b84 (a : BitVec 8) : a.toNat=84 ↔ a=84#8 := byte_eq a 84#8
  have b80 (a : BitVec 8) : a.toNat=80 ↔ a=80#8 := byte_eq a 80#8
  have b47 (a : BitVec 8) : a.toNat=47 ↔ a=47#8 := byte_eq a 47#8
  simp only [bytes,Nat.add_assoc,Nat.reduceAdd,b72,b84,b80,b47]

theorem version (ram : Word → BitVec 8) (buf : Word) (te : Nat) (ht : 0<te) :
    HttpRequestSpec.version (bytes ram buf) (te+1) (te+9)=
      if ram (buf+BitVec.ofNat 32 (te-1)+2#32)=72#8 ∧ HeadVersionTail.Good ram (buf+BitVec.ofNat 32 (te-1))
      then versionDigits (bytes ram buf (te+6)) (bytes ram buf (te+7)) (bytes ram buf (te+8)) else 3 := by
  have width : te+9=(te+1)+8 := by omega
  rw [width,HeadVersionSpec.version]
  simp only [prefix_iff ram buf te ht,Nat.add_assoc,Nat.reduceAdd]
end E5R.Thermostat.HeadVersionInputSpec
