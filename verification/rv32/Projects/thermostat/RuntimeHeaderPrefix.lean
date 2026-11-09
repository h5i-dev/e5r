import Projects.thermostat.MainMethodBytes
import Projects.thermostat.MainQuerySpec
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeHeaderPrefix
open E5R E5R.Thermostat

/-- Body compaction may alter later bytes; method and URI bytes are framed by
    the exact original head prefix, independently of the decoder's RAM layout. -/
theorem method {raw original : List (BitVec 8)} {cut len : Nat}
    (same : raw.take cut=original) (inside : len≤cut) :
    MainMethodBytes.token raw len=MainMethodBytes.token original len := by
  rw [←same,MainMethodBytes.token,MainMethodBytes.token,List.take_take,Nat.min_eq_left inside]

theorem bytes {raw original : List (BitVec 8)} {cut k : Nat}
    (same : raw.take cut=original) (inside : k<cut) :
    MainQuerySpec.bytes raw k=MainQuerySpec.bytes original k := by
  rw [←same]
  simp only [MainQuerySpec.bytes,List.getElem?_take,inside,ite_true]

theorem path {raw original : List (BitVec 8)} {cut first last : Nat}
    (same : raw.take cut=original) (inside : first≤last ∧ last≤cut) :
    MainQuerySpec.path raw first last=MainQuerySpec.path original first last := by
  have scanEq : MainQuerySpec.position (MainQuerySpec.bytes raw) first last=MainQuerySpec.position (MainQuerySpec.bytes original) first last :=
    HeadLineScanSpec.scan_congr _ _ _ _ _ (fun k hk => bytes same (by omega))
  have sizeEq : MainQuerySpec.pathLength (MainQuerySpec.bytes raw) first last=MainQuerySpec.pathLength (MainQuerySpec.bytes original) first last := by
    unfold MainQuerySpec.pathLength;rw [scanEq]
  have bound := (MainQuerySpec.bounds (MainQuerySpec.bytes raw) first last inside.1).2
  have length : MainQuerySpec.pathLength (MainQuerySpec.bytes raw) first last≤cut-first := by
    unfold MainQuerySpec.pathLength;omega
  unfold MainQuerySpec.path
  rw [←sizeEq,←same,List.drop_take,List.take_take,Nat.min_eq_left length]
end E5R.Thermostat.RuntimeHeaderPrefix
