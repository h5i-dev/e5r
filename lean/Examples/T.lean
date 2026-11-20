import Examples.Sum2
import NoCompiler.Auto
open NoCompiler NoCompiler.Auto Examples.Sum.Image
set_option maxHeartbeats 400000 in
example (s : State) (a : Word) (xs : List Word) (he : Entry sum2_dom sum2_entry s) (ha0 : s.reg Reg.a0 = a) (ha1 : s.reg Reg.a1 = BitVec.ofNat 64 xs.length)
    (hd1 : ∀ x, (arrRegion a xs).mem x → ¬ (Spec.stackRegion s 32).mem x) (harr1 : arr64 s.mem a xs) :
    arr64   (writeLE     (writeLE       (writeLE (writeLE s.mem (s.reg 2 + 18446744073709551608#64) (BitVec.toNat (s.reg 1)) 8)         (s.reg 2 + 18446744073709551600#64) (BitVec.toNat (s.reg 8)) 8)       (s.reg 2 + 18446744073709551592#64) (BitVec.toNat (s.reg 9)) 8)     (s.reg 2 + 18446744073709551584#64) (BitVec.toNat (s.reg 18)) 8)   a xs := by
  have := (show (State.reg s 2).toNat % 16 = 0 from (he).sp)
  nocompiler_vnorm [arr64_writeLE_of_outside hd1, ret_mask (he).retAligned, eq_true (he).retAligned, eq_true (aligned_two_of_four (he).retAligned), harr1, arr64.read harr1, ha0, ha1]
