import Fp.Theorems.PackUnpackRoundTrip
import Crosscheck

namespace Crosscheck
/-- A useful staged rewrite for chained IEEE multiplications, with canonicality
    discharged for actual packed inputs instead of assuming Canonical_all. -/
theorem mul_intermediate_roundtrip (he : 1 < e) (hs : 0 < s)
    (x y : PackedFloat e s) :
    (EUnpackedFloat.mul .RNE x.unpack y.unpack).pack.unpack =
      EUnpackedFloat.mul .RNE x.unpack y.unpack := by
  apply EUnpackedFloat.mul_pack_unpack he hs
  · exact EUnpackedFloat.Canonical_unpack he hs x
  · exact EUnpackedFloat.Canonical_unpack he hs y

/-- Rewrite a packed multiply chain to remove one intermediate unpack/pack. -/
theorem mul_chain (he : 1 < e) (hs : 0 < s) (x y z : PackedFloat e s) :
    PackedFloat.mul .RNE (PackedFloat.mul .RNE x y) z =
      (EUnpackedFloat.mul .RNE (EUnpackedFloat.mul .RNE x.unpack y.unpack)
        z.unpack).pack := by
  unfold PackedFloat.mul
  rw [mul_intermediate_roundtrip he hs]
end Crosscheck
