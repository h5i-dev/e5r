/- Instruction-level prerequisites appearing unchanged in the frozen FP4 entry.
No whole-kernel execution or SASS correctness is claimed here. -/
import Ptx.Semantics.Instruction

namespace Ptx

/-- The absent modifier is retained in syntax, while the specified instruction
rounding is RN. This does not verify ptxas contraction permissions. -/
theorem default_bin_rn (K : Kernel) (c : Ctx) (s : TState) (op : FBin)
    (ftz sat : Bool) (t : Ty) (d : String) (a b : Operand) :
    exec K c s (.fbinDefault op ftz sat t d a b) =
      exec K c s (.fbin op .rn ftz sat t d a b) := by
  cases op <;> rfl

/-- Integer-to-float conversion is specified even if the two arbitrary
contexts/oracles have different PCs. All u16 values are finite. -/
theorem cvt_u16_f32_oracle_independent (c₀ c₁ : Ctx) (s₀ s₁ : TState) (a : Val) :
    cvtFloat c₀ s₀ .f32 .u16 (.f .rn) false false a =
      cvtFloat c₁ s₁ .f32 .u16 (.f .rn) false false a := rfl

theorem cvt_s16_f32_oracle_independent (c₀ c₁ : Ctx) (s₀ s₁ : TState) (a : Val) :
    cvtFloat c₀ s₀ .f32 .s16 (.f .rn) false false a =
      cvtFloat c₁ s₁ .f32 .s16 (.f .rn) false false a := rfl

set_option maxRecDepth 100000 in
/-- The exact clz/sub sequence used for all eight public block sizes obtains
log2(blocksize/2), including the source's 32-bit subtraction semantics. -/
theorem public_block_shift : ∀ i : Fin 8,
    (31#32 - (BitVec.ofNat 32 (16 * 2^i.val)).clz).toNat = 4 + i.val := by
  decide +kernel

/-- The actual special-register expression for the two warps of a 64-thread
one-dimensional CTA agrees with the hardware lane numbering. -/
theorem laneid_oneD (c : Ctx) (hy : c.tid.y = 0) (hz : c.tid.z = 0) :
    (c.sreg .laneid).toNat = c.tid.x.toNat % 32 := by
  simp [Ctx.sreg, hy, hz, BitVec.toNat_and]
  change c.tid.x.toNat &&& (2^5 - 1) = c.tid.x.toNat % 2^5
  exact Nat.and_two_pow_sub_one_eq_mod _ _

#print axioms default_bin_rn
#print axioms cvt_u16_f32_oracle_independent
#print axioms public_block_shift
#print axioms laneid_oneD
end Ptx
