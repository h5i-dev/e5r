/-
Universal compatibility facts for the admitted unsigned byte loads and
16-bit register operations. These use kernel-checked bit-vector lemmas.
NVIDIA PTX ISA 8.8 §9.4.1 specifies the relaxed ld/st/cvt operand widths;
§9.7.9.21 specifies integer chopping and source-dependent extension.
-/
import Ptx.Logic.Phases

namespace Ptx

/-- All supported register normalizations are idempotent. -/
theorem fit_idempotent (t : Ty) (v : Val) : fit t (fit t v) = fit t v := by
  cases t <;> simp [fit, Ty.width, lo32, ext32]

/-- A narrow unsigned conversion ignores all bits above the source width. -/
theorem convert_u16_u32_fit (v : Val) :
    convert .u16 .u32 v = fit .u16 (fit .u32 v) := by
  simp [convert, fit, Ty.width, lo32, ext32]

/-- A zero-extended 16-bit value has the same representation at 32/64 bits. -/
theorem convert_u32_u16_fit (v : Val) :
    convert .u32 .u16 (fit .u16 v) = fit .u16 v := by
  simp [convert, fit, Ty.width, Ty.signed]

theorem convert_u64_u16_fit (v : Val) :
    convert .u64 .u16 (fit .u16 v) = fit .u16 v := by
  simp [convert, fit, Ty.width, Ty.signed]

/-- Sign extension preserves the original low bits, including the sign bit. -/
theorem signExtend16_low (v : BitVec 16) :
    (v.signExtend 64).setWidth 16 = v := by
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getElem_signExtend,
    hi, show i < 64 by omega]

/-- A signed widening followed by truncation recovers exactly the low16 bits. -/
theorem convert_s16_roundtrip (v : Val) :
    convert .u16 .s64 (convert .u64 .s16 v) = fit .u16 v := by
  simp only [convert, Ty.width, Ty.signed, ↓reduceIte, fit]
  rw [signExtend16_low]

/-- Signed widening to32 and64 agrees on all32 observable result bits. -/
theorem convert_s16_32_64 (v : Val) :
    convert .u32 .s16 v = fit .u32 (convert .u64 .s16 v) := by
  simp only [convert, Ty.width, Ty.signed, ↓reduceIte, fit, lo32, ext32]
  congr 1
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getElem_signExtend,
    show i < 64 by omega]

/-- The existing frame theorem covers the newly admitted byte stores. -/
theorem wr_byte_frame {m : Mem} {a x : Addr} {v : Val} (h : x ≠ a) :
    wr m a .b1 v x = m x := by
  apply wr_outside
  unfold covers Size.bytes
  intro hx
  have he : x - a = 0 := by bv_omega
  have : x = a := by bv_omega
  exact h this

/-- Two-byte stores preserve every byte outside their footprint. -/
theorem wr_half_frame {m : Mem} {a x : Addr} {v : Val}
    (h : ¬ covers a 2 x) : wr m a .b2 v x = m x := wr_outside h

/-- Byte/half loads are zero-extended, even after an arbitrary store value. -/
theorem rd_wr_byte (m : Mem) (a : Addr) (v : Val) :
    rd (wr m a .b1 v) a .b1 = fit .u8 v := rd_wr_same m a .b1 v

theorem rd_wr_half (m : Mem) (a : Addr) (v : Val) :
    rd (wr m a .b2 v) a .b2 = fit .u16 v := rd_wr_same m a .b2 v

end Ptx
