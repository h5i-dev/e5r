import Projects.thermostat.Bytes
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ReadBytes
open E5R E5R.Thermostat

/-- Exactly the two existing deterministic byte-load cases. ROM is usable only
    when RAM does not shadow the address; device values are never summarized. -/
inductive Byte (B : Board) (img : List Segment) (ram : Word → BitVec 8) (a : Word) (v : BitVec 8) : Prop
  | ram (inside : B.inRam a 1 = true) (value : ram a = v) : Byte B img ram a v
  | rom (outside : B.inRam a 1 = false)
      (value : romRead? img a.toNat 1 false = some (BitVec.ofNat 32 v.toNat)) : Byte B img ram a v

theorem load {B img ram a v} (h : Byte B img ram a v) (o : Oracle) (k : Word → Eff) (i : Nat) (evs : List Event) :
    interp B img o (.load .b a false k) ram i evs = interp B img o (k (BitVec.ofNat 32 v.toNat)) ram i evs := by
  cases h with
  | ram hi hv =>
    rw [interp_load_ram o (by change a.toNat%1 = 0;omega) hi]
    change interp B img o (k (BitVec.ofNat 32 (ram a).toNat)) ram i evs = _
    rw [hv]
  | rom ho hv => exact interp_load_rom o (by change a.toNat%1 = 0;omega) ho rfl hv

theorem extend_byte (v : BitVec 8) : extend .b false (BitVec.ofNat 32 v.toNat) = v.setWidth 32 := by
  rw [←Memory.ofNat_width]
  apply BitVec.eq_of_toNat_eq
  have hv := v.isLt
  simp only [extend,BitVec.toNat_and,BitVec.toNat_ofNat]
  change (v.toNat%4294967296 &&& 255) = v.toNat%4294967296
  rw [show (255 : Nat) = 2^8-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega

structure Span (B : Board) (img : List Segment) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8)) : Prop where
  length : xs.length < 2^32
  nowrap : p.toNat+xs.length ≤ 2^32
  bytes : ∀ i : Fin xs.length, Byte B img ram (p+BitVec.ofNat 32 i.val) xs[i]

theorem of_ram {B img ram p xs} (h : Bytes.Span B ram p xs) : Span B img ram p xs :=
  ⟨h.length,h.nowrap,fun i => .ram (h.memory i) (h.bytes i)⟩

theorem head {B img ram p b bs} (h : Span B img ram p (b::bs)) : Byte B img ram p b := by
  have hb := h.bytes ⟨0,by simp⟩
  change Byte B img ram (p+0#32) b at hb
  simpa only [BitVec.add_zero] using hb

theorem tail {B img ram p b bs} (h : Span B img ram p (b::bs)) : Span B img ram (p+1#32) bs := by
  have hl : bs.length+1 < 2^32 := by simpa using h.length
  have hn : p.toNat+(bs.length+1) ≤ 2^32 := by simpa using h.nowrap
  refine ⟨by omega,?_,?_⟩
  · by_cases hz : bs.length = 0
    · have hp := (p+1#32).isLt;omega
    · have hp : (p+1#32).toNat = p.toNat+1 := by
        rw [BitVec.toNat_add]
        change (p.toNat+1)%4294967296 = p.toNat+1
        rw [Nat.mod_eq_of_lt (by omega)]
      rw [hp];omega
  · intro i
    have hi := i.isLt
    have hb := h.bytes ⟨i.val+1,by simpa using Nat.succ_lt_succ hi⟩
    have ha : (p+1#32)+BitVec.ofNat 32 i.val = p+BitVec.ofNat 32 (i.val+1) := by
      rw [BitVec.add_assoc,←BitVec.ofNat_add,show 1+i.val = i.val+1 by omega]
    rw [ha];exact hb

/-- Changing RAM preserves ROM views and any explicitly framed RAM byte. -/
theorem Byte.frame {B img ram ram' a v} (h : Byte B img ram a v) (hf : ram' a = ram a) : Byte B img ram' a v := by
  cases h with
  | ram hi hv => exact .ram hi (hf.trans hv)
  | rom ho hv => exact .rom ho hv
end E5R.Thermostat.ReadBytes
