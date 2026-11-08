import Projects.thermostat.DecimalMath
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.TrimMath
open E5R

/-- Rust trim_ascii's byte set. Vertical tab is deliberately excluded. -/
def white (b : BitVec 8) : Bool := decide (b.toNat = 9 ∨ b.toNat = 10 ∨ b.toNat = 12 ∨ b.toNat = 13 ∨ b.toNat = 32)

def left (xs : List (BitVec 8)) := xs.dropWhile white
def trim (xs : List (BitVec 8)) := (left xs).reverse.dropWhile white |>.reverse

theorem range (b : BitVec 8) :
    taken .ltu 23#32 (BitVec.ofNat 32 b.toNat+0xfffffff7#32) = decide (b.toNat < 9 ∨ 32 < b.toNat) := by
  have hb := b.isLt
  simp only [taken]
  rw [BitVec.ult,BitVec.toNat_add,BitVec.toNat_ofNat]
  change decide (23 < (b.toNat%4294967296+4294967287)%4294967296) = _
  have hh : 23 < (b.toNat%4294967296+4294967287)%4294967296 ↔ b.toNat < 9 ∨ 32 < b.toNat := by omega
  simp only [hh]

@[irreducible] def shifted (b : BitVec 8) : Word := 0x80001b#32 >>> ((BitVec.ofNat 32 b.toNat+0xfffffff7#32).toNat%32)

theorem mask : ∀ b : BitVec 8, 9 ≤ b.toNat ∧ b.toNat ≤ 32 →
    (shifted b &&& 1#32) =
      (if white b then 1#32 else 0#32) := by
  unfold shifted
  decide +kernel


theorem left_length (xs : List (BitVec 8)) : (left xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [left]
  | cons b bs ih =>
    cases hw : white b <;> simp [left,List.dropWhile_cons,hw] at * <;> omega


/-- The backwards scan starts at the last byte after a leading trim. This
    equality is modular and also covers an end pointer wrapping to zero. -/
theorem end_pred (p : Word) (n m : Nat) (hm : 0 < m) (hle : m ≤ n) :
    (p+BitVec.ofNat 32 n)+0xffffffff#32 =
      (p+BitVec.ofNat 32 (n-m))+BitVec.ofNat 32 (m-1) := by
  have hn : n = (n-m)+(m-1)+1 := by omega
  have he : BitVec.ofNat 32 n = (BitVec.ofNat 32 (n-m)+BitVec.ofNat 32 (m-1))+1#32 := by
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 32) hn
  rw [he,←BitVec.add_assoc p _ 1#32,BitVec.add_assoc (p+_) 1#32 0xffffffff#32,
    show 1#32+0xffffffff#32 = 0#32 by decide +kernel,BitVec.add_zero,←BitVec.add_assoc]

theorem vt_retained : trim [11#8,49#8,11#8] = [11#8,49#8,11#8] := by decide +kernel
theorem ff_trimmed : trim [12#8,49#8,12#8] = [49#8] := by decide +kernel
theorem only_whitespace : trim [9#8,10#8,12#8,13#8,32#8] = [] := by decide +kernel
end E5R.Thermostat.TrimMath
