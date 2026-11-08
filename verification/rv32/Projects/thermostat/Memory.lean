import Theories.Logic

namespace E5R.Thermostat.Memory
open E5R

theorem load_byte (ram : Word → BitVec 8) (a : Word) :
    extend .b false (ramRead ram a .b) = BitVec.ofNat 32 (ram a).toNat := by
  apply BitVec.eq_of_toNat_eq
  have h := (ram a).isLt
  simp only [extend, ramRead, BitVec.toNat_and, BitVec.toNat_ofNat]
  change ((ram a).toNat % 4294967296 &&& 255) = (ram a).toNat % 4294967296
  rw [show (255 : Nat) = 2^8-1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem load_half_byte0 (ram : Word → BitVec 8) (a : Word) :
    byteOf (extend .h true (ramRead ram a .h)) 0 = ram a := by
  apply BitVec.eq_of_toNat_eq
  have h0 := (ram a).isLt
  have h1 := (ram (a+1)).isLt
  simp only [byteOf, extend, ramRead, BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  split <;> omega

theorem load_half_byte1 (ram : Word → BitVec 8) (a : Word) :
    byteOf (extend .h true (ramRead ram a .h)) 1 = ram (a+1) := by
  apply BitVec.eq_of_toNat_eq
  have h0 := (ram a).isLt
  have h1 := (ram (a+1)).isLt
  simp only [byteOf, extend, ramRead, BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  split <;> omega

theorem ofNat_width (b : BitVec 8) : BitVec.ofNat 32 b.toNat = b.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth]

theorem read_tag (b : BitVec 8) :
    alu .sltu (b.setWidth 32 + 0xfffffffc#32) 1#32 =
      if b = 4#8 then 1 else 0 := by
  have h := b.isLt
  have he : b = 4#8 ↔ b.toNat = 4 := by
    constructor
    · intro e; subst b; rfl
    · intro e; apply BitVec.eq_of_toNat_eq; exact e
  have hc : (b.setWidth 32 + 0xfffffffc#32).ult 1#32 = decide (b.toNat = 4) := by
    rw [BitVec.ult, BitVec.toNat_add, BitVec.toNat_setWidth]
    change decide (((b.toNat % 4294967296) + 4294967292) % 4294967296 < 1) = decide (b.toNat = 4)
    have hh : ((b.toNat % 4294967296) + 4294967292) % 4294967296 < 1 ↔ b.toNat = 4 := by omega
    simp only [hh]
  unfold alu
  rw [hc]
  simp only [decide_eq_true_eq, ← he]

theorem option_tag (b : BitVec 8) : BitVec.ofNat 32 b.toNat = 2#32 ↔ b = 2#8 := by
  constructor
  · intro h
    have he := congrArg BitVec.toNat h
    change b.toNat % 4294967296 = 2 at he
    apply BitVec.eq_of_toNat_eq
    change b.toNat = 2
    have := b.isLt
    omega
  · intro h; subst b; rfl

theorem read_word_write_other (ram : Word → BitVec 8) (a b v : Word)
    (h : ∀ i j : Fin 4, a + BitVec.ofNat 32 i.val ≠ b + BitVec.ofNat 32 j.val) :
    ramRead (ramWrite ram b v .w) a .w = ramRead ram a .w := by
  apply ramRead_w_congr
  intro k hk
  apply ramWrite_w_other
  intro j hj
  exact h ⟨k,hk⟩ ⟨j,hj⟩

theorem word_disjoint (p : Word) (a b : Nat) (ha : a < 128) (hb : b < 128)
    (h4a : a % 4 = 0) (h4b : b % 4 = 0) (hne : a ≠ b) :
    ∀ i j : Fin 4, p + BitVec.ofNat 32 a + BitVec.ofNat 32 i.val ≠
      p + BitVec.ofNat 32 b + BitVec.ofNat 32 j.val := by
  intro i j he
  simp only [BitVec.add_assoc, BitVec.add_right_inj] at he
  have hh := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hh
  have hi := i.isLt
  have hj := j.isLt
  omega

/-- A non-wrapping caller-owned object wholly inside modeled RAM. -/
def Block (B : Board) (p : Word) (n : Nat) : Prop :=
  B.ramBase ≤ p.toNat ∧ p.toNat + n ≤ B.ramBase + B.ramSize ∧ p.toNat + n ≤ 4294967296

theorem block_access {B : Board} {p : Word} {n off width : Nat}
    (h : Block B p n) (hw : 0 < width) (ho : off + width ≤ n) :
    B.inRam (p + BitVec.ofNat 32 off) width = true := by
  apply (Board.inRam_iff (p + BitVec.ofNat 32 off) width).mpr
  rw [BitVec.toNat_add,BitVec.toNat_ofNat]
  have hp := p.isLt
  obtain ⟨hb,he,hn⟩ := h
  constructor <;> omega

theorem half_aligned (p : Word) (k : Nat) (ha : p.toNat % 2 = 0) :
    (p + BitVec.ofNat 32 (2*k)).toNat % 2 = 0 := by
  rw [BitVec.toNat_add,BitVec.toNat_ofNat]
  have hp := p.isLt
  omega

theorem sub_block {B : Board} {p : Word} {n off m : Nat}
    (h : Block B p n) (hm : 0 < m) (ho : off+m ≤ n) : Block B (p+BitVec.ofNat 32 off) m := by
  unfold Block
  rw [BitVec.toNat_add,BitVec.toNat_ofNat]
  have hp := p.isLt
  obtain ⟨hb,he,hn⟩ := h
  exact ⟨by omega,by omega,by omega⟩

theorem half_block {B : Board} {p : Word} (h : Block B p 10) (ha : p.toNat % 2 = 0) :
    ∀ k : Fin 5, (p+BitVec.ofNat 32 (2*k.val)).toNat % 2 = 0 ∧
      B.inRam (p+BitVec.ofNat 32 (2*k.val)) 2 = true := by
  intro k
  have hk := k.isLt
  exact ⟨half_aligned p k.val ha,
    block_access (B := B) (p := p) (n := 10) (off := 2*k.val) (width := 2) h (by decide) (by omega)⟩

theorem word_aligned (p : Word) (k : Nat) (ha : p.toNat % 4 = 0) :
    (p+BitVec.ofNat 32 (4*k)).toNat % 4 = 0 := by
  rw [BitVec.toNat_add,BitVec.toNat_ofNat]
  have hp := p.isLt
  omega

end E5R.Thermostat.Memory
