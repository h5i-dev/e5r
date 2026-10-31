/-
  memmove, backward direction, n ≥ 16, source and destination NOT
  congruent mod 4: the whole path composed (pinned RMK image), and the
  memmove contract for every case.

  Original e5r code, Apache-2.0.

  Besides the destination this path writes only its stack temporaries
  sp+0x1a..sp+0x23 of the callee frame, i.e. [sp - 22, sp - 12) of the
  caller's sp, below the three save slots.
-/
import Projects.rmk.MemmoveBwdMisEnd
import Projects.rmk.MemmoveBwd

set_option maxRecDepth 100000

namespace E5R.Rmk
open E5R E5R.Rmk.MemmoveFetch E5R.Rmk.Memmove

/-! ## Copies ignore bytes they neither read nor write -/

theorem bwd_frame (Z : Word → Prop) : ∀ (k : Nat) (R1 R2 : Word → BitVec 8) (p q : Word),
    (∀ y, ¬ Z y → R1 y = R2 y) → (∀ i < k, ¬ Z (p - BitVec.ofNat 32 i)) →
    (∀ i < k, ¬ Z (q + 0xffffffff#32 - BitVec.ofNat 32 i)) →
    ∀ y, ¬ Z y → bwd R1 p q k y = bwd R2 p q k y
  | 0, R1, R2, p, q, h, _, _, y, hy => h y hy
  | k+1, R1, R2, p, q, h, hs, hd, y, hy => by
    simp only [bwd]
    apply bwd_frame Z k _ _ (p + 0xffffffff#32) (q + 0xffffffff#32)
    · intro y' hy'
      simp only [ramPut]
      split
      · exact h p (by simpa using hs 0 (by omega))
      · exact h y' hy'
    · intro i hi
      rw [show p + 0xffffffff#32 - BitVec.ofNat 32 i = p - BitVec.ofNat 32 (i + 1) by bv_omega]
      exact hs (i + 1) (by omega)
    · intro i hi
      rw [show q + 0xffffffff#32 + 0xffffffff#32 - BitVec.ofNat 32 i = q + 0xffffffff#32 - BitVec.ofNat 32 (i + 1) by
        bv_omega]
      exact hd (i + 1) (by omega)
    · exact hy

/-- One backward word store is a backward copy of its four bytes. -/
theorem word_bwd (R : Word → BitVec 8) (p q : Word) (h1 : 1 ≤ p.toNat) (h2 : p.toNat + 4 < 2 ^ 32)
    (h3 : p.toNat + 4 ≤ q.toNat) :
    ramWrite R (q + 0xfffffffc#32) (ramRead R p .w) .w = bwd R (p + 3) q 4 := by
  funext x
  rw [word_spec _ _ _ _ (by bv_omega), bwd_spec 4 R (p + 3) q x (by bv_omega) (by bv_omega)]
  split <;> split <;> first | (exfalso; bv_omega) | (refine congrArg R ?_; bv_omega) | rfl

theorem ramWrite_off (Z : Word → Prop) (R R' : Word → BitVec 8) (a v : Word)
    (h : ∀ y, ¬ Z y → R y = R' y) : ∀ y, ¬ Z y → ramWrite R a v .w y = ramWrite R' a v .w y := by
  intro y hy
  simp only [ramWrite, ramPut]
  split
  · rfl
  split
  · rfl
  split
  · rfl
  split
  · rfl
  exact h y hy

/-- The RAM of the backward misaligned path: head bytes `H`, `J + 1`
    merged words (the last one through its own temporary), tail bytes `T`;
    outside `Z` (the temporaries) the result is the backward copy. -/
theorem bmis_ram (Z : Word → Prop) (R0 R1 R' R2 Rt R3 R4 : Word → BitVec 8) (P Q p0 A W Sx : Word)
    (H J T : Nat)
    (hR1 : R1 = bwd R0 P Q H) (hR' : ∀ y, ¬ Z y → R' y = R1 y)
    (hR2 : R2 = wordsB R' p0 A J) (hRt : ∀ y, ¬ Z y → Rt y = R2 y)
    (hR3 : R3 = ramWrite Rt (A - W) (ramRead R2 (p0 - BitVec.ofNat 32 (4 * J)) .w) .w)
    (hR4 : R4 = bwd R3 Sx (A - W) T)
    -- arithmetic of the path
    (hW : W.toNat = 4 * (J + 1)) (hp0 : p0 + 3 = P - BitVec.ofNat 32 H) (hA : A = Q - BitVec.ofNat 32 H)
    (hSx : Sx = P - BitVec.ofNat 32 (H + W.toNat)) (hAW : A - W = Q - BitVec.ofNat 32 (H + W.toNat))
    (c1 : 4 * J ≤ A.toNat) (c2 : 4 * J ≤ p0.toNat + 3) (c3 : p0.toNat + 4 < 2 ^ 32) (c4 : p0.toNat + 4 ≤ A.toNat)
    (c5 : 4 * J + 1 ≤ p0.toNat) (c6 : W.toNat ≤ A.toNat)
    -- the copy's reads and writes avoid the temporaries
    (zr : ∀ i < 4 * (J + 1), ¬ Z (p0 + 3 - BitVec.ofNat 32 i))
    (zw : ∀ i < 4 * (J + 1), ¬ Z (A + 0xffffffff#32 - BitVec.ofNat 32 i))
    (zr' : ∀ i < 4, ¬ Z (p0 - BitVec.ofNat 32 (4 * J) + BitVec.ofNat 32 i))
    (zt : ∀ i < T, ¬ Z (Sx - BitVec.ofNat 32 i)) (zt' : ∀ i < T, ¬ Z (A - W + 0xffffffff#32 - BitVec.ofNat 32 i)) :
    ∀ y, ¬ Z y → R4 y = bwd R0 P Q (H + W.toNat + T) y := by
  -- the ideal RAM after the words
  let I2 := wordsB R1 p0 A J
  have eI2 : I2 = bwd R1 (p0 + 3) A (4 * J) := wordsB_eq_bwd J R1 p0 A c1 c2 c3 c4
  have eR2 : R2 = bwd R' (p0 + 3) A (4 * J) := by rw [hR2]; exact wordsB_eq_bwd J R' p0 A c1 c2 c3 c4
  have f2 : ∀ y, ¬ Z y → R2 y = I2 y := by
    intro y hy
    rw [eR2, eI2]
    exact bwd_frame Z (4 * J) R' R1 _ _ hR' (fun i hi => zr i (by omega))
      (fun i hi => zw i (by omega)) y hy
  -- the last word
  let I3 := ramWrite I2 (A - W) (ramRead I2 (p0 - BitVec.ofNat 32 (4 * J)) .w) .w
  have hrd : ramRead R2 (p0 - BitVec.ofNat 32 (4 * J)) .w = ramRead I2 (p0 - BitVec.ofNat 32 (4 * J)) .w :=
    ramRead_congr (fun i hi => f2 _ (zr' i hi))
  have f3 : ∀ y, ¬ Z y → R3 y = I3 y := by
    intro y hy
    rw [hR3, hrd]
    exact ramWrite_off Z Rt I2 _ _ (fun y hy => (hRt y hy).trans (f2 y hy)) y hy
  have eI3 : I3 = bwd R1 (p0 + 3) A (4 * J + 4) := by
    show ramWrite I2 (A - W) (ramRead I2 (p0 - BitVec.ofNat 32 (4 * J)) .w) .w = _
    rw [show A - W = (A - BitVec.ofNat 32 (4 * J)) + 0xfffffffc#32 by bv_omega,
      word_bwd I2 _ _ (by bv_omega) (by bv_omega) (by bv_omega), eI2, bwd_add]
    exact bwd_congr (by bv_omega) (by bv_omega)
  -- the tail
  have f4 : ∀ y, ¬ Z y → R4 y = bwd I3 Sx (A - W) T y := by
    intro y hy
    rw [hR4]
    exact bwd_frame Z T R3 I3 _ _ f3 zt zt' y hy
  intro y hy
  rw [f4 y hy, eI3, hR1, show 4 * J + 4 = W.toNat by omega, bwd_add (H + W.toNat) T, bwd_add H W.toNat,
    hAW, hSx, hp0, hA]

/-! ## Dispatch on the misalignment -/

theorem bstart_any (g : Core) (R : Word → BitVec 8) (o : Nat) (ho : 0 < o ∧ o < 4) (hpc : g.pc = 0x80020e00)
    (hq : Quiet g) (h6 : g.get 6 = BitVec.ofNat 32 o) (h56 : (g.get 5).toNat % 4 = o)
    (hsr : B.inRam (g.get 5 - BitVec.ofNat 32 o) o = true) (hT : B.inRam (g.get 2 + 0x1a#32) 4 = true)
    (hsep : (g.get 5).toNat ≤ (g.get 2 + 0x1a#32).toNat ∨
      (g.get 2 + 0x1a#32).toNat + 4 ≤ (g.get 5 - BitVec.ofNat 32 o).toNat)
    (hs1 : o ≤ (g.get 5).toNat) (hlp : (g.get 28 + 4#32).ult (g.get 7) = true) :
    ∃ k g' R', QRun B img k ⟨g, R⟩ ⟨g', R'⟩ ∧ AtBL g g' R R' o := by
  rcases (by omega : o = 1 ∨ o = 2 ∨ o = 3) with rfl | rfl | rfl
  · obtain ⟨g', R', hr, ha⟩ := bstart1 g R hpc hq h6 hsr hT hsep hs1 hlp
    exact ⟨_, g', R', hr, ha⟩
  · obtain ⟨g', R', hr, ha⟩ := bstart2 g R hpc hq h6 h56 hsr hT hsep hs1 hlp
    exact ⟨_, g', R', hr, ha⟩
  · obtain ⟨g', R', hr, ha⟩ := bstart3 g R hpc hq h6 h56 hsr hT hsep hs1 hlp
    exact ⟨_, g', R', hr, ha⟩

theorem bend_any (g : Core) (R0 : Word → BitVec 8) (Lq : Word) (o : Nat) (ho : 0 < o ∧ o < 4)
    (hpc : g.pc = 0x8002103a) (hq : Quiet g)
    (hLq : g.get 30 + g.get 18 = Lq) (h6 : g.get 6 = BitVec.ofNat 32 o) (h29 : g.get 29 = BitVec.ofNat 32 (8 * o))
    (hprev : ∀ k, k < o → byteOf (g.get 15) k = R0 (Lq + BitVec.ofNat 32 k))
    (hL : Lq.toNat % 4 = 0) (hL4 : 4 ≤ Lq.toNat)
    (hsrc : B.inRam (Lq + 0xfffffffc#32 + BitVec.ofNat 32 o) (4 - o) = true)
    (hT : B.inRam (g.get 2 + 0x20#32) 4 = true) (hTa : (g.get 2 + 0x20#32).toNat % 4 = 0)
    (hsep : ∀ j < 4 - o, ∀ i < 4, Lq + 0xfffffffc#32 + BitVec.ofNat 32 o + BitVec.ofNat 32 j ≠
      g.get 2 + 0x20#32 + BitVec.ofNat 32 i)
    (hD : (g.get 11 + 0xfffffffc#32).toNat % 4 = 0) (hDr : B.inRam (g.get 11 + 0xfffffffc#32) 4 = true) :
    ∃ k g' R', QRun B img k ⟨g, R0⟩ ⟨g', R'⟩ ∧ AtBT g g' R0 R' Lq o := by
  rcases (by omega : o = 1 ∨ o = 2 ∨ o = 3) with rfl | rfl | rfl
  · obtain ⟨g', R', hr, ha⟩ := bend1 g R0 Lq hpc hq hLq h6 h29 hprev hL hL4 hsrc hT hTa hsep hD hDr
    exact ⟨_, g', R', hr, ha⟩
  · obtain ⟨g', R', hr, ha⟩ := bend2 g R0 Lq hpc hq hLq h6 h29 hprev hL hL4 hsrc hT hTa hsep hD hDr
    exact ⟨_, g', R', hr, ha⟩
  · obtain ⟨g', R', hr, ha⟩ := bend3 g R0 Lq hpc hq hLq h6 h29 hprev hL hL4 hsrc hT hTa hsep hD hDr
    exact ⟨_, g', R', hr, ha⟩

/-- The backward temporaries: sp+0x1a..sp+0x23 of the callee frame. -/
def InTB (sp x : Word) : Prop := sp.toNat - 22 ≤ x.toNat ∧ x.toNat < sp.toNat - 12

theorem bvi1 : ∀ x y z u : Word, x - y + z + (0 - u) = z + x - u - y := by intros; bv_omega

theorem bvi2 : ∀ x y z u : Word, x + y - z + (0 - u) = x + y + (0 - u) - z := by intros; bv_omega

theorem bvi3 : ∀ x y z u v : Word, x - y + z - v + (0 - u) = z + x - u - y - v := by intros; bv_omega

theorem bvL1 (a y c : Word) : a - y + c + y = a + c := by bv_omega

theorem bvL2 (a : Word) : a + 0xfffffffc#32 + 3 = a + 0xffffffff#32 := by bv_omega

theorem bvL3 (a y z c : Word) : a - y - z + c + y = a - z + c := by bv_omega

theorem bvi4 : ∀ x y z : Word, x - y + 0xfffffffc#32 + y + 3 - z = x + 0xffffffff#32 - z := by
  intros; rw [bvL1, bvL2]

theorem bvi5 : ∀ x y z w : Word, x - y + 0xfffffffc#32 + y - z + w = x + 0xfffffffc#32 - z + w := by
  intros; rw [bvL1]

theorem bvi6 : ∀ x y z w : Word, x - y - z + 0xfffffffc#32 + y + w = x - z + 0xfffffffc#32 + w := by
  intros; rw [bvL3]

/-- Arithmetic of the backward misaligned path, in the forms its pieces use;
    `L0`/`Lq` are the loop's source word base before/after its `J` words. -/
structure BMArith2 (d s n sp H A W T : Word) (o J : Nat) : Prop where
  o6 : (s + n - H) &&& 3#32 = BitVec.ofNat 32 o
  o56 : (s + n - H).toNat % 4 = o
  ho : 0 < o ∧ o < 4
  sr : B.inRam (s + n - H - BitVec.ofNat 32 o) o = true
  t1a : B.inRam (sp + 0xffffffd0#32 + 0x1a#32) 4 = true
  sep1 : (s + n - H).toNat ≤ (sp + 0xffffffd0#32 + 0x1a#32).toNat ∨
    (sp + 0xffffffd0#32 + 0x1a#32).toNat + 4 ≤ (s + n - H - BitVec.ofNat 32 o).toNat
  s1 : o ≤ (s + n - H).toNat
  lp : (A - W + 4#32).ult A = true
  D : d + n + (0 - H) = A - W + 4#32 + BitVec.ofNat 32 (4 * J)
  dl : (A - W + 4#32).toNat + 4 * J < 2 ^ 32
  lo : 4 * J ≤ (n - BitVec.ofNat 32 o + s + (0 - H)).toNat
  L0a : (n - BitVec.ofNat 32 o + s + (0 - H)).toNat % 4 = 0
  Ta : (A - W + 4#32).toNat % 4 = 0
  dir : (n - BitVec.ofNat 32 o + s + (0 - H)).toNat + o ≤ (d + n + (0 - H)).toNat
  L0 : n - BitVec.ofNat 32 o + s + (0 - H) = s + n - H - BitVec.ofNat 32 o
  hs : B.inRam (n - BitVec.ofNat 32 o + s + (0 - H) - BitVec.ofNat 32 (4 * J)) (4 * J) = true
  hd : B.inRam (A - W + 4#32) (4 * J) = true
  Lq : n - BitVec.ofNat 32 o + s - BitVec.ofNat 32 (4 * J) + (0 - H) =
    n - BitVec.ofNat 32 o + s + (0 - H) - BitVec.ofNat 32 (4 * J)
  La : (n - BitVec.ofNat 32 o + s - BitVec.ofNat 32 (4 * J) + (0 - H)).toNat % 4 = 0
  L4 : 4 ≤ (n - BitVec.ofNat 32 o + s - BitVec.ofNat 32 (4 * J) + (0 - H)).toNat
  src : B.inRam (n - BitVec.ofNat 32 o + s - BitVec.ofNat 32 (4 * J) + (0 - H) + 0xfffffffc#32 + BitVec.ofNat 32 o)
    (4 - o) = true
  t20 : B.inRam (sp + 0xffffffd0#32 + 0x20#32) 4 = true
  t20a : (sp + 0xffffffd0#32 + 0x20#32).toNat % 4 = 0
  sep2 : ∀ j < 4 - o, ∀ i < 4, n - BitVec.ofNat 32 o + s - BitVec.ofNat 32 (4 * J) + (0 - H) + 0xfffffffc#32 +
    BitVec.ofNat 32 o + BitVec.ofNat 32 j ≠ sp + 0xffffffd0#32 + 0x20#32 + BitVec.ofNat 32 i
  e11 : d + n - BitVec.ofNat 32 (4 * J) + (0 - H) + 0xfffffffc#32 = A - W
  AWa : (A - W).toNat % 4 = 0
  AWr : B.inRam (A - W) 4 = true
  q : d + n + (0 - H) = A
  p0 : n - BitVec.ofNat 32 o + s + (0 - H) + 0xfffffffc#32 + BitVec.ofNat 32 o + 3 =
    s + n + 0xffffffff#32 - BitVec.ofNat 32 H.toNat
  A' : A = d + n - BitVec.ofNat 32 H.toNat
  Sx : s + n - H - W + 0xffffffff#32 = s + n + 0xffffffff#32 - BitVec.ofNat 32 (H.toNat + W.toNat)
  AW : A - W = d + n - BitVec.ofNat 32 (H.toNat + W.toNat)
  p0' : n - BitVec.ofNat 32 o + s + (0 - H) + 0xfffffffc#32 + BitVec.ofNat 32 o - BitVec.ofNat 32 (4 * J) =
    n - BitVec.ofNat 32 o + s - BitVec.ofNat 32 (4 * J) + (0 - H) + 0xfffffffc#32 + BitVec.ofNat 32 o
  c1 : 4 * J ≤ A.toNat
  c2 : 4 * J ≤ (n - BitVec.ofNat 32 o + s + (0 - H) + 0xfffffffc#32 + BitVec.ofNat 32 o).toNat + 3
  c3 : (n - BitVec.ofNat 32 o + s + (0 - H) + 0xfffffffc#32 + BitVec.ofNat 32 o).toNat + 4 < 2 ^ 32
  c4 : (n - BitVec.ofNat 32 o + s + (0 - H) + 0xfffffffc#32 + BitVec.ofNat 32 o).toNat + 4 ≤ A.toNat
  c5 : 4 * J + 1 ≤ (n - BitVec.ofNat 32 o + s + (0 - H) + 0xfffffffc#32 + BitVec.ofNat 32 o).toNat
  c6 : W.toNat ≤ A.toNat
  zr : ∀ i < 4 * (J + 1),
    ¬ InTB sp (n - BitVec.ofNat 32 o + s + (0 - H) + 0xfffffffc#32 + BitVec.ofNat 32 o + 3 - BitVec.ofNat 32 i)
  zw : ∀ i < 4 * (J + 1), ¬ InTB sp (A + 0xffffffff#32 - BitVec.ofNat 32 i)
  zr' : ∀ i < 4, ¬ InTB sp (n - BitVec.ofNat 32 o + s + (0 - H) + 0xfffffffc#32 + BitVec.ofNat 32 o -
    BitVec.ofNat 32 (4 * J) + BitVec.ofNat 32 i)
  zt : ∀ i < T.toNat, ¬ InTB sp (s + n - H - W + 0xffffffff#32 - BitVec.ofNat 32 i)
  zt' : ∀ i < T.toNat, ¬ InTB sp (A - W + 0xffffffff#32 - BitVec.ofNat 32 i)
  nT : n.toNat = H.toNat + W.toNat + T.toNat

set_option maxHeartbeats 20000000 in
theorem bmis_arith (d s n sp H A W T : Word) (o J : Nat)
    (hdr : 0x80029bc8 ≤ d.toNat ∧ d.toNat + n.toNat ≤ 0x81000000)
    (hsr : 0x80029bc8 ≤ s.toNat ∧ s.toNat + n.toNat ≤ 0x81000000)
    (hn : 16 ≤ n.toNat) (hle : s.toNat ≤ d.toNat) (hnc : s.toNat % 4 ≠ d.toNat % 4)
    (hH : H.toNat = (d + n).toNat % 4) (hA : A.toNat = (d + n).toNat - (d + n).toNat % 4)
    (hW : W.toNat = (n - H).toNat - (n - H).toNat % 4) (hT : T.toNat = (n - H).toNat % 4)
    (hspa : sp.toNat % 4 = 0) (hst : 0x80029bc8 + 48 ≤ sp.toNat ∧ sp.toNat ≤ 0x81000000)
    (hdsep : d.toNat + n.toNat + 48 ≤ sp.toNat ∨ sp.toNat ≤ d.toNat)
    (hssep : s.toNat + n.toNat + 48 ≤ sp.toNat ∨ sp.toNat ≤ s.toNat)
    (hoo : o = (s + n - H).toNat % 4) (hJ : 4 * (J + 1) = W.toNat) :
    BMArith2 d s n sp H A W T o J := by
  have hD : (d + n).toNat = d.toNat + n.toNat := by bv_omega
  have hH4 : H.toNat < 4 := by omega
  have hM : (n - H).toNat = n.toNat - H.toNat := by bv_omega
  have kA : A.toNat + H.toNat = d.toNat + n.toNat := by omega
  have kW : W.toNat + T.toNat + H.toNat = n.toNat := by omega
  have kT : T.toNat < 4 := by omega
  have kW4 : W.toNat % 4 = 0 := by omega
  have kA4 : A.toNat % 4 = 0 := by omega
  have kH : H.toNat = (d.toNat + n.toNat) % 4 := by omega
  have kSH : (s + n - H).toNat = s.toNat + n.toNat - H.toNat := by bv_omega
  have ko : o = (s.toNat + n.toNat - H.toNat) % 4 := by rw [hoo, kSH]
  have ko0 : 0 < o := by omega
  clear hnc
  have ko4 : o < 4 := by omega
  have kJ : 4 * (J + 1) = W.toNat := hJ
  have ho' : (BitVec.ofNat 32 o).toNat = o := by simp; omega
  have o6 : (s + n - H) &&& 3#32 = BitVec.ofNat 32 o := by
    apply BitVec.eq_of_toNat_eq; rw [and3, ho', kSH, ko]
  clear hH hA hW hT hD hM hoo
  -- canonical forms of the loop's wrapping sums (s2 = -H)
  have i1 := bvi1
  have i2 := bvi2
  have i3 := bvi3
  have eQ : d + n + (0 - H) = A := by bv_omega
  have kL0 : (s + n - H - BitVec.ofNat 32 o).toNat = s.toNat + n.toNat - H.toNat - o := by bv_omega
  have hTBs : ∀ y : Word, s.toNat ≤ y.toNat → y.toNat < s.toNat + n.toNat → ¬ InTB sp y := by
    intro y h1 h2 hT; unfold InTB at hT; omega
  have hsepT : ∀ y : Word, s.toNat ≤ y.toNat → y.toNat < s.toNat + n.toNat →
      ∀ i < 4, y ≠ sp + 0xffffffd0#32 + 0x20#32 + BitVec.ofNat 32 i := by
    intro y h1 h2 i hi e
    have hy : y.toNat = sp.toNat - 16 + i := by rw [e]; bv_omega
    omega
  have i4 := bvi4
  have i5 := bvi5
  have i6 := bvi6
  have hzr : ∀ i < 4 * (J + 1), ¬ InTB sp
      (n - BitVec.ofNat 32 o + s + (0 - H) + 0xfffffffc#32 + BitVec.ofNat 32 o + 3 - BitVec.ofNat 32 i) := by
    intro i hi; rw [i1, i4]
    apply hTBs <;>
      (clear hdsep hssep ko kH kA kA4 kW4 o6 ho' kL0 eQ hdr hTBs hsepT i1 i2 i3 i4 i5 i6
       generalize s + n - H = SH at kSH ⊢; bv_omega)
  have hzr' : ∀ i < 4, ¬ InTB sp (n - BitVec.ofNat 32 o + s + (0 - H) + 0xfffffffc#32 + BitVec.ofNat 32 o -
      BitVec.ofNat 32 (4 * J) + BitVec.ofNat 32 i) := by
    intro i hi; rw [i1, i5]
    apply hTBs <;>
      (clear hdsep hssep ko kH kA kA4 kW4 o6 ho' kL0 eQ hdr hTBs hsepT i1 i2 i3 i4 i5 i6
       generalize s + n - H = SH at kSH ⊢; bv_omega)
  have hsep2 : ∀ j < 4 - o, ∀ i < 4, n - BitVec.ofNat 32 o + s - BitVec.ofNat 32 (4 * J) + (0 - H) + 0xfffffffc#32 +
      BitVec.ofNat 32 o + BitVec.ofNat 32 j ≠ sp + 0xffffffd0#32 + 0x20#32 + BitVec.ofNat 32 i := by
    intro j hj i hi; rw [i3, i6]
    apply hsepT _ _ _ i hi <;>
      (clear hdsep hssep ko kH kA kA4 kW4 o6 ho' kL0 eQ hdr hTBs hsepT i1 i2 i3 i4 i5 i6
       generalize s + n - H = SH at kSH ⊢; bv_omega)
  clear i4 i5 i6
  clear hTBs hsepT
  refine {
      o6 := o6
      o56 := ?_
      ho := ⟨ko0, ko4⟩
      sr := ?_
      t1a := ?_
      sep1 := ?_
      s1 := ?_
      lp := ?_
      D := ?_
      dl := ?_
      lo := ?_
      L0a := ?_
      Ta := ?_
      dir := ?_
      L0 := ?_
      hs := ?_
      hd := ?_
      Lq := ?_
      La := ?_
      L4 := ?_
      src := ?_
      t20 := ?_
      t20a := ?_
      sep2 := hsep2
      e11 := ?_
      AWa := ?_
      AWr := ?_
      q := ?_
      p0 := ?_
      A' := ?_
      Sx := ?_
      AW := ?_
      p0' := ?_
      c1 := ?_
      c2 := ?_
      c3 := ?_
      c4 := ?_
      c5 := ?_
      c6 := ?_
      zr := hzr
      zw := ?_
      zr' := hzr'
      zt := ?_
      zt' := ?_
      nT := ?_ }
  all_goals (try intro i hi); all_goals (try intro i' hi')
  all_goals (try simp only [i1, i3])
  all_goals (try simp only [i2])
  all_goals (try simp only [eQ])
  all_goals (clear i1 i2 i3)
  all_goals (try generalize s + n - H - BitVec.ofNat 32 o = L0 at *)
  all_goals (try unfold InTB)
  all_goals (try simp only [B_ram])
  all_goals (try simp only [BitVec.ult, decide_eq_true_iff])
  all_goals first
    | (clear hdsep hssep; omega)
    | (clear hdsep hssep; refine ⟨?_, ?_⟩ <;> bv_omega)
    | (clear hdsep hssep; bv_omega)
    | (refine ⟨?_, ?_⟩ <;> bv_omega)
    | bv_omega

end E5R.Rmk
