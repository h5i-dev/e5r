/-
  `Deframer::next`: the exit test at 0x8001d4f8 (no complete frame left) to `NextPost`.

  Original e5r code, Apache-2.0.

  PROVED here: `exit_post`: from 0x8001d4f8 with next's frame intact, s0 = filled ≤ len, s7 ≤ 1
  and the deframer fields as stored, every one of the four exits (discarding: consumed := filled,
  discarding := 1; filled ≠ len; cursor ≠ 0; a full buffer without a delimiter: discard) returns
  `None` and meets `NextPost`.
-/
import Projects.rmk.Deframer.NextRet

set_option maxRecDepth 100000

namespace E5R.Rmk.Deframer.Next
open E5R E5R.Rmk.NextFetch E5R.Rmk.Deframer.Tail

structure XAt (c : Core) (R0 : Word → BitVec 8) (e : Core) (M : Word → BitVec 8) : Prop where
  pc : e.pc = 0x8001d4f8
  quiet : Quiet e
  csr : e.sameCsr c
  sp : e.get 2 = ng c
  kept : ∀ r : Reg, r.val ∈ nkept → e.get r = c.get r
  slots : NSlots c M
  len : e.get 18 = c.get 12
  self : e.get 19 = c.get 10
  s7 : (e.get 23).toNat ≤ 1
  fle : (e.get 8).toNat ≤ (c.get 12).toNat
  fcur : (ramRead M (c.get 10) .w).toNat ≤ (e.get 8).toNat
  ffil : ramRead M (c.get 10 + 4) .w = e.get 8
  fdisc : (M (c.get 10 + 8)).toNat = (e.get 23).toNat
  ram : ∀ x, Outside (c.get 10) (c.get 11) (c.get 12).toNat (c.get 2) nextStack x → M x = R0 x

theorem and1 (x : Word) (h : x.toNat ≤ 1) : alu .and x 0x00000001#32 = x := by
  have : x = 0 ∨ x = 1 := by bv_omega
  rcases this with rfl | rfl <;> rfl

/-- The discarding stores: consumed := filled, discarding := 1. -/
def xstore (M : Word → BitVec 8) (p f : Word) : Word → BitVec 8 :=
  ramWrite (ramWrite M p f .w) (p + 0x00000008#32) (alu .add 0 0x00000001#32) .b

theorem xstore_other (M : Word → BitVec 8) (p f x : Word) (hp : p.toNat + 12 ≤ 2 ^ 32)
    (hx : x.toNat < p.toNat ∨ p.toNat + 12 ≤ x.toNat) : xstore M p f x = M x := by
  have e8 : (p + 0x00000008#32).toNat = p.toNat + 8 := add_toNat p 8 (by omega)
  unfold xstore
  rw [ramWrite, ramPut_ne _ (fun h => by rw [h, e8] at hx; omega), wr_byte_other _ _ _ _ (by omega) (by omega)]

theorem xstore_cons (M : Word → BitVec 8) (p f : Word) (hp : p.toNat + 12 ≤ 2 ^ 32) :
    ramRead (xstore M p f) p .w = f := by
  have e8 : (p + 0x00000008#32).toNat = p.toNat + 8 := add_toNat p 8 (by omega)
  unfold xstore
  rw [show ramRead (ramWrite (ramWrite M p f .w) (p + 0x00000008#32) (alu .add 0 0x00000001#32) .b) p .w =
      ramRead (ramWrite M p f .w) p .w from rd_congr p (by omega) fun x h1 h2 => by
        rw [ramWrite, ramPut_ne _ (fun h => by rw [h, e8] at h2; omega)],
    ramRead_ramWrite_w]

theorem xstore_mid (M : Word → BitVec 8) (p f x : Word) (hp : p.toNat + 12 ≤ 2 ^ 32)
    (h1 : p.toNat + 4 ≤ x.toNat) (h2 : x.toNat < p.toNat + 8) : xstore M p f x = M x := by
  have e8 : (p + 0x00000008#32).toNat = p.toNat + 8 := add_toNat p 8 (by omega)
  unfold xstore
  rw [ramWrite, ramPut_ne _ (fun h => by rw [h, e8] at h2; omega), wr_byte_other _ _ _ _ (by omega) (by omega)]

theorem xstore_fil (M : Word → BitVec 8) (p f : Word) (hp : p.toNat + 12 ≤ 2 ^ 32) :
    ramRead (xstore M p f) (p + 4) .w = ramRead M (p + 4) .w := by
  have e4 : (p + 4).toNat = p.toNat + 4 := add_toNat p 4 (by omega)
  exact rd_congr _ (by omega) fun x h1 h2 => xstore_mid M p f x hp (by omega) (by omega)

theorem xstore_disc (M : Word → BitVec 8) (p f : Word) :
    (xstore M p f (p + 8)).toNat = 1 := by
  unfold xstore; rw [ramWrite, show (p + 8 : Word) = p + 0x00000008#32 from rfl, ramPut_eq]; rfl


/-- `RetAt` from an exit: a0 = 0 (None), everything else as at the exit test, up to the
    deframer stores. -/
theorem retAt_of (c : Core) (R0 : Word → BitVec 8) (e : Core) (M : Word → BitVec 8) (h : XAt c R0 e M)
    (e' : Core) (M' : Word → BitVec 8) (hpc : e'.pc = 0x8001d510) (hcs : e'.sameCsr e)
    (hsp : e'.get 2 = e.get 2) (hk : ∀ r : Reg, r.val ∈ nkept → e'.get r = e.get r)
    (hsl : ∀ x : Word, (c.get 2).toNat - 0x40 ≤ x.toNat → x.toNat < (c.get 2).toNat → M' x = M x)
    (ha0 : e'.get 10 = 0) (hinv : Inv M' (c.get 10) (c.get 12).toNat) (hdisc : discarding M' (c.get 10) ≤ 1)
    (hram : ∀ x, Outside (c.get 10) (c.get 11) (c.get 12).toNat (c.get 2) nextStack x → M' x = M x)
    (hg : 0x40 ≤ (c.get 2).toNat ∧ (c.get 2).toNat < 2 ^ 32) :
    RetAt c R0 e' M' := by
  refine ⟨hpc, Quiet.of_sameCsr hcs h.quiet, hcs.trans h.csr, hsp.trans h.sp,
    fun r hr => (hk r hr).trans (h.kept r hr), ?_, by rw [ha0]; decide,
    fun h1 => absurd h1 (by rw [ha0]; decide), hinv, hdisc,
    fun x hx => (hram x hx).trans (h.ram x hx)⟩
  intro o r hm
  rw [← h.slots o r hm]
  have ho : 0xc ≤ o ∧ o + 4 ≤ 0x40 := by
    simp only [nslots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
      ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have eg : (ng c).toNat = (c.get 2).toNat - 0x40 := by unfold ng; bv_omega
  have eo : (ng c + BitVec.ofNat 32 o).toNat = (ng c).toNat + o := add_toNat _ _ (by omega)
  exact rd_congr _ (by omega) fun x h1 h2 => hsl x (by omega) (by omega)

theorem exit_post (c : Core) (R0 : Word → BitVec 8) (E : CallEnv nextPc nextStack ⟨c, R0⟩)
    (e : Core) (M : Word → BitVec 8) (h : XAt c R0 e M) :
    ∃ k m, QRun B img k ⟨e, M⟩ m ∧ NextPost ⟨c, R0⟩ m := by
  have hst := stack_nat (c.get 2) nextStack E.stack
  rw [show nextStack = 0x70 from rfl] at hst
  have hp := (B_ram (c.get 10) 12).mp E.self
  have hsep : (c.get 10).toNat + 12 ≤ (c.get 2).toNat - 0x70 ∧
      (c.get 11).toNat + (c.get 12).toNat ≤ (c.get 2).toNat - 0x70 := E.stackSep
  have hg : 0x40 ≤ (c.get 2).toNat ∧ (c.get 2).toNat < 2 ^ 32 := ⟨by omega, (c.get 2).isLt⟩
  have hs7 := h.s7
  have hfl := h.fle
  have hfc := h.fcur
  have hfd := h.fdisc
  have hff := h.ffil
  have e19 := h.self
  have e8a : (c.get 10 + 0x00000008#32).toNat = (c.get 10).toNat + 8 := add_toNat _ 8 (by omega)
  have al19 : (e.get 19).toNat % 4 = 0 := by rw [e19]; exact E.selfAl
  have in19 : B.inRam (e.get 19) 4 = true := by rw [e19, B_ram]; omega
  have al8 : (e.get 19 + 0x00000008#32).toNat % 1 = 0 := Nat.mod_one _
  have in8 : B.inRam (e.get 19 + 0x00000008#32) 1 = true := by rw [e19, B_ram, e8a]; omega
  -- the discarding exit (nx1, nx4): consumed := filled, discarding := 1
  have disc_exit : ∀ (e' : Core), e'.pc = 0x8001d510 → e'.sameCsr e → e'.get 2 = e.get 2 →
      (∀ r : Reg, r.val ∈ nkept → e'.get r = e.get r) → e'.get 10 = 0 →
      RetAt c R0 e' (xstore M (e.get 19) (e.get 8)) := by
    intro e' a b d' f' g'
    rw [e19]
    refine retAt_of c R0 e M h e' _ a b d' f' ?_ g' ?_ ?_ ?_ hg
    · intro x h1 h2; exact xstore_other M _ _ x (by omega) (.inr (by omega))
    · show (ramRead (xstore M (c.get 10) (e.get 8)) (c.get 10) .w).toNat ≤
        (ramRead (xstore M (c.get 10) (e.get 8)) (c.get 10 + 4) .w).toNat ∧
        (ramRead (xstore M (c.get 10) (e.get 8)) (c.get 10 + 4) .w).toNat ≤ (c.get 12).toNat
      rw [xstore_cons M _ _ (by omega), xstore_fil M _ _ (by omega), hff]; omega
    · show (xstore M (c.get 10) (e.get 8) (c.get 10 + 8)).toNat ≤ 1
      rw [xstore_disc]; decide
    · intro x hx
      have h1 : ¬ ((c.get 10).toNat ≤ x.toNat ∧ x.toNat < (c.get 10).toNat + 12) := hx.1
      exact xstore_other M _ _ x (by omega) (by omega)
  -- the keeping exits (nx2, nx3)
  have keep_exit : ∀ (e' : Core), e'.pc = 0x8001d510 → e'.sameCsr e → e'.get 2 = e.get 2 →
      (∀ r : Reg, r.val ∈ nkept → e'.get r = e.get r) → e'.get 10 = 0 → RetAt c R0 e' M := by
    intro e' a b d' f' g'
    refine retAt_of c R0 e M h e' M a b d' f' (fun _ _ _ => rfl) g' ?_ ?_ (fun _ _ => rfl) hg
    · show (ramRead M (c.get 10) .w).toNat ≤ (ramRead M (c.get 10 + 4) .w).toNat ∧
        (ramRead M (c.get 10 + 4) .w).toNat ≤ (c.get 12).toNat
      rw [hff]; omega
    · show (M (c.get 10 + 8)).toNat ≤ 1
      rw [hfd]; exact hs7
  have kept_of : ∀ (e' : Core), (∀ r : Reg, r ≠ 10 → r ≠ 11 → e'.get r = e.get r) →
      ∀ r : Reg, r.val ∈ nkept → e'.get r = e.get r := by
    intro e' hk r hr
    exact hk r (fun h => by subst h; exact absurd hr (by decide)) (fun h => by subst h; exact absurd hr (by decide))
  by_cases h1 : e.get 23 = 1
  · have w : taken .ne (alu .and (e.get 23) 0x00000001#32) 0 = true := by rw [and1 _ hs7, h1]; rfl
    have r := nx1 e M h.pc h.quiet w al19 in19 al8 in8
    obtain ⟨k, m, r2, post⟩ := ret_post c R0 E _ _ (disc_exit (nx1Core e M) rfl (by unfold nx1Core; (repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_)))
      (by simp [nx1Core, Core.wr_get_ne]) (kept_of _ fun r a b => by simp [nx1Core, Core.wr_get_ne, a, b])
      (by simp [nx1Core, Core.wr_get_ne, Core.wr_get_self, alu_add]))
    exact ⟨_, m, r.trans r2, post⟩
  · have h0 : e.get 23 = 0 := by
      have : (e.get 23).toNat ≠ 1 := fun h' => h1 (BitVec.eq_of_toNat_eq h')
      exact BitVec.eq_of_toNat_eq (by show (e.get 23).toNat = 0; omega)
    have w : taken .ne (alu .and (e.get 23) 0x00000001#32) 0 = false := by rw [and1 _ hs7, h0]; rfl
    have a0z : alu .and (e.get 23) 0x00000001#32 = 0 := by rw [and1 _ hs7, h0]
    by_cases h2 : e.get 8 = e.get 18
    · have w2 : taken .ne (e.get 8) (e.get 18) = false := by simp [taken, h2]
      by_cases h3 : e.get 9 = 0
      · have w3 : taken .ne (e.get 9) 0 = false := by simp [taken, h3]
        have r := nx4 e M h.pc h.quiet w w2 w3 al19 in19 al8 in8
        obtain ⟨k, m, r2, post⟩ := ret_post c R0 E _ _ (disc_exit (nx4Core e M) rfl (by unfold nx4Core; (repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_)))
          (by simp [nx4Core, Core.wr_get_ne]) (kept_of _ fun r a b => by simp [nx4Core, Core.wr_get_ne, a, b])
          (by simp [nx4Core, Core.wr_get_ne, Core.wr_get_self, alu_add]))
        exact ⟨_, m, r.trans r2, post⟩
      · have w3 : taken .ne (e.get 9) 0 = true := by simp only [taken, bne_iff_ne, ne_eq]; exact h3
        have r := nx3 e M h.pc h.quiet w w2 w3
        obtain ⟨k, m, r2, post⟩ := ret_post c R0 E _ _ (keep_exit (nx3Core e M) rfl (by unfold nx3Core; (repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_)))
          (by simp [nx3Core, Core.wr_get_ne]) (kept_of _ fun r a b => by simp [nx3Core, Core.wr_get_ne, a, b])
          (by simp [nx3Core, Core.wr_get_ne, Core.wr_get_self]; exact a0z))
        exact ⟨_, m, r.trans r2, post⟩
    · have w2 : taken .ne (e.get 8) (e.get 18) = true := by simp [taken, h2]
      have r := nx2 e M h.pc h.quiet w w2
      obtain ⟨k, m, r2, post⟩ := ret_post c R0 E _ _ (keep_exit (nx2Core e M) rfl (by unfold nx2Core; (repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_)))
        (by simp [nx2Core, Core.wr_get_ne]) (kept_of _ fun r a b => by simp [nx2Core, Core.wr_get_ne, a, b])
        (by simp [nx2Core, Core.wr_get_ne, Core.wr_get_self]; exact a0z))
      exact ⟨_, m, r.trans r2, post⟩

end E5R.Rmk.Deframer.Next
