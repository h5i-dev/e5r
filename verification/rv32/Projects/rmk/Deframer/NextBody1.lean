/-
  `Deframer::next`: one turn of the frame loop, part 1 (no call): the end of the pending bytes,
  the delimiter scan, and a delimiter found while discarding.

  Original e5r code, Apache-2.0.

  PROVED here:
  * `end_case`: LoopInv with cursor = filled => NextPost (via the exit test);
  * `scan_case`: LoopInv with cursor ≠ filled => either the exit test with no delimiter left
    (=> NextPost) or a delimiter at cursor + j (`FoundAt`);
  * `disc_case`: a delimiter found while discarding => LoopInv again, cursor := cursor + j + 1,
    discarding := 0 (so filled - cursor decreases).
-/
import Projects.rmk.Deframer.NextExit

set_option maxRecDepth 100000

namespace E5R.Rmk.Deframer.Next
open E5R E5R.Rmk.NextFetch E5R.Rmk.Deframer.Tail

theorem add_toNat' (x y : Word) (h : x.toNat + y.toNat < 2 ^ 32) : (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add]; omega

/-- Numbers from `next`'s entry environment. -/
structure EnvNat (c : Core) : Prop where
  sp : 0x80029bc8 + 0x70 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000
  self : 0x80029bc8 ≤ (c.get 10).toNat ∧ (c.get 10).toNat + 12 ≤ 0x81000000
  buf : 0x80029bc8 ≤ (c.get 11).toNat ∧ (c.get 11).toNat + (c.get 12).toNat ≤ 0x81000000
  len : (c.get 12).toNat = bufLen
  sepS : (c.get 10).toNat + 12 ≤ (c.get 2).toNat - 0x70 ∧ (c.get 11).toNat + (c.get 12).toNat ≤ (c.get 2).toNat - 0x70
  sep : (c.get 10).toNat + 12 ≤ (c.get 11).toNat ∨ (c.get 11).toNat + (c.get 12).toNat ≤ (c.get 10).toNat

theorem envNat (c : Core) (R0 : Word → BitVec 8) (E : CallEnv nextPc nextStack ⟨c, R0⟩) : EnvNat c := by
  have hst := stack_nat (c.get 2) nextStack E.stack
  rw [show nextStack = 0x70 from rfl] at hst
  exact ⟨hst, (B_ram _ _).mp E.self, (B_ram _ _).mp E.buf, E.len, E.stackSep, E.sep⟩

theorem ng_toNat (c : Core) (h : EnvNat c) : (ng c).toNat = (c.get 2).toNat - 0x40 := by
  have := h.sp; unfold ng; bv_omega

/-- The invariant again, from what a turn of the loop changes. -/
theorem loopInv_next (c : Core) (R0 : Word → BitVec 8) (hE : EnvNat c) (d : Core) (M : Word → BitVec 8)
    (h : LoopInv c R0 d M) (d' : Core) (M' : Word → BitVec 8) (hpc : d'.pc = 0x8001d476)
    (hcs : d'.sameCsr d) (hsame : ∀ r : Reg, r.val ∈ [0, 2, 3, 4, 8, 18, 19, 20, 24, 25, 26] → d'.get r = d.get r)
    (hs7 : (d'.get 23).toNat ≤ 1) (ha0 : d'.get 10 = d'.get 23) (hcur : (d'.get 9).toNat ≤ (d.get 8).toNat)
    (hsl : ∀ x : Word, (c.get 2).toNat - 0x40 + 0xc ≤ x.toNat → x.toNat < (c.get 2).toNat → M' x = M x)
    (hfc : ramRead M' (c.get 10) .w = d'.get 9) (hff : ramRead M' (c.get 10 + 4) .w = ramRead M (c.get 10 + 4) .w)
    (hfd : (M' (c.get 10 + 8)).toNat = (d'.get 23).toNat)
    (hram : ∀ x, Outside (c.get 10) (c.get 11) (c.get 12).toNat (c.get 2) nextStack x → M' x = M x) :
    LoopInv c R0 d' M' := by
  have g := fun r (hr : r ∈ [0, 2, 3, 4, 8, 18, 19, 20, 24, 25, 26]) (e : Reg) (he : e.val = r) =>
    hsame e (he ▸ hr)
  refine ⟨hpc, Quiet.of_sameCsr hcs h.quiet, hcs.trans h.csr, (hsame 2 (by decide)).trans h.sp,
    (hsame 18 (by decide)).trans h.len, (hsame 19 (by decide)).trans h.self, (hsame 20 (by decide)).trans h.buf,
    hs7, ha0, ?_, (hsame 25 (by decide)).trans h.s9, (hsame 26 (by decide)).trans h.s10, ?_, ?_, ?_, ?_, ?_, ?_,
    hfd, fun x hx => (hram x hx).trans (h.ram x hx)⟩
  · rw [hsame 24 (by decide), hsame 8 (by decide)]; exact h.s8
  · intro r hr
    have : r.val ∈ [0, 2, 3, 4, 8, 18, 19, 20, 24, 25, 26] := by
      simp only [nkept, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega
    exact (hsame r this).trans (h.kept r hr)
  · rw [hsame 8 (by decide)]; exact hcur
  · rw [hsame 8 (by decide)]; exact h.fle
  · intro o r hm
    rw [← h.slots o r hm]
    have ho : 0xc ≤ o ∧ o + 4 ≤ 0x40 := by
      simp only [nslots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
        ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
    have eg := ng_toNat c hE
    have hsp := hE.sp
    have eo : (ng c + BitVec.ofNat 32 o).toNat = (ng c).toNat + o := add_toNat _ _ (by omega)
    exact rd_congr _ (by omega) fun x h1 h2 => hsl x (by omega) (by omega)
  · exact hfc
  · rw [hff, hsame 8 (by decide)]; exact h.ffil

/-! ## The end of the pending bytes -/

theorem end_case (c : Core) (R0 : Word → BitVec 8) (E : CallEnv nextPc nextStack ⟨c, R0⟩)
    (d : Core) (M : Word → BitVec 8) (h : LoopInv c R0 d M) (heq : d.get 9 = d.get 8) :
    ∃ k m, QRun B img k ⟨d, M⟩ m ∧ NextPost ⟨c, R0⟩ m := by
  have r := nend d M h.pc h.quiet (by simp [taken, heq])
  have gs : ∀ r : Reg, r ≠ 9 → (nendCore d M).get r = d.get r := fun r hr => by
    simp [nendCore, Core.wr_get_ne, hr]
  have cs : (nendCore d M).sameCsr d := by unfold nendCore; csr_chain
  obtain ⟨k, m, r2, post⟩ := exit_post c R0 E (nendCore d M) M
    ⟨rfl, Quiet.of_sameCsr cs h.quiet, cs.trans h.csr, (gs 2 (by decide)).trans h.sp,
      fun r hr => (gs r (fun e => by subst e; exact absurd hr (by decide))).trans (h.kept r hr), h.slots,
      (gs 18 (by decide)).trans h.len, (gs 19 (by decide)).trans h.self,
      by rw [gs 23 (by decide)]; exact h.s7, by rw [gs 8 (by decide)]; exact h.fle,
      by rw [gs 8 (by decide), h.fcur]; exact h.curle, by rw [gs 8 (by decide)]; exact h.ffil,
      by rw [gs 23 (by decide)]; exact h.fdisc, h.ram⟩
  exact ⟨_, m, r.trans r2, post⟩

/-! ## The delimiter scan -/

/-- A delimiter found at cursor + j: the core at 0x8001d49a after the scan from the loop core d. -/
structure FoundAt (c : Core) (d e : Core) (M : Word → BitVec 8) (j : Nat) : Prop where
  pc : e.pc = 0x8001d49a
  quiet : Quiet e
  csr : e.sameCsr d
  same : ∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → e.get r = d.get r
  a2 : e.get 12 = 0 - BitVec.ofNat 32 j
  a1 : e.get 11 = c.get 11 + d.get 9
  jlt : j < (d.get 8 - d.get 9).toNat
  zero : M (c.get 11 + BitVec.ofNat 32 j + d.get 9) = 0

theorem scan_case (c : Core) (R0 : Word → BitVec 8) (E : CallEnv nextPc nextStack ⟨c, R0⟩)
    (d : Core) (M : Word → BitVec 8) (h : LoopInv c R0 d M) (hne : d.get 9 ≠ d.get 8) :
    (∃ k m, QRun B img k ⟨d, M⟩ m ∧ NextPost ⟨c, R0⟩ m) ∨
    (∃ k e j, QRun B img k ⟨d, M⟩ ⟨e, M⟩ ∧ FoundAt c d e M j) := by
  have hE := envNat c R0 E
  have hb := hE.buf
  have hcl := h.curle
  have hfl := h.fle
  have r1 := nhead d M h.pc h.quiet (by simp only [taken, beq_eq_false_iff_ne]; exact hne)
  let e0 := nheadCore d M
  have cs0 : e0.sameCsr d := by unfold e0 nheadCore; csr_chain
  have g0 : ∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → e0.get r = d.get r := fun r a b c' d' => by
    simp [e0, nheadCore, Core.wr_get_ne, a, b, c', d']
  let n := (d.get 8 - d.get 9).toNat
  have hn : n = (d.get 8).toNat - (d.get 9).toNat := sub_toNat _ _ hcl
  have hpos : 0 < n := by
    have : (d.get 9).toNat ≠ (d.get 8).toNat := fun e => hne (BitVec.eq_of_toNat_eq e)
    omega
  have hin : ∀ t, t < n → B.inRam (c.get 11 + BitVec.ofNat 32 t + d.get 9) 1 = true := by
    intro t ht
    have e1 : (c.get 11 + BitVec.ofNat 32 t).toNat = (c.get 11).toNat + t := add_toNat _ _ (by omega)
    have e2 : (c.get 11 + BitVec.ofNat 32 t + d.get 9).toNat = (c.get 11).toNat + t + (d.get 9).toNat :=
      by rw [add_toNat' _ _ (by omega), e1]
    rw [B_ram, e2]; omega
  obtain ⟨s, e', hr, hcs, hfr, hres⟩ := scan M (d.get 8) (d.get 9) (c.get 11) n rfl hin n 0 e0 (by omega) hpos
    rfl (Quiet.of_sameCsr cs0 h.quiet) (g0 9 (by decide) (by decide) (by decide) (by decide))
    (by simp [e0, nheadCore, Core.wr_get_ne, Core.wr_get_self, h.s8]; rfl)
    (by simp [e0, nheadCore, Core.wr_get_ne, Core.wr_get_self, alu_add])
    (by simp [e0, nheadCore, Core.wr_get_ne, Core.wr_get_self, alu_add, h.buf])
  have ge : ∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → e'.get r = d.get r :=
    fun r a b c' d' f' => (hfr r b d' f').trans (g0 r a b c' d')
  rcases hres with ⟨j, -, hj, hz, hpc', h12⟩ | ⟨-, hpc'⟩
  · refine .inr ⟨_, e', j, r1.trans hr, hpc', Quiet.of_sameCsr (hcs.trans cs0) h.quiet, hcs.trans cs0, ge, h12,
      ?_, hj, hz⟩
    rw [hfr 11 (by decide) (by decide) (by decide)]
    simp [e0, nheadCore, Core.wr_get_ne, Core.wr_get_self, alu_add, h.buf]
  · left
    obtain ⟨k, m, r2, post⟩ := exit_post c R0 E e' M
      ⟨hpc', Quiet.of_sameCsr (hcs.trans cs0) h.quiet, (hcs.trans cs0).trans h.csr,
        (ge 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.sp,
        fun r hr => (ge r (fun e => by subst e; exact absurd hr (by decide)) (fun e => by subst e; exact absurd hr (by decide))
          (fun e => by subst e; exact absurd hr (by decide)) (fun e => by subst e; exact absurd hr (by decide))
          (fun e => by subst e; exact absurd hr (by decide))).trans (h.kept r hr), h.slots,
        (ge 18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.len,
        (ge 19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.self,
        by rw [ge 23 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.s7,
        by rw [ge 8 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.fle,
        by rw [ge 8 (by decide) (by decide) (by decide) (by decide) (by decide), h.fcur]; exact h.curle,
        by rw [ge 8 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.ffil,
        by rw [ge 23 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.fdisc, h.ram⟩
    exact ⟨_, m, (r1.trans hr).trans r2, post⟩

/-! ## A delimiter found while discarding -/

theorem s11_toNat (cur : Word) (j : Nat) (h : cur.toNat + j + 1 < 2 ^ 32) :
    (alu .add (alu .sub cur (0 - BitVec.ofNat 32 j)) 0x00000001#32).toNat = cur.toNat + j + 1 := by
  simp only [alu_add, alu_sub]; bv_omega

theorem disc_case (c : Core) (R0 : Word → BitVec 8) (E : CallEnv nextPc nextStack ⟨c, R0⟩)
    (d : Core) (M : Word → BitVec 8) (h : LoopInv c R0 d M) (e : Core) (j : Nat) (hf : FoundAt c d e M j)
    (h1 : d.get 23 = 1) :
    ∃ k d' M', QRun B img k ⟨e, M⟩ ⟨d', M'⟩ ∧ LoopInv c R0 d' M' ∧
      (d'.get 8).toNat - (d'.get 9).toNat < (d.get 8).toNat - (d.get 9).toNat := by
  have hE := envNat c R0 E
  have hp := hE.self
  have hcl := h.curle
  have hfl := h.fle
  have hj := hf.jlt
  rw [sub_toNat _ _ hcl] at hj
  have e19 : e.get 19 = c.get 10 := (hf.same 19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.self
  have e9 : e.get 9 = d.get 9 := hf.same 9 (by decide) (by decide) (by decide) (by decide) (by decide)
  have e8 : e.get 8 = d.get 8 := hf.same 8 (by decide) (by decide) (by decide) (by decide) (by decide)
  have e10 : e.get 10 = 1 := by
    rw [hf.same 10 (by decide) (by decide) (by decide) (by decide) (by decide), h.a0, h1]
  have hs11 := s11_toNat (d.get 9) j (by omega)
  have e8a : (c.get 10 + 0x00000008#32).toNat = (c.get 10).toNat + 8 := add_toNat _ 8 (by omega)
  have r := ndisc e M hf.pc hf.quiet (by rw [e19]; exact E.selfAl) (by rw [e19, B_ram]; omega)
    (by rw [e10]; rfl) (Nat.mod_one _) (by rw [e19, B_ram, e8a]; omega)
    (by rw [e8, e9, hf.a2]; simp only [taken, BitVec.ult, Bool.not_eq_true', decide_eq_false_iff_not]; omega)
  let s11 := alu .add (alu .sub (d.get 9) (0 - BitVec.ofNat 32 j)) 0x00000001#32
  let d' := ndiscCore e M
  let M' := ndiscRam e M
  have cs : d'.sameCsr e := by unfold d' ndiscCore; csr_chain
  have gd : ∀ r : Reg, r ≠ 9 → r ≠ 10 → r ≠ 21 → r ≠ 23 → r ≠ 27 → d'.get r = e.get r := fun r a b c' d'' f' => by
    simp [d', ndiscCore, Core.wr_get_ne, a, b, c', d'', f']
  have d9 : d'.get 9 = s11 := by
    simp [d', ndiscCore, Core.wr_get_ne, Core.wr_get_self, alu_add, e9, hf.a2, s11]
  have d23 : d'.get 23 = 0 := by simp [d', ndiscCore, Core.wr_get_ne, Core.wr_get_self, alu_add]
  have d10 : d'.get 10 = 0 := by simp [d', ndiscCore, Core.wr_get_ne, Core.wr_get_self, alu_add]
  have eM' : M' = ramWrite (ramWrite M (c.get 10) s11 .w) (c.get 10 + 0x00000008#32) 0 .b := by
    simp only [M', ndiscRam, e19, e9, hf.a2, s11]
  have mo : ∀ x : Word, (x.toNat < (c.get 10).toNat ∨ (c.get 10).toNat + 12 ≤ x.toNat) → M' x = M x := by
    intro x hx
    rw [eM', ramWrite, ramPut_ne _ (fun he => by rw [he, e8a] at hx; omega), wr_byte_other _ _ _ _ (by omega) (by omega)]
  refine ⟨_, d', M', r, ?_, ?_⟩
  · refine loopInv_next c R0 hE d M h d' M' rfl (cs.trans hf.csr) ?_ (by rw [d23]; decide) (by rw [d10, d23])
      (by rw [d9, hs11]; omega) (fun x h1 h2 => mo x (.inr (by have := hE.sepS; omega))) ?_ ?_ ?_ ?_
    · intro r hr
      have : r ≠ 9 ∧ r ≠ 10 ∧ r ≠ 21 ∧ r ≠ 23 ∧ r ≠ 27 ∧ r ≠ 11 ∧ r ≠ 12 ∧ r ≠ 13 ∧ r ≠ 14 ∧ r ≠ 15 := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> subst e <;> exact absurd hr (by decide)
      obtain ⟨a, b, c', d'', f', g', h', i', j', k'⟩ := this
      rw [gd r a b c' d'' f']; exact hf.same r g' h' i' j' k'
    · rw [eM', d9]
      rw [rd_congr (c.get 10) (by omega) (ram' := ramWrite (ramWrite M (c.get 10) s11 .w) (c.get 10 + 0x00000008#32) 0 .b)
        (ram := ramWrite M (c.get 10) s11 .w) fun x h1 h2 => by
          rw [ramWrite, ramPut_ne _ (fun he => by rw [he, e8a] at h2; omega)], ramRead_ramWrite_w]
    · have e4 : (c.get 10 + 4).toNat = (c.get 10).toNat + 4 := add_toNat _ 4 (by omega)
      apply rd_congr _ (by omega)
      intro x h1 h2
      rw [eM', ramWrite, ramPut_ne _ (fun he => by rw [he, e8a] at h2; omega),
        wr_byte_other _ _ _ _ (by omega) (by omega)]
    · rw [eM', d23, ramWrite, show (c.get 10 + 8 : Word) = c.get 10 + 0x00000008#32 from rfl, ramPut_eq]; rfl
    · intro x hx
      exact mo x (by have := hx.1; omega)
  · rw [gd 8 (by decide) (by decide) (by decide) (by decide) (by decide), e8, d9, hs11]; omega

end E5R.Rmk.Deframer.Next
