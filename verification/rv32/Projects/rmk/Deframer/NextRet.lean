/-
  `Deframer::next`: from the shared return block 0x8001d510 to `NextPost`.

  Original e5r code, Apache-2.0.

  PROVED here: `ret_post`: a core at 0x8001d510 with next's frame intact (the 13 save slots, sp,
  x0/gp/tp), a0 ∈ {0, 1}, a Some length (s6) in (2, len], and the deframer invariant in RAM,
  returns (the generated epilogue `nepi`) to a machine meeting `NextPost`.
-/
import Projects.rmk.Deframer.NextInv

set_option maxRecDepth 100000

namespace E5R.Rmk.Deframer.Next
open E5R E5R.Rmk.NextFetch E5R.Rmk.Deframer.Tail

/-- The return-block state of `next` relative to its entry machine `⟨c, R0⟩`. -/
structure RetAt (c : Core) (R0 : Word → BitVec 8) (e : Core) (M : Word → BitVec 8) : Prop where
  pc : e.pc = 0x8001d510
  quiet : Quiet e
  csr : e.sameCsr c
  sp : e.get 2 = ng c
  kept : ∀ r : Reg, r.val ∈ nkept → e.get r = c.get r
  slots : NSlots c M
  tag : (e.get 10).toNat ≤ 1
  val : (e.get 10).toNat = 1 → 2 < (e.get 22).toNat ∧ (e.get 22).toNat ≤ (c.get 12).toNat
  inv : Inv M (c.get 10) (c.get 12).toNat
  disc : discarding M (c.get 10) ≤ 1
  ram : ∀ x, Outside (c.get 10) (c.get 11) (c.get 12).toNat (c.get 2) nextStack x → M x = R0 x

theorem nepi_sameCsr (e M) : (nepiCore e M).sameCsr e := by
  unfold nepiCore
  repeat (first | exact Core.sameCsr_wr _ _ _ _ | refine (Core.sameCsr_goto _ _).trans ?_ | refine (Core.sameCsr_wr _ _ _ _).trans ?_)

theorem ng_add (c : Core) : ng c + 0x00000040#32 = c.get 2 := by unfold ng; bv_omega

theorem ret_post (c : Core) (R0 : Word → BitVec 8) (E : CallEnv nextPc nextStack ⟨c, R0⟩)
    (e : Core) (M : Word → BitVec 8) (h : RetAt c R0 e M) :
    ∃ k m, QRun B img k ⟨e, M⟩ m ∧ NextPost ⟨c, R0⟩ m := by
  have hst := stack_nat (c.get 2) nextStack E.stack
  rw [show nextStack = 0x70 from rfl] at hst
  have hsp : (e.get 2).toNat % 4 = 0 := by rw [h.sp]; unfold ng; have := E.spAl; bv_omega
  have hs : 0x80029bc8 ≤ (e.get 2).toNat ∧ (e.get 2).toNat + 0x40 ≤ 0x81000000 := by
    rw [h.sp]; unfold ng; constructor <;> bv_omega
  have sl : ∀ o r, (o, r) ∈ nslots → ramRead M (e.get 2 + BitVec.ofNat 32 o) .w = c.get r := by
    intro o r hm; rw [h.sp]; exact h.slots o r hm
  have hra : (ramRead M (e.get 2 + 0x0000003c#32) .w).getLsbD 0 = false := by
    rw [sl 0x3c 1 (by simp [nslots])]; exact E.ra
  have run := nepi e M h.pc h.quiet
    (by bv_omega) (by rw [B_ram]; constructor <;> bv_omega)
    (by bv_omega) (by rw [B_ram]; constructor <;> bv_omega)
    (by bv_omega) (by rw [B_ram]; constructor <;> bv_omega)
    (by bv_omega) (by rw [B_ram]; constructor <;> bv_omega)
    (by bv_omega) (by rw [B_ram]; constructor <;> bv_omega)
    (by bv_omega) (by rw [B_ram]; constructor <;> bv_omega)
    (by bv_omega) (by rw [B_ram]; constructor <;> bv_omega)
    (by bv_omega) (by rw [B_ram]; constructor <;> bv_omega)
    (by bv_omega) (by rw [B_ram]; constructor <;> bv_omega)
    (by bv_omega) (by rw [B_ram]; constructor <;> bv_omega)
    (by bv_omega) (by rw [B_ram]; constructor <;> bv_omega)
    (by bv_omega) (by rw [B_ram]; constructor <;> bv_omega)
    (by bv_omega) (by rw [B_ram]; constructor <;> bv_omega)
    hra
  refine ⟨_, _, run, ?_⟩
  have hval := h.val
  have htag := h.tag
  have hinv := h.inv
  have hdisc := h.disc
  refine ⟨?_, (nepi_sameCsr _ _).trans h.csr, ?_, ?_, ?_, ?_, h.inv, h.disc, h.ram⟩
  · show (nepiCore e M).pc = c.get 1
    simp only [nepiCore, Core.goto_pc]; exact sl 0x3c 1 (by simp [nslots])
  · show (nepiCore e M).get 2 = c.get 2
    simp [nepiCore, Core.wr_get_ne, Core.wr_get_self, h.sp, alu_add]; exact ng_add c
  · intro r hr
    show (nepiCore e M).get r = c.get r
    have hr' : r.val ∈ [0, 1, 2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by
      have := r.isLt
      simp only [callerSaved, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega
    obtain ⟨k, hk⟩ := r
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · rfl
    · simp [nepiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x3c 1 (by simp [nslots])
    · simp [nepiCore, Core.wr_get_ne, Core.wr_get_self, h.sp, alu_add]; exact ng_add c
    · simp [nepiCore, Core.wr_get_ne]; exact h.kept 3 (by decide)
    · simp [nepiCore, Core.wr_get_ne]; exact h.kept 4 (by decide)
    · simp [nepiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x38 8 (by simp [nslots])
    · simp [nepiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x34 9 (by simp [nslots])
    · simp [nepiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x30 18 (by simp [nslots])
    · simp [nepiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x2c 19 (by simp [nslots])
    · simp [nepiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x28 20 (by simp [nslots])
    · simp [nepiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x24 21 (by simp [nslots])
    · simp [nepiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x20 22 (by simp [nslots])
    · simp [nepiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x1c 23 (by simp [nslots])
    · simp [nepiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x18 24 (by simp [nslots])
    · simp [nepiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x14 25 (by simp [nslots])
    · simp [nepiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x10 26 (by simp [nslots])
    · simp [nepiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0xc 27 (by simp [nslots])
  · show ((nepiCore e M).get 10).toNat ≤ 1
    simp [nepiCore, Core.wr_get_ne]; exact htag
  · intro h1
    have h1' : (e.get 10).toNat = 1 := by simpa [nepiCore, Core.wr_get_ne] using h1
    show 2 < ((nepiCore e M).get 11).toNat ∧ ((nepiCore e M).get 11).toNat ≤ (c.get 12).toNat
    simp [nepiCore, Core.wr_get_ne, Core.wr_get_self, alu_add]; exact hval h1'

end E5R.Rmk.Deframer.Next
