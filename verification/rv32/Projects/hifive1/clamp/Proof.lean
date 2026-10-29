/-
  The V0 clamp, recompiled for the HiFive1 memory map, proved for every
  32-bit input rather than every byte.

    let input = read_volatile(0x8000_0000 as *const u32);
    let output = input.wrapping_add(7).min(100);
    write_volatile(0x8000_0004 as *mut u32, output);

  rustc 1.98.1 emits the same bytes at opt-level 1, 2 and s. The theorem
  covers every boot state with the pc at the entry point (all registers,
  CSRs and RAM arbitrary), so the input is any word. The specification is
  the source expression, wrapping included: for inputs within 7 of 2^32 the
  sum wraps and the binary stores the small wrapped value, which `wraps`
  exhibits. A non-wrapping reading of the source would be false of this
  binary.
-/
import Theories.Logic
import Theories.Board.Hifive1Revb
import Projects.hifive1.clamp.Image

set_option maxRecDepth 100000

namespace E5R.Hifive1.Clamp
open E5R

abbrev B := Hifive1Revb.board
abbrev img := Clamp32.segments

def inAddr : Word := 0x80000000
def outAddr : Word := 0x80000004
def donePc : Word := 0x2001001e

/-- `input.wrapping_add(7).min(100)`. -/
def spec (n : Word) : Word := if (n + 7).ult 100 then n + 7 else 100

theorem spec_toNat (n : Word) : (spec n).toNat = min ((n.toNat + 7) % 2^32) 100 := by
  unfold spec
  split <;> rename_i h <;> simp [BitVec.ult, BitVec.toNat_add] at h ⊢ <;> omega

/-- The wrapping case is real behavior of the binary, not an artifact. -/
theorem wraps : spec 0xfffffffa = 1 := by decide

theorem i0 : fetchDecode img 0x20010000 = some (.lui 10 0x80000000, 4) := by decide +kernel
theorem i1 : fetchDecode img 0x20010004 = some (.load .w true 11 10 0, 2) := by decide +kernel
theorem i2 : fetchDecode img 0x20010006 = some (.opimm .add 11 11 7, 2) := by decide +kernel
theorem i3 : fetchDecode img 0x20010008 = some (.opimm .add 12 0 100, 4) := by decide +kernel
theorem i4 : fetchDecode img 0x2001000c = some (.branch .ltu 11 12 8, 4) := by decide +kernel
theorem i5 : fetchDecode img 0x20010010 = some (.opimm .add 11 0 100, 4) := by decide +kernel
theorem i6 : fetchDecode img 0x20010014 = some (.store .w 10 11 4, 2) := by decide +kernel
theorem i7 : fetchDecode img 0x20010016 = some (.auipc 1 0, 4) := by decide +kernel
theorem i8 : fetchDecode img 0x2001001a = some (.jalr 1 1 8, 4) := by decide +kernel
/-- The endpoint is the idle loop `j .`. -/
theorem idle : fetchDecode img 0x2001001e = some (.jal 0 0, 4) := by decide +kernel

/-- What the run guarantees. -/
structure Post (c₀ : Core) (ram : Word → BitVec 8) (m : Machine) : Prop where
  pc : m.core.pc = donePc
  out : ramRead m.ram outAddr .w = spec (ramRead ram inAddr .w)
  frame : ∀ x, (∀ k < 4, x ≠ outAddr + BitVec.ofNat 32 k) → m.ram x = ram x
  csr : m.core.sameCsr c₀

theorem clamp_all (c₀ : Core) (ram : Word → BitVec 8) (hpc : c₀.pc = 0x20010000) :
    ∃ n m, DetSteps B img n ⟨c₀, ram⟩ m ∧ Post c₀ ram m := by
  let n := ramRead ram inAddr .w
  have s0 : DetStep B img ⟨c₀, ram⟩ ⟨c₀.wr 10 0x80000000 0x20010004, ram⟩ :=
    detStep_of (B := B) (by rw [hpc]; decide) (by rw [hpc]; exact i0)
      fun o => by rw [exec_lui, hpc]; rfl
  generalize hc1 : c₀.wr 10 0x80000000 0x20010004 = c1 at s0
  have a1 : c1.get 10 = 0x80000000 := by rw [← hc1, Core.wr_get_self _ _ _ _ (by decide)]
  have s1 : DetStep B img ⟨c1, ram⟩ ⟨c1.wr 11 n 0x20010006, ram⟩ := by
    refine detStep_of (B := B) (by rw [← hc1]; simp only [Core.wr_pc]; decide) (by rw [← hc1]; exact i1) fun o => ?_
    rw [exec_load, a1, interp_load_ram o (by decide) (by decide)]
    simp [extend, n, inAddr, ← hc1]
  generalize hc2 : c1.wr 11 n 0x20010006 = c2 at s1
  have s2 : DetStep B img ⟨c2, ram⟩ ⟨c2.wr 11 (n + 7) 0x20010008, ram⟩ := by
    refine detStep_of (B := B) (by rw [← hc2]; simp only [Core.wr_pc]; decide) (by rw [← hc2]; exact i2) fun o => ?_
    rw [exec_opimm, ← hc2, Core.wr_get_self _ _ _ _ (by decide)]; rfl
  generalize hc3 : c2.wr 11 (n + 7) 0x20010008 = c3 at s2
  have s3 : DetStep B img ⟨c3, ram⟩ ⟨c3.wr 12 100 0x2001000c, ram⟩ := by
    refine detStep_of (B := B) (by rw [← hc3]; simp only [Core.wr_pc]; decide) (by rw [← hc3]; exact i3) fun o => ?_
    rw [exec_opimm]; simp [alu, ← hc3]
  generalize hc4 : c3.wr 12 100 0x2001000c = c4 at s3
  have r11 : c4.get 11 = n + 7 := by
    rw [← hc4, Core.wr_get_ne _ _ _ _ _ (by decide), ← hc3, Core.wr_get_self _ _ _ _ (by decide)]
  have r12 : c4.get 12 = 100 := by rw [← hc4, Core.wr_get_self _ _ _ _ (by decide)]
  have r10 : c4.get 10 = 0x80000000 := by
    rw [← hc4, Core.wr_get_ne _ _ _ _ _ (by decide), ← hc3, Core.wr_get_ne _ _ _ _ _ (by decide),
      ← hc2, Core.wr_get_ne _ _ _ _ _ (by decide), a1]
  have p4 : c4.pc = 0x2001000c := by rw [← hc4]; rfl
  -- Both sides of the branch meet at the store with a1 = spec n.
  have br : ∃ c5 : Core, ∃ k, DetSteps B img k ⟨c4, ram⟩ ⟨c5, ram⟩ ∧ c5.pc = 0x20010014 ∧
      c5.get 11 = spec n ∧ c5.get 10 = 0x80000000 ∧ c5.sameCsr c4 := by
    by_cases h : (n + 7).ult 100
    · refine ⟨c4.goto 0x20010014, 1, .single ?_, rfl, ?_, by simp [r10], Core.sameCsr_goto _ _⟩
      · refine detStep_of (B := B) (by rw [p4]; decide) (by rw [p4]; exact i4) fun o => ?_
        rw [exec_branch, if_pos (by simpa [taken, r11, r12] using h), p4, jump_ok _ _ (by decide)]
        rfl
      · simp only [Core.goto_get, r11]; unfold spec; rw [if_pos h]
    · refine ⟨(c4.goto 0x20010010).wr 11 100 0x20010014, 2,
        .step (m₁ := ⟨c4.goto 0x20010010, ram⟩) ?_ (.single ?_), rfl, ?_, ?_, ?_⟩
      · refine detStep_of (B := B) (by rw [p4]; decide) (by rw [p4]; exact i4) fun o => ?_
        rw [exec_branch, if_neg (by simpa [taken, r11, r12] using h), p4]; rfl
      · refine detStep_of (B := B) (by simp only [Core.goto_pc]; decide) i5 fun o => ?_
        rw [exec_opimm]; simp [alu]
      · rw [Core.wr_get_self _ _ _ _ (by decide)]; unfold spec; rw [if_neg h]
      · rw [Core.wr_get_ne _ _ _ _ _ (by decide)]; simp [r10]
      · exact (Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_goto _ _)
  obtain ⟨c5, k5, s5, p5, v5, a5, csr5⟩ := br
  let ram' := ramWrite ram outAddr (spec n) .w
  have s6 : DetStep B img ⟨c5, ram⟩ ⟨c5.goto 0x20010016, ram'⟩ := by
    refine detStep_of (B := B) (by rw [p5]; decide) (by rw [p5]; exact i6) fun o => ?_
    have ha : c5.get 10 + 4 = outAddr := by rw [a5]; rfl
    rw [exec_store, ha, v5, interp_store_ram o (by decide) (by decide), p5]; rfl
  have s7 : DetStep B img ⟨c5.goto 0x20010016, ram'⟩
      ⟨(c5.goto 0x20010016).wr 1 0x20010016 0x2001001a, ram'⟩ :=
    detStep_of (B := B) (by simp only [Core.wr_pc, Core.goto_pc]; decide) i7 fun o => by rw [exec_auipc]; rfl
  have s8 : DetStep B img ⟨(c5.goto 0x20010016).wr 1 0x20010016 0x2001001a, ram'⟩
      ⟨((c5.goto 0x20010016).wr 1 0x20010016 0x2001001a).set 1 0x2001001e |>.goto donePc, ram'⟩ := by
    refine detStep_of (B := B) (by simp only [Core.wr_pc, Core.goto_pc]; decide) i8 fun o => ?_
    rw [exec_jalr, Core.wr_get_self _ _ _ _ (by decide), jump_ok _ _ (by decide)]; rfl
  refine ⟨_, _, ((((((DetSteps.single s0).trans (.single s1)).trans (.single s2)).trans
    (.single s3)).trans s5).trans ((DetSteps.single s6).trans ((DetSteps.single s7).trans
    (.single s8)))), ?_⟩
  refine ⟨rfl, ramRead_ramWrite_w _ _ _, fun x hx => ramWrite_w_other _ _ _ _ hx, ?_⟩
  -- Only registers changed: every CSR and the reservation are as at boot.
  have : ((((c5.goto 0x20010016).wr 1 0x20010016 0x2001001a).set 1 0x2001001e).goto donePc).sameCsr c5 :=
    (Core.sameCsr_goto _ _).trans ((Core.sameCsr_set (Core.sameCsr_wr _ _ _ _) _ _).trans
      (Core.sameCsr_goto _ _))
  refine this.trans (csr5.trans ?_)
  rw [← hc4, ← hc3, ← hc2, ← hc1]
  exact (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
    ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_wr _ _ _ _)))

#print axioms clamp_all
#print axioms spec_toNat

/-! ## Nonvacuity

A concrete boot state whose input word is 0xfffffffa really reaches the idle
loop with the wrapped result 1 stored. -/

def demo : Core :=
  { pc := 0x20010000, x := fun _ => 0, mie_ := false, mpie := false, mpp := 3, mieReg := 0,
    mtvec := 0, mepc := 0, mcause := 0, mscratch := 0, resv := false }

/-- RAM holding 0xfffffffa at the input word, zero elsewhere. -/
def demoRam : Word → BitVec 8 := fun a =>
  if a = 0x80000000 then 0xfa else if a = 0x80000001 ∨ a = 0x80000002 ∨ a = 0x80000003 then 0xff else 0

theorem nonvacuous : ∃ n m, DetSteps B img n ⟨demo, demoRam⟩ m ∧ m.core.pc = donePc ∧
    ramRead m.ram outAddr .w = 1 := by
  obtain ⟨n, m, h, post⟩ := clamp_all demo demoRam rfl
  refine ⟨n, m, h, post.pc, ?_⟩
  rw [post.out]; decide

end E5R.Hifive1.Clamp
