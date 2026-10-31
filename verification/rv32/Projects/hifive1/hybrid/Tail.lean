/-
  A machine-code summary of the Embassy channel's ring-tail update (the
  send side), in the emitted firmware (sampler task poll), for hybrid
  composition with the abstract-interpretation checker.

  Original e5r code, Apache-2.0.

  embassy-sync's `Channel<_, u8, 4>` send side, as rustc emitted it inside
  the sampler's poll, in a critical section (MIE cleared before this point):

    20010482 lw   a1,0x18(s1)  20010484 lw   a2,0x14(s1)  20010486 addi a3,a1,1
    2001048a addi a4,a3,-4     2001048e seqz a4,a4        20010492 addi a4,a4,-1
    20010494 and  a3,a3,a4     20010496 add  a1,a1,s1     20010498 sb   a0,0x1d(a1)
    2001049c sw   a3,0x18(s1)  -> 2001049e (bne a2,a3,...)

  `s1` is the channel, the tail word is at +0x18, the head word at +0x14,
  the four buffer bytes at +0x1d. The sample in `a0` is stored at
  `buf[tail]` and the tail advanced to `tail + 1` wrapped at 4, branch-free.
  The tail is read from RAM by the region itself, so the precondition is
  about the tail word in RAM (below 4), not about a register.

  The summary covers every machine of the run: each is masked (so no
  interrupt is enabled and the deterministic step is its only transition),
  no step faults or emits an event, the registers and RAM written are
  exactly those listed, and CSRs are unchanged. The instructions are
  checked against the flash image the checker uses (`Firmware.segments`).
-/
import Theories.Hybrid.Basic
import Theories.Hybrid.Wrap
import Theories.Board.Hifive1Revb
import Projects.hifive1.Image

set_option maxRecDepth 100000

namespace E5R.Hifive1.Hybrid.Tail
open E5R E5R.Hybrid

abbrev B := Hifive1Revb.board
abbrev img := Firmware.segments

def entry : Word := 0x20010482
def exit : Word := 0x2001049e

/-! ## The instructions (kernel-checked against the image) -/

theorem i0 : fetchDecode img 0x20010482 = some (.load .w true 11 9 0x18, 2) := by decide +kernel
theorem i1 : fetchDecode img 0x20010484 = some (.load .w true 12 9 0x14, 2) := by decide +kernel
theorem i2 : fetchDecode img 0x20010486 = some (.opimm .add 13 11 1, 4) := by decide +kernel
theorem i3 : fetchDecode img 0x2001048a = some (.opimm .add 14 13 0xfffffffc, 4) := by decide +kernel
theorem i4 : fetchDecode img 0x2001048e = some (.opimm .sltu 14 14 1, 4) := by decide +kernel
theorem i5 : fetchDecode img 0x20010492 = some (.opimm .add 14 14 0xffffffff, 2) := by decide +kernel
theorem i6 : fetchDecode img 0x20010494 = some (.op .and 13 13 14, 2) := by decide +kernel
theorem i7 : fetchDecode img 0x20010496 = some (.op .add 11 11 9, 2) := by decide +kernel
theorem i8 : fetchDecode img 0x20010498 = some (.store .b 11 10 0x1d, 4) := by decide +kernel
theorem i9 : fetchDecode img 0x2001049c = some (.store .w 9 13 0x18, 2) := by decide +kernel

/-! ## Contract -/

/-- The tail word of the channel at `s1` in `m`. -/
def tail (m : Machine) : Word := ramRead m.ram (m.core.get 9 + 0x18) .w

/-- What the summary needs at entry: an exact pc, MIE clear, the head and
    tail words aligned RAM, the tail below 4, and the buffer byte it
    indexes inside RAM. -/
structure Pre (m : Machine) : Prop where
  pc : m.core.pc = entry
  masked : m.core.mie_ = false
  headAligned : (m.core.get 9 + 0x14).toNat % 4 = 0
  headRam : B.inRam (m.core.get 9 + 0x14) 4 = true
  tailAligned : (m.core.get 9 + 0x18).toNat % 4 = 0
  tailRam : B.inRam (m.core.get 9 + 0x18) 4 = true
  tailLt : (tail m).toNat < 4
  bufRam : B.inRam (tail m + m.core.get 9 + 0x1d) 1 = true

/-- The wrap mask the region leaves in `a4`. -/
def mask (t : Word) : Word := alu .add (alu .sltu (t + 1 + 0xfffffffc) 1) 0xffffffff

/-- The exit machine, as a function of the entry machine. -/
structure Spec (m₀ m : Machine) : Prop where
  pc : m.core.pc = exit
  a1 : m.core.get 11 = tail m₀ + m₀.core.get 9
  a2 : m.core.get 12 = ramRead m₀.ram (m₀.core.get 9 + 0x14) .w
  a3 : m.core.get 13 = next (tail m₀)
  a4 : m.core.get 14 = mask (tail m₀)
  frame : ∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → m.core.get r = m₀.core.get r
  csr : m.core.sameCsr m₀.core
  ram : m.ram = ramWrite (ramWrite m₀.ram (tail m₀ + m₀.core.get 9 + 0x1d) (m₀.core.get 10) .b)
    (m₀.core.get 9 + 0x18) (next (tail m₀)) .w

theorem masked_of_sameCsr {c d : Core} (h : c.sameCsr d) (hd : d.mie_ = false) : c.mie_ = false := by
  have := congrArg (·.1) h; simp only [Core.ctl] at this; rw [this, hd]

/-- **The ring-tail summary**: from every machine satisfying `Pre`, a masked
    run of ten deterministic instructions ends in the machine `Spec`
    describes. -/
theorem contract (m₀ : Machine) (h : Pre m₀) : ∃ m, MRun B img 10 m₀ m ∧ Spec m₀ m := by
  obtain ⟨c₀, ram⟩ := m₀
  obtain ⟨hpc, hmask, hal14, hram14, hal18, hram18, htl, hbuf⟩ := h
  simp only [tail] at hpc hmask hal14 hram14 hal18 hram18 htl hbuf ⊢
  generalize hS : c₀.get 9 = S at hal14 hram14 hal18 hram18 htl hbuf
  generalize hT : ramRead ram (S + 0x18) .w = T at htl hbuf
  generalize hA : c₀.get 10 = A
  let H := ramRead ram (S + 0x14) .w
  let c1 := c₀.wr 11 T 0x20010484
  let c2 := c1.wr 12 H 0x20010486
  let c3 := c2.wr 13 (T + 1) 0x2001048a
  let c4 := c3.wr 14 (T + 1 + 0xfffffffc) 0x2001048e
  let c5 := c4.wr 14 (alu .sltu (T + 1 + 0xfffffffc) 1) 0x20010492
  let c6 := c5.wr 14 (mask T) 0x20010494
  let c7 := c6.wr 13 (next T) 0x20010496
  let c8 := c7.wr 11 (T + S) 0x20010498
  let c9 := c8.goto 0x2001049c
  let c10 := c9.goto exit
  let ram1 := ramWrite ram (T + S + 0x1d) A .b
  let ram2 := ramWrite ram1 (S + 0x18) (next T) .w
  have cs1 : c1.sameCsr c₀ := Core.sameCsr_wr _ _ _ _
  have cs2 : c2.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans cs1
  have cs3 : c3.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans cs2
  have cs4 : c4.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans cs3
  have cs5 : c5.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans cs4
  have cs6 : c6.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans cs5
  have cs7 : c7.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans cs6
  have cs8 : c8.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans cs7
  have cs9 : c9.sameCsr c₀ := (Core.sameCsr_goto _ _).trans cs8
  have cs10 : c10.sameCsr c₀ := (Core.sameCsr_goto _ _).trans cs9
  have s0 : DetStep B img ⟨c₀, ram⟩ ⟨c1, ram⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact i0) fun o => ?_
    rw [exec_load, hS, interp_load_ram o hal18 hram18, hT, hpc]; rfl
  have s1 : DetStep B img ⟨c1, ram⟩ ⟨c2, ram⟩ := by
    refine detStep_of (by show (0x20010484 : Word).getLsbD 0 = false; decide) i1 fun o => ?_
    rw [exec_load]
    have : c1.get 9 = S := by simp [c1, Core.wr_get, hS]
    rw [this, interp_load_ram o hal14 hram14]; rfl
  have s2 : DetStep B img ⟨c2, ram⟩ ⟨c3, ram⟩ := by
    refine detStep_of (by show (0x20010486 : Word).getLsbD 0 = false; decide) i2 fun o => ?_
    rw [exec_opimm]
    have : c2.get 11 = T := by simp [c2, c1, Core.wr_get]
    simp only [alu, this]; rfl
  have s3 : DetStep B img ⟨c3, ram⟩ ⟨c4, ram⟩ := by
    refine detStep_of (by show (0x2001048a : Word).getLsbD 0 = false; decide) i3 fun o => ?_
    rw [exec_opimm]
    have : c3.get 13 = T + 1 := by simp [c3, Core.wr_get]
    simp only [alu, this]; rfl
  have s4 : DetStep B img ⟨c4, ram⟩ ⟨c5, ram⟩ := by
    refine detStep_of (by show (0x2001048e : Word).getLsbD 0 = false; decide) i4 fun o => ?_
    rw [exec_opimm]
    have : c4.get 14 = T + 1 + 0xfffffffc := by simp [c4, Core.wr_get]
    simp only [this]; rfl
  have s5 : DetStep B img ⟨c5, ram⟩ ⟨c6, ram⟩ := by
    refine detStep_of (by show (0x20010492 : Word).getLsbD 0 = false; decide) i5 fun o => ?_
    rw [exec_opimm]
    have : c5.get 14 = alu .sltu (T + 1 + 0xfffffffc) 1 := by simp [c5, Core.wr_get]
    simp only [this]; rfl
  have s6 : DetStep B img ⟨c6, ram⟩ ⟨c7, ram⟩ := by
    refine detStep_of (by show (0x20010494 : Word).getLsbD 0 = false; decide) i6 fun o => ?_
    rw [exec_op]
    have e13 : c6.get 13 = T + 1 := by simp [c6, c5, c4, c3, Core.wr_get]
    have e14 : c6.get 14 = mask T := by simp [c6, Core.wr_get]
    rw [e13, e14, mask, wrap' htl]; rfl
  have s7 : DetStep B img ⟨c7, ram⟩ ⟨c8, ram⟩ := by
    refine detStep_of (by show (0x20010496 : Word).getLsbD 0 = false; decide) i7 fun o => ?_
    rw [exec_op]
    have e11 : c7.get 11 = T := by simp [c7, c6, c5, c4, c3, c2, c1, Core.wr_get]
    have e9 : c7.get 9 = S := by simp [c7, c6, c5, c4, c3, c2, c1, Core.wr_get, hS]
    simp only [alu, e11, e9]; rfl
  have s8 : DetStep B img ⟨c8, ram⟩ ⟨c9, ram1⟩ := by
    refine detStep_of (by show (0x20010498 : Word).getLsbD 0 = false; decide) i8 fun o => ?_
    rw [exec_store]
    have e11 : c8.get 11 = T + S := by simp [c8, Core.wr_get]
    have e10 : c8.get 10 = A := by simp [c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get, hA]
    rw [e11, e10, interp_store_ram o (by simp only [Width.bytes, Nat.mod_one]) hbuf]
    rfl
  have s9 : DetStep B img ⟨c9, ram1⟩ ⟨c10, ram2⟩ := by
    refine detStep_of (by show (0x2001049c : Word).getLsbD 0 = false; decide) i9 fun o => ?_
    rw [exec_store]
    have e9 : c9.get 9 = S := by simp [c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get, hS]
    have e13 : c9.get 13 = next T := by simp [c9, c8, c7, Core.wr_get]
    rw [e9, e13, interp_store_ram o hal18 hram18]
    rfl
  have mk : ∀ c (r : Word → BitVec 8), c.sameCsr c₀ → Masked ⟨c, r⟩ :=
    fun c _ h => masked_of_sameCsr h hmask
  refine ⟨⟨c10, ram2⟩,
    .step hmask s0 (.step (mk _ _ cs1) s1 (.step (mk _ _ cs2) s2 (.step (mk _ _ cs3) s3
      (.step (mk _ _ cs4) s4 (.step (mk _ _ cs5) s5 (.step (mk _ _ cs6) s6
        (.step (mk _ _ cs7) s7 (.step (mk _ _ cs8) s8 (.single (mk _ _ cs9) s9))))))))), ?_⟩
  have et : tail ⟨c₀, ram⟩ = T := by simp only [tail]; rw [hS, hT]
  refine ⟨rfl, ?a1, ?a2, ?a3, ?a4, ?fr, cs10, ?rm⟩
  case a1 => rw [et, hS]; simp [c10, c9, c8, Core.wr_get]
  case a2 => rw [hS]; simp [c10, c9, c8, c7, c6, c5, c4, c3, c2, Core.wr_get, H]
  case a3 => rw [et]; simp [c10, c9, c8, c7, Core.wr_get]
  case a4 => rw [et]; simp [c10, c9, c8, c7, c6, Core.wr_get]
  case fr =>
    intro r a b d e
    by_cases hr : r = 0
    · subst hr; simp [Core.get]
    · simp [c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get, a, b, d, e, hr]
  case rm => show ram2 = _; rw [et, hS, hA]

/-- The summary, in the form `Hybrid.hybrid_sound` takes. -/
def summary : Summary B img where
  Pre := Pre
  Post m := ∃ m₀, Pre m₀ ∧ Spec m₀ m
  run m h := let ⟨m', hr, hs⟩ := contract m h; ⟨9, m', hr, m, h, hs⟩

/-- The stored tail stays below the capacity. -/
theorem post_tail_lt {m₀ m : Machine} (h : Pre m₀) (hs : Spec m₀ m) : (m.core.get 13).toNat < 4 := by
  rw [hs.a3]; exact next_lt h.tailLt

end E5R.Hifive1.Hybrid.Tail
