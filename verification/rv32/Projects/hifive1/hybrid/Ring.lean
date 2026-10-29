/-
  A machine-code summary of the Embassy channel's ring-head update, in the
  emitted firmware (actuator task poll), for hybrid composition with the
  abstract-interpretation checker.

  Original e5r code, Apache-2.0.

  embassy-sync's `Channel<_, u8, 4>` receive side, as rustc emitted it inside
  `TaskStorage<actuator>::poll`, in a critical section (`csrrci a0, mstatus, 8`
  at 0x20010638 cleared MIE before this point):

    20010698 addi a2,a0,1      2001069c add  a0,a0,s1     2001069e addi a3,a2,-4
    200106a2 lbu  a1,0x1d(a0)  200106a6 seqz a0,a3        200106aa addi a0,a0,-1
    200106ac and  a0,a0,a2     200106ae sw   a0,0x14(s1)  -> 200106b0

  `a0` holds the ring head (loaded from 0x14(s1)), `s1` the channel. The
  new head is `head + 1` masked by `seqz(head + 1 - 4) - 1`, i.e. wrapped
  to 0 at 4, without a branch. A non-relational abstract domain loses the
  link between `a2` and `a3` here and cannot bound the stored head; this
  summary proves it, for every head below 4.

  The summary covers every machine of the run: each is masked (so no
  interrupt is enabled and the deterministic step is its only transition),
  no step faults or emits an event, the registers and RAM written are
  exactly those listed, and CSRs are unchanged. The instructions are
  checked against the flash image the checker uses (`Firmware.segments`).
-/
import Theories.Hybrid.Basic
import Theories.Board.Hifive1Revb
import Projects.hifive1.Image

set_option maxRecDepth 100000

namespace E5R.Hifive1.Hybrid.Ring
open E5R E5R.Hybrid

abbrev B := Hifive1Revb.board
abbrev img := Firmware.segments

def entry : Word := 0x20010698
def exit : Word := 0x200106b0

/-! ## The instructions (kernel-checked against the image) -/

theorem i0 : fetchDecode img 0x20010698 = some (.opimm .add 12 10 1, 4) := by decide +kernel
theorem i1 : fetchDecode img 0x2001069c = some (.op .add 10 10 9, 2) := by decide +kernel
theorem i2 : fetchDecode img 0x2001069e = some (.opimm .add 13 12 0xfffffffc, 4) := by decide +kernel
theorem i3 : fetchDecode img 0x200106a2 = some (.load .b false 11 10 0x1d, 4) := by decide +kernel
theorem i4 : fetchDecode img 0x200106a6 = some (.opimm .sltu 10 13 1, 4) := by decide +kernel
theorem i5 : fetchDecode img 0x200106aa = some (.opimm .add 10 10 0xffffffff, 2) := by decide +kernel
theorem i6 : fetchDecode img 0x200106ac = some (.op .and 10 10 12, 2) := by decide +kernel
theorem i7 : fetchDecode img 0x200106ae = some (.store .w 9 10 0x14, 2) := by decide +kernel

/-! ## Contract -/

/-- The ring head after one receive: `head + 1`, wrapped at the capacity 4. -/
def next (h : Word) : Word := if h = 3 then 0 else h + 1

theorem next_lt {h : Word} (hh : h.toNat < 4) : (next h).toNat < 4 := by
  unfold next; split
  · simp
  · rename_i hn
    have : h.toNat ≠ 3 := fun e => hn (BitVec.eq_of_toNat_eq (by simp [e]))
    rw [BitVec.toNat_add]; simp; omega

/-- The branch-free wrap the compiler emitted computes `next`. -/
theorem wrap {h : Word} (hh : h.toNat < 4) :
    alu .and (alu .add (alu .sltu (h + 1 + 0xfffffffc) 1) 0xffffffff) (h + 1) = next h := by
  have : h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 := by
    have e : h = BitVec.ofNat 32 h.toNat := by simp
    rcases (by omega : h.toNat = 0 ∨ h.toNat = 1 ∨ h.toNat = 2 ∨ h.toNat = 3) with k | k | k | k <;>
      rw [k] at e <;> simp [e]
  rcases this with rfl | rfl | rfl | rfl <;> decide

/-- What the summary needs at entry. Everything is checkable on an abstract
    state: an exact pc, the head below 4, MIE clear, and the two RAM
    accesses inside RAM (the head word aligned). -/
structure Pre (m : Machine) : Prop where
  pc : m.core.pc = entry
  head : (m.core.get 10).toNat < 4
  masked : m.core.mie_ = false
  cellAligned : (m.core.get 9 + 0x14).toNat % 4 = 0
  cellRam : B.inRam (m.core.get 9 + 0x14) 4 = true
  bufRam : B.inRam (m.core.get 10 + m.core.get 9 + 0x1d) 1 = true

/-- The exit machine, as a function of the entry machine. -/
structure Spec (m₀ m : Machine) : Prop where
  pc : m.core.pc = exit
  head : m.core.get 10 = next (m₀.core.get 10)
  byte : m.core.get 11 = extend .b false (ramRead m₀.ram (m₀.core.get 10 + m₀.core.get 9 + 0x1d) .b)
  a2 : m.core.get 12 = m₀.core.get 10 + 1
  a3 : m.core.get 13 = m₀.core.get 10 + 1 + 0xfffffffc
  frame : ∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → m.core.get r = m₀.core.get r
  csr : m.core.sameCsr m₀.core
  ram : m.ram = ramWrite m₀.ram (m₀.core.get 9 + 0x14) (next (m₀.core.get 10)) .w

theorem masked_of_sameCsr {c d : Core} (h : c.sameCsr d) (hd : d.mie_ = false) : c.mie_ = false := by
  have := congrArg (·.1) h; simp only [Core.ctl] at this; rw [this, hd]

/-- **The ring-head summary**: from every machine satisfying `Pre`, a masked
    run of eight deterministic instructions ends in the machine `Spec`
    describes. -/
theorem contract (m₀ : Machine) (h : Pre m₀) : ∃ m, MRun B img 8 m₀ m ∧ Spec m₀ m := by
  obtain ⟨c₀, ram⟩ := m₀
  obtain ⟨hpc, hhead, hmask, hal, hcell, hbuf⟩ := h
  simp only at hpc hhead hmask hal hcell hbuf
  generalize hH : c₀.get 10 = H at hhead hbuf
  generalize hS : c₀.get 9 = S at hal hcell hbuf
  -- The eight machines.
  let c1 := c₀.wr 12 (H + 1) 0x2001069c
  let c2 := c1.wr 10 (H + S) 0x2001069e
  let c3 := c2.wr 13 (H + 1 + 0xfffffffc) 0x200106a2
  let byte := extend .b false (ramRead ram (H + S + 0x1d) .b)
  let c4 := c3.wr 11 byte 0x200106a6
  let c5 := c4.wr 10 (alu .sltu (H + 1 + 0xfffffffc) 1) 0x200106aa
  let c6 := c5.wr 10 (alu .add (alu .sltu (H + 1 + 0xfffffffc) 1) 0xffffffff) 0x200106ac
  let c7 := c6.wr 10 (next H) 0x200106ae
  let c8 := c7.goto exit
  have cs1 : c1.sameCsr c₀ := Core.sameCsr_wr _ _ _ _
  have cs2 : c2.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans cs1
  have cs3 : c3.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans cs2
  have cs4 : c4.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans cs3
  have cs5 : c5.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans cs4
  have cs6 : c6.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans cs5
  have cs7 : c7.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans cs6
  have cs8 : c8.sameCsr c₀ := (Core.sameCsr_goto _ _).trans cs7
  have s0 : DetStep B img ⟨c₀, ram⟩ ⟨c1, ram⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact i0) fun o => ?_
    rw [exec_opimm, hpc, hH]; rfl
  have s1 : DetStep B img ⟨c1, ram⟩ ⟨c2, ram⟩ := by
    refine detStep_of (by show (0x2001069c : Word).getLsbD 0 = false; decide) i1 fun o => ?_
    rw [exec_op]
    have : c1.get 10 = H := by simp [c1, Core.wr_get, hH]
    have h9 : c1.get 9 = S := by simp [c1, Core.wr_get, hS]
    simp only [alu, this, h9]; rfl
  have s2 : DetStep B img ⟨c2, ram⟩ ⟨c3, ram⟩ := by
    refine detStep_of (by show (0x2001069e : Word).getLsbD 0 = false; decide) i2 fun o => ?_
    rw [exec_opimm]
    have : c2.get 12 = H + 1 := by simp [c2, c1, Core.wr_get]
    simp only [alu, this]; rfl
  have s3 : DetStep B img ⟨c3, ram⟩ ⟨c4, ram⟩ := by
    refine detStep_of (by show (0x200106a2 : Word).getLsbD 0 = false; decide) i3 fun o => ?_
    rw [exec_load]
    have : c3.get 10 = H + S := by simp [c3, c2, Core.wr_get]
    rw [this, interp_load_ram o (by simp only [Width.bytes, Nat.mod_one]) hbuf]
    rfl
  have s4 : DetStep B img ⟨c4, ram⟩ ⟨c5, ram⟩ := by
    refine detStep_of (by show (0x200106a6 : Word).getLsbD 0 = false; decide) i4 fun o => ?_
    rw [exec_opimm]
    have : c4.get 13 = H + 1 + 0xfffffffc := by simp [c4, c3, Core.wr_get]
    simp only [this]; rfl
  have s5 : DetStep B img ⟨c5, ram⟩ ⟨c6, ram⟩ := by
    refine detStep_of (by show (0x200106aa : Word).getLsbD 0 = false; decide) i5 fun o => ?_
    rw [exec_opimm]
    have : c5.get 10 = alu .sltu (H + 1 + 0xfffffffc) 1 := by simp [c5, Core.wr_get]
    simp only [this]; rfl
  have s6 : DetStep B img ⟨c6, ram⟩ ⟨c7, ram⟩ := by
    refine detStep_of (by show (0x200106ac : Word).getLsbD 0 = false; decide) i6 fun o => ?_
    rw [exec_op]
    have e10 : c6.get 10 = alu .add (alu .sltu (H + 1 + 0xfffffffc) 1) 0xffffffff := by
      simp [c6, Core.wr_get]
    have e12 : c6.get 12 = H + 1 := by simp [c6, c5, c4, c3, c2, c1, Core.wr_get]
    rw [e10, e12, wrap hhead]; rfl
  have s7 : DetStep B img ⟨c7, ram⟩ ⟨c8, ramWrite ram (S + 0x14) (next H) .w⟩ := by
    refine detStep_of (by show (0x200106ae : Word).getLsbD 0 = false; decide) i7 fun o => ?_
    rw [exec_store]
    have e9 : c7.get 9 = S := by simp [c7, c6, c5, c4, c3, c2, c1, Core.wr_get, hS]
    have e10 : c7.get 10 = next H := by simp [c7, Core.wr_get]
    rw [e9, e10, interp_store_ram o hal hcell]
    rfl
  have mk : ∀ c : Core, c.sameCsr c₀ → Masked ⟨c, ram⟩ := fun c h => masked_of_sameCsr h hmask
  refine ⟨⟨c8, ramWrite ram (S + 0x14) (next H) .w⟩,
    .step hmask s0 (.step (mk _ cs1) s1 (.step (mk _ cs2) s2 (.step (mk _ cs3) s3
      (.step (mk _ cs4) s4 (.step (mk _ cs5) s5 (.step (mk _ cs6) s6
        (.single (mk _ cs7) s7))))))), ?_⟩
  refine ⟨rfl, ?hd, ?b, ?a2, ?a3, ?fr, cs8, ?rm⟩
  case hd => simp [c8, c7, Core.wr_get, hH]
  case b => simp only [hH, hS]; simp [c8, c7, c6, c5, c4, Core.wr_get, byte]
  case a2 => simp [c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get, hH]
  case a3 => simp [c8, c7, c6, c5, c4, c3, Core.wr_get, hH]
  case fr =>
    intro r a b d e
    by_cases hr : r = 0
    · subst hr; simp [Core.get]
    · simp [c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get, a, b, d, e, hr]
  case rm => simp only [hH, hS]

/-- The summary, in the form `Hybrid.hybrid_sound` takes. -/
def summary : Summary B img where
  Pre := Pre
  Post m := ∃ m₀, Pre m₀ ∧ Spec m₀ m
  run m h := let ⟨m', hr, hs⟩ := contract m h; ⟨7, m', hr, m, h, hs⟩

/-- The stored head stays below the capacity: the invariant the abstract
    side keeps for the head cell. -/
theorem post_head_lt {m₀ m : Machine} (h : Pre m₀) (hs : Spec m₀ m) : (m.core.get 10).toNat < 4 := by
  rw [hs.head]; exact next_lt h.head

end E5R.Hifive1.Hybrid.Ring
