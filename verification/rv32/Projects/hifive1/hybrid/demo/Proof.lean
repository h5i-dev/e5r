/-
  Hybrid demo: one kernel-checked safety theorem for a real compiled binary
  (Projects/hifive1/hybrid/demo/ring.rs, rustc 1.98.1, build/hybrid-ring-O2.elf),
  combining a directly proved machine-code summary with the abstract-
  interpretation certificate checker.

  Original e5r code, Apache-2.0.

  This is a separate integration example, not the Embassy firmware. The
  binary performs one ring-head step exactly as embassy-sync's channel does
  in the firmware (`addi +1; addi -4; seqz; addi -1; and`) and then loops,
  writing `head * 33` to pwm0.pwmcmp1. The property is the checker's: no
  reachable machine can escape, and every pwmcmp1 write is at most 100.

  * Region 0x20010000..0x20010026 (boot through the head store) is proved
    directly (`region`): a masked run of 15 instructions from every boot
    state the board allows, ending at 0x20010028 with the head in 0..3.
  * Everything reachable from there is covered by the checker:
    `check cfg handover cert = true`, evaluated by the kernel, and
    `E5R.AI.check_sound`. The certificate comes from the untrusted analyzer
    (AnalyzeDemo.lean) and is only data here.
  * `Hybrid.seq_sound` composes them for global `Reach` from boot.

  Abstract interpretation alone cannot prove this program: from boot the
  analyzer reports that pwmcmp1 may receive 132 (head 4 after the wrap; see
  results/hybrid-demo-controls.txt). The summary supplies the relational fact.
-/
import Theories.Hybrid.Basic
import Theories.Hybrid.Wrap
import Theories.AbsintSound
import Projects.hifive1.hybrid.demo.Config
import Projects.hifive1.hybrid.demo.Cert

set_option maxRecDepth 100000

namespace E5R.HybridDemo.Proof
open E5R E5R.AI E5R.Hybrid E5R.HybridDemo.Job

abbrev B := cfg.board
abbrev img := cfg.img

/-! ## The region's instructions (kernel-checked against the image) -/

theorem i0 : fetchDecode img 0x20010000 = some (.lui 2 0x80004000, 4) := by decide +kernel
theorem i1 : fetchDecode img 0x20010004 = some (.jal 0 4, 4) := by decide +kernel
theorem i2 : fetchDecode img 0x20010008 = some (.opimm .add 2 2 0xfffffff0, 2) := by decide +kernel
theorem i3 : fetchDecode img 0x2001000a = some (.lui 10 0x80000000, 4) := by decide +kernel
theorem i4 : fetchDecode img 0x2001000e = some (.load .w true 11 10 0, 2) := by decide +kernel
theorem i5 : fetchDecode img 0x20010010 = some (.opimm .add 12 2 12, 2) := by decide +kernel
theorem i6 : fetchDecode img 0x20010012 = some (.opimm .and 11 11 3, 2) := by decide +kernel
theorem i7 : fetchDecode img 0x20010014 = some (.store .w 2 11 12, 2) := by decide +kernel
theorem i8 : fetchDecode img 0x20010016 = some (.load .w true 11 2 12, 2) := by decide +kernel
theorem i9 : fetchDecode img 0x20010018 = some (.opimm .add 11 11 1, 2) := by decide +kernel
theorem i10 : fetchDecode img 0x2001001a = some (.opimm .add 12 11 0xfffffffc, 4) := by decide +kernel
theorem i11 : fetchDecode img 0x2001001e = some (.opimm .sltu 12 12 1, 4) := by decide +kernel
theorem i12 : fetchDecode img 0x20010022 = some (.opimm .add 12 12 0xffffffff, 2) := by decide +kernel
theorem i13 : fetchDecode img 0x20010024 = some (.op .and 11 11 12, 2) := by decide +kernel
theorem i14 : fetchDecode img 0x20010026 = some (.store .w 10 11 0, 2) := by decide +kernel

/-! ## The abstract handover state, concretely -/

theorem handover_get (r : Reg) :
    handover.get r = if r.val = 10 then AV.const head else if r.val = 0 then AV.const 0 else AV.top := by
  revert r; decide

theorem sameCsr_parts {c d : Core} (h : c.sameCsr d) :
    c.mie_ = d.mie_ ∧ c.mpie = d.mpie ∧ c.mpp = d.mpp ∧ c.mieReg = d.mieReg ∧ c.mtvec = d.mtvec ∧
      c.mepc = d.mepc ∧ c.mcause = d.mcause ∧ c.mscratch = d.mscratch := by
  simp only [Core.sameCsr, Core.ctl, Prod.mk.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

/-! ## The directly proved region -/

theorem region (m₀ : Machine) (hb : StateHolds ρM boot m₀) :
    ∃ m, MRun B img 15 m₀ m ∧ StateHolds ρM handover m := by
  obtain ⟨c₀, ram⟩ := m₀
  have hpc : c₀.pc = 0x20010000 := hb.pc
  have hmask : c₀.mie_ = false := by
    have := hb.mie; simp only [boot, Tri.mayBe] at this; simpa using this
  let X := ramRead ram 0x80000000 .w
  let H := alu .and X 3
  have hH : H.toNat < 4 := by
    show (X &&& 3).toNat < 4
    rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  let c1 := c₀.wr 2 0x80004000 0x20010004
  let c2 := c1.goto 0x20010008
  let c3 := c2.wr 2 0x80003ff0 0x2001000a
  let c4 := c3.wr 10 0x80000000 0x2001000e
  let c5 := c4.wr 11 X 0x20010010
  let c6 := c5.wr 12 0x80003ffc 0x20010012
  let c7 := c6.wr 11 H 0x20010014
  let ram1 := ramWrite ram 0x80003ffc H .w
  let c8 := c7.goto 0x20010016
  let c9 := c8.wr 11 H 0x20010018
  let c10 := c9.wr 11 (H + 1) 0x2001001a
  let c11 := c10.wr 12 (H + 1 + 0xfffffffc) 0x2001001e
  let c12 := c11.wr 12 (alu .sltu (H + 1 + 0xfffffffc) 1) 0x20010022
  let c13 := c12.wr 12 (alu .add (alu .sltu (H + 1 + 0xfffffffc) 1) 0xffffffff) 0x20010024
  let c14 := c13.wr 11 (next H) 0x20010026
  let ram2 := ramWrite ram1 0x80000000 (next H) .w
  let c15 := c14.goto 0x20010028
  have s0 : DetStep B img ⟨c₀, ram⟩ ⟨c1, ram⟩ :=
    detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact i0) fun o => by rw [exec_lui, hpc]; rfl
  have s1 : DetStep B img ⟨c1, ram⟩ ⟨c2, ram⟩ :=
    detStep_of (by show (0x20010004 : Word).getLsbD 0 = false; decide) i1 fun o => by
      rw [exec_jal, jump_ok _ _ (by show ((0x20010004 : Word) + 4).getLsbD 0 = false; decide)]; rfl
  have s2 : DetStep B img ⟨c2, ram⟩ ⟨c3, ram⟩ :=
    detStep_of (by show (0x20010008 : Word).getLsbD 0 = false; decide) i2 fun o => by
      rw [exec_opimm]
      have : c2.get 2 = 0x80004000 := by simp [c2, c1, Core.wr_get]
      simp only [alu, this]; rfl
  have s3 : DetStep B img ⟨c3, ram⟩ ⟨c4, ram⟩ :=
    detStep_of (by show (0x2001000a : Word).getLsbD 0 = false; decide) i3 fun o => by
      rw [exec_lui]; rfl
  have s4 : DetStep B img ⟨c4, ram⟩ ⟨c5, ram⟩ :=
    detStep_of (by show (0x2001000e : Word).getLsbD 0 = false; decide) i4 fun o => by
      rw [exec_load]
      have : c4.get 10 + 0 = 0x80000000 := by simp [c4, Core.wr_get]
      rw [this, interp_load_ram o (by decide) (by decide)]; rfl
  have s5 : DetStep B img ⟨c5, ram⟩ ⟨c6, ram⟩ :=
    detStep_of (by show (0x20010010 : Word).getLsbD 0 = false; decide) i5 fun o => by
      rw [exec_opimm]
      have : c5.get 2 = 0x80003ff0 := by simp [c5, c4, c3, Core.wr_get]
      simp only [alu, this]; rfl
  have s6 : DetStep B img ⟨c6, ram⟩ ⟨c7, ram⟩ :=
    detStep_of (by show (0x20010012 : Word).getLsbD 0 = false; decide) i6 fun o => by
      rw [exec_opimm]
      have : c6.get 11 = X := by simp [c6, c5, Core.wr_get]
      simp only [this]; rfl
  have s7 : DetStep B img ⟨c7, ram⟩ ⟨c8, ram1⟩ :=
    detStep_of (by show (0x20010014 : Word).getLsbD 0 = false; decide) i7 fun o => by
      rw [exec_store]
      have e2 : c7.get 2 + 12 = 0x80003ffc := by simp [c7, c6, c5, c4, c3, Core.wr_get]
      have e11 : c7.get 11 = H := by simp [c7, Core.wr_get]
      rw [e2, e11, interp_store_ram o (by decide) (by decide)]; rfl
  have s8 : DetStep B img ⟨c8, ram1⟩ ⟨c9, ram1⟩ :=
    detStep_of (by show (0x20010016 : Word).getLsbD 0 = false; decide) i8 fun o => by
      rw [exec_load]
      have e2 : c8.get 2 + 12 = 0x80003ffc := by simp [c8, c7, c6, c5, c4, c3, Core.wr_get]
      rw [e2, interp_load_ram o (by decide) (by decide)]
      simp only [ram1, ramRead_ramWrite_w]; rfl
  have s9 : DetStep B img ⟨c9, ram1⟩ ⟨c10, ram1⟩ :=
    detStep_of (by show (0x20010018 : Word).getLsbD 0 = false; decide) i9 fun o => by
      rw [exec_opimm]
      have : c9.get 11 = H := by simp [c9, Core.wr_get]
      simp only [alu, this]; rfl
  have s10 : DetStep B img ⟨c10, ram1⟩ ⟨c11, ram1⟩ :=
    detStep_of (by show (0x2001001a : Word).getLsbD 0 = false; decide) i10 fun o => by
      rw [exec_opimm]
      have : c10.get 11 = H + 1 := by simp [c10, Core.wr_get]
      simp only [alu, this]; rfl
  have s11 : DetStep B img ⟨c11, ram1⟩ ⟨c12, ram1⟩ :=
    detStep_of (by show (0x2001001e : Word).getLsbD 0 = false; decide) i11 fun o => by
      rw [exec_opimm]
      have : c11.get 12 = H + 1 + 0xfffffffc := by simp [c11, Core.wr_get]
      simp only [this]; rfl
  have s12 : DetStep B img ⟨c12, ram1⟩ ⟨c13, ram1⟩ :=
    detStep_of (by show (0x20010022 : Word).getLsbD 0 = false; decide) i12 fun o => by
      rw [exec_opimm]
      have : c12.get 12 = alu .sltu (H + 1 + 0xfffffffc) 1 := by simp [c12, Core.wr_get]
      simp only [this]; rfl
  have s13 : DetStep B img ⟨c13, ram1⟩ ⟨c14, ram1⟩ :=
    detStep_of (by show (0x20010024 : Word).getLsbD 0 = false; decide) i13 fun o => by
      rw [exec_op]
      have e11 : c13.get 11 = H + 1 := by simp [c13, c12, c11, c10, Core.wr_get]
      have e12 : c13.get 12 = alu .add (alu .sltu (H + 1 + 0xfffffffc) 1) 0xffffffff := by
        simp [c13, Core.wr_get]
      rw [e11, e12, wrap' hH]; rfl
  have s14 : DetStep B img ⟨c14, ram1⟩ ⟨c15, ram2⟩ :=
    detStep_of (by show (0x20010026 : Word).getLsbD 0 = false; decide) i14 fun o => by
      rw [exec_store]
      have e10 : c14.get 10 + 0 = 0x80000000 := by
        simp [c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, Core.wr_get]
      have e11 : c14.get 11 = next H := by simp [c14, Core.wr_get]
      rw [e10, e11, interp_store_ram o (by decide) (by decide)]; rfl
  -- Every core keeps the boot CSRs, so every machine of the run is masked.
  have cs : ∀ c : Core, c.sameCsr c₀ → ∀ r, Masked ⟨c, r⟩ := fun c h _ => by
    show c.mie_ = false; rw [(sameCsr_parts h).1, hmask]
  have k1 : c1.sameCsr c₀ := Core.sameCsr_wr _ _ _ _
  have k2 : c2.sameCsr c₀ := (Core.sameCsr_goto _ _).trans k1
  have k3 : c3.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans k2
  have k4 : c4.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans k3
  have k5 : c5.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans k4
  have k6 : c6.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans k5
  have k7 : c7.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans k6
  have k8 : c8.sameCsr c₀ := (Core.sameCsr_goto _ _).trans k7
  have k9 : c9.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans k8
  have k10 : c10.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans k9
  have k11 : c11.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans k10
  have k12 : c12.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans k11
  have k13 : c13.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans k12
  have k14 : c14.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans k13
  have k15 : c15.sameCsr c₀ := (Core.sameCsr_goto _ _).trans k14
  refine ⟨⟨c15, ram2⟩, .step hmask s0 (.step (cs _ k1 _) s1 (.step (cs _ k2 _) s2 (.step (cs _ k3 _) s3 (.step (cs _ k4 _) s4 (.step (cs _ k5 _) s5 (.step (cs _ k6 _) s6 (.step (cs _ k7 _) s7 (.step (cs _ k8 _) s8 (.step (cs _ k9 _) s9 (.step (cs _ k10 _) s10 (.step (cs _ k11 _) s11 (.step (cs _ k12 _) s12 (.step (cs _ k13 _) s13 (.single (cs _ k14 _) s14)))))))))))))), ?_⟩
  -- The exit machine is described by the checker's start state.
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := sameCsr_parts k15
  refine ⟨rfl, fun r => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [handover_get]
    by_cases h10 : r.val = 10
    · have : r = 10 := Fin.ext h10
      subst this
      have : c15.get 10 = 0x80000000 := by
        simp [c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, Core.wr_get]
      simp only [h10, ↓reduceIte, this]
      show (0x80000000 : Word).toNat ∈ [head % M32]; decide
    · by_cases h0 : r.val = 0
      · simp only [h0, ↓reduceIte]
        have : (⟨c15, ram2⟩ : Machine).core.get r = 0 := by simp [Core.get, h0]
        rw [this]; show (0 : Word).toNat ∈ [0 % M32]; decide
      · simp only [h10, h0, ↓reduceIte]; trivial
  · intro c hc
    simp only [handover, List.mem_singleton] at hc
    subst hc
    intro _
    show (ramRead ram2 0x80000000 .w).toNat ∈ [0, 1, 2, 3]
    simp only [ram2, ramRead_ramWrite_w]
    have := next_lt hH
    simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
  · show handover.mie.mayBe c15.mie_ = true; rw [e1, hmask]; rfl
  · show boot.mpie.mayBe c15.mpie = true; rfl
  · show c15.mpp.toNat ∈ boot.mpp; rw [e3]; exact hb.mpp
  · show boot.mieReg.gam ρM c15.mieReg; rw [e4]; exact hb.mieReg
  · show boot.mtvec.gam ρM c15.mtvec; trivial
  · show boot.mepc.gam ρM c15.mepc; trivial
  · show boot.mcause.gam ρM c15.mcause; trivial
  · show boot.mscratch.gam ρM c15.mscratch; trivial

/-- The directly proved summary, in the form `Hybrid` composes. -/
def summary : Summary B img where
  Pre := StateHolds ρM boot
  Post := StateHolds ρM handover
  run m h := let ⟨m', hr, hs⟩ := region m h; ⟨14, m', hr, hs⟩

/-! ## The abstract-interpretation part -/

/-- The checker accepts the analyzer's certificate from the handover state. -/
theorem ai_check : check cfg handover Cert.cert = true := by decide +kernel

theorem ai_safe : Safe B img (StateHolds ρM handover) (EvOk cfg) :=
  check_sound ai_check (fun _ h => h)

/-! ## The composed theorem -/

/-- **Hybrid safety of the demo binary.** From every boot state the board
    allows, no reachable machine can escape, and every device write on the
    way satisfies the configured property (pwmcmp1 at most 100). -/
theorem demo_safe : Safe B img (StateHolds ρM boot) (EvOk cfg) :=
  seq_sound summary (fun _ h => h) ai_safe

end E5R.HybridDemo.Proof
