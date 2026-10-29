/-
  Hybrid demo, loop variant: one kernel-checked safety theorem for a real
  compiled binary (ring_loop.rs, rustc 1.98.1, build/hybrid-ring-loop-O2.elf)
  in which abstract interpretation covers the program around a directly
  proved region that runs on every loop iteration.

  Original e5r code, Apache-2.0.

  The main loop loads the ring head, steps it exactly as embassy-sync's
  channel does in the firmware (0x20010018..0x20010026: addi +1; addi -4;
  seqz; addi -1; and; sw), and writes `head * 33` to pwm0.pwmcmp1.

  * The checker (`checkHybrid`, evaluated by the kernel) covers every node of
    the certificate except the delegated region entry at 0x20010018; the
    certificate (LoopCert.lean, from the untrusted BuildLoopCert.lean) is
    data only.
  * The region is a masked run of six instructions (`contract`), lifted to
    the abstract states around it (`adapter`): from any machine an accepted
    entry node describes, the run ends in a machine `post` of that node
    describes, and `post` of every delegated node is covered by a main node
    (`entries_ok`, kernel-evaluated).
  * `E5R.AI.check_sound_hybrid` (support-lean4 d6ae986) composes them, with
    `Hybrid.regionOf` discharging its step and interrupt obligations.

  Abstract interpretation alone cannot prove this program (BuildLoopCert
  --no-delegate: pwmcmp1 may receive up to 132).
-/
import Theories.Hybrid.AIBridge
import Theories.Hybrid.Wrap
import Projects.hifive1.hybrid.demo.LoopConfig
import Projects.hifive1.hybrid.demo.LoopCert

set_option maxRecDepth 100000

namespace E5R.HybridLoop.Proof
open E5R E5R.AI E5R.Hybrid E5R.HybridLoop.Job

abbrev B := cfg.board
abbrev img := cfg.img

/-! ## The region (kernel-checked against the image) -/

theorem i0 : fetchDecode img 0x20010018 = some (.opimm .add 12 12 1, 2) := by decide +kernel
theorem i1 : fetchDecode img 0x2001001a = some (.opimm .add 13 12 0xfffffffc, 4) := by decide +kernel
theorem i2 : fetchDecode img 0x2001001e = some (.opimm .sltu 13 13 1, 4) := by decide +kernel
theorem i3 : fetchDecode img 0x20010022 = some (.opimm .add 13 13 0xffffffff, 2) := by decide +kernel
theorem i4 : fetchDecode img 0x20010024 = some (.op .and 12 12 13, 2) := by decide +kernel
theorem i5 : fetchDecode img 0x20010026 = some (.store .w 10 12 0, 2) := by decide +kernel

/-- The wrap mask: all ones unless the head wraps. -/
def mask (h : Word) : Word := alu .add (alu .sltu (h + 1 + 0xfffffffc) 1) 0xffffffff

theorem mask_vals {h : Word} (hh : h.toNat < 4) : (mask h).toNat ∈ [0, 0xffffffff] := by
  rcases cases4 hh with rfl | rfl | rfl | rfl <;> decide

structure Pre (m : Machine) : Prop where
  pc : m.core.pc = 0x20010018
  head : (m.core.get 12).toNat < 4
  masked : m.core.mie_ = false
  aligned : (m.core.get 10).toNat % 4 = 0
  ram : B.inRam (m.core.get 10) 4 = true

structure Spec (m₀ m : Machine) : Prop where
  pc : m.core.pc = 0x20010028
  head : m.core.get 12 = next (m₀.core.get 12)
  mask : m.core.get 13 = mask (m₀.core.get 12)
  frame : ∀ r : Reg, r ≠ 12 → r ≠ 13 → m.core.get r = m₀.core.get r
  csr : m.core.sameCsr m₀.core
  ram : m.ram = ramWrite m₀.ram (m₀.core.get 10) (next (m₀.core.get 12)) .w

theorem masked_of_sameCsr {c d : Core} (h : c.sameCsr d) (hd : d.mie_ = false) : c.mie_ = false := by
  have := congrArg (·.1) h; simp only [Core.ctl] at this; rw [this, hd]

theorem contract (m₀ : Machine) (h : Pre m₀) : ∃ m, MRun B img 6 m₀ m ∧ Spec m₀ m := by
  obtain ⟨c₀, ram⟩ := m₀
  obtain ⟨hpc, hhead, hmask, hal, hram⟩ := h
  simp only at hpc hhead hmask hal hram
  generalize hH : c₀.get 12 = H at hhead
  generalize hA : c₀.get 10 = A at hal hram
  let c1 := c₀.wr 12 (H + 1) 0x2001001a
  let c2 := c1.wr 13 (H + 1 + 0xfffffffc) 0x2001001e
  let c3 := c2.wr 13 (alu .sltu (H + 1 + 0xfffffffc) 1) 0x20010022
  let c4 := c3.wr 13 (mask H) 0x20010024
  let c5 := c4.wr 12 (next H) 0x20010026
  let c6 := c5.goto 0x20010028
  have s0 : DetStep B img ⟨c₀, ram⟩ ⟨c1, ram⟩ :=
    detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact i0) fun o => by rw [exec_opimm, hpc, hH]; rfl
  have s1 : DetStep B img ⟨c1, ram⟩ ⟨c2, ram⟩ :=
    detStep_of (by show (0x2001001a : Word).getLsbD 0 = false; decide) i1 fun o => by
      rw [exec_opimm]
      have : c1.get 12 = H + 1 := by simp [c1, Core.wr_get]
      simp only [alu, this]; rfl
  have s2 : DetStep B img ⟨c2, ram⟩ ⟨c3, ram⟩ :=
    detStep_of (by show (0x2001001e : Word).getLsbD 0 = false; decide) i2 fun o => by
      rw [exec_opimm]
      have : c2.get 13 = H + 1 + 0xfffffffc := by simp [c2, Core.wr_get]
      simp only [this]; rfl
  have s3 : DetStep B img ⟨c3, ram⟩ ⟨c4, ram⟩ :=
    detStep_of (by show (0x20010022 : Word).getLsbD 0 = false; decide) i3 fun o => by
      rw [exec_opimm]
      have : c3.get 13 = alu .sltu (H + 1 + 0xfffffffc) 1 := by simp [c3, Core.wr_get]
      simp only [this]; rfl
  have s4 : DetStep B img ⟨c4, ram⟩ ⟨c5, ram⟩ :=
    detStep_of (by show (0x20010024 : Word).getLsbD 0 = false; decide) i4 fun o => by
      rw [exec_op]
      have e12 : c4.get 12 = H + 1 := by simp [c4, c3, c2, c1, Core.wr_get]
      have e13 : c4.get 13 = mask H := by simp [c4, Core.wr_get]
      rw [e12, e13]; unfold mask; rw [wrap' hhead]; rfl
  have s5 : DetStep B img ⟨c5, ram⟩ ⟨c6, ramWrite ram A (next H) .w⟩ :=
    detStep_of (by show (0x20010026 : Word).getLsbD 0 = false; decide) i5 fun o => by
      rw [exec_store]
      have e10 : c5.get 10 + 0 = A := by simp [c5, c4, c3, c2, c1, Core.wr_get, hA]
      have e12 : c5.get 12 = next H := by simp [c5, Core.wr_get]
      rw [e10, e12, interp_store_ram o hal hram]; rfl
  have k1 : c1.sameCsr c₀ := Core.sameCsr_wr _ _ _ _
  have k2 : c2.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans k1
  have k3 : c3.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans k2
  have k4 : c4.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans k3
  have k5 : c5.sameCsr c₀ := (Core.sameCsr_wr _ _ _ _).trans k4
  have k6 : c6.sameCsr c₀ := (Core.sameCsr_goto _ _).trans k5
  have mk : ∀ c : Core, c.sameCsr c₀ → ∀ r, Masked ⟨c, r⟩ := fun c h _ => masked_of_sameCsr h hmask
  refine ⟨⟨c6, ramWrite ram A (next H) .w⟩, .step hmask s0 (.step (mk _ k1 _) s1 (.step (mk _ k2 _) s2
    (.step (mk _ k3 _) s3 (.step (mk _ k4 _) s4 (.single (mk _ k5 _) s5))))), ?_⟩
  refine ⟨rfl, ?hd, ?mk, ?fr, k6, ?rm⟩
  case hd => simp [c6, c5, Core.wr_get, hH]
  case mk => simp [c6, c5, c4, Core.wr_get, hH]
  case fr =>
    intro r a b
    by_cases hr : r = 0
    · subst hr; simp [Core.get]
    · simp [c6, c5, c4, c3, c2, c1, Core.wr_get, a, b, hr]
  case rm => simp only [hH, hA]

/-! ## The region between abstract states -/

theorem sameCsr_parts {c d : Core} (h : c.sameCsr d) :
    c.mie_ = d.mie_ ∧ c.mpie = d.mpie ∧ c.mpp = d.mpp ∧ c.mieReg = d.mieReg ∧ c.mtvec = d.mtvec ∧
      c.mepc = d.mepc ∧ c.mcause = d.mcause ∧ c.mscratch = d.mscratch := by
  simp only [Core.sameCsr, Core.ctl, Prod.mk.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

/-- From every machine an accepted abstract entry state describes, the
    region's masked run ends in a machine `post` of that state describes. -/
theorem adapter {s : AState} {m : Machine} (ha : enterOk s = true) (hs : StateHolds ρM s m) :
    ∃ m', MRun B img 6 m m' ∧ StateHolds ρM (post s) m' := by
  unfold enterOk at ha
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at ha
  obtain ⟨⟨⟨⟨⟨⟨hpc, hnd⟩, hmie⟩, hwf⟩, _⟩, h12⟩, h10⟩ := ha
  split at h10
  · rename_i a ha10
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h10
    obtain ⟨⟨hal, hin⟩, hlt⟩ := h10
    -- Concrete facts from the abstract entry state.
    have hA : m.core.get 10 = w a := by
      have := hs.regs 10; rw [ha10] at this
      simp only [AV.gam, List.mem_singleton] at this
      rw [← this]; simp [w]
    have hH : (m.core.get 12).toNat < 4 := by
      have := leq_sound h12 (hs.regs 12); simp only [AV.gam] at this; omega
    have hmk : m.core.mie_ = false := by
      have := hs.mie; revert this hmie; cases s.mie <;> cases m.core.mie_ <;> simp [Tri.mayBe]
    have hwa : (w a).toNat = a := by simp [w]; unfold M32 at hlt; omega
    have pre : Pre m := ⟨by rw [hs.pc, hpc]; rfl, hH, hmk,
      by rw [hA, hwa]; exact hal, by rw [hA]; exact hin⟩
    obtain ⟨m', hr, sp⟩ := contract m pre
    refine ⟨m', hr, ?_⟩
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := sameCsr_parts sp.csr
    have hlen : s.regs.length = 31 := by
      unfold AState.wf at hwf; simp only [Bool.and_eq_true, beq_iff_eq] at hwf; exact hwf.1.1.1
    have pg : ∀ r, (post s).get r = ((s.set 12 headAV).set 13 maskAV).get r :=
      fun _ => rfl
    have hlen12 : (s.set 12 headAV).regs.length = 31 := by
      simp [AState.set, hlen]
    refine ⟨?pc, fun r => ?regs, ?mem, ?mie, ?mpie, ?mpp, ?mieReg, ?mtvec, ?mepc, ?mcause, ?msc⟩
    case pc => rw [sp.pc]; rfl
    case regs =>
      rw [pg]
      by_cases r13 : r = 13
      · subst r13; rw [AState.get_set_self _ _ _ (by decide) hlen12, sp.mask]
        exact mask_vals hH
      · rw [AState.get_set_ne _ _ _ _ r13]
        by_cases r12 : r = 12
        · subst r12; rw [AState.get_set_self _ _ _ (by decide) hlen, sp.head]
          have := next_lt hH
          simp only [headAV, AV.gam, List.mem_cons, List.not_mem_nil, or_false]; omega
        · rw [AState.get_set_ne _ _ _ _ r12, sp.frame r r12 r13]; exact hs.regs r
    case mem =>
      show MemHolds ρM m'.ram (storeStrong s.mem .abs (match s.get 10 with | .vals [a] => a | _ => 0) .w headAV)
      rw [ha10, sp.ram, hA]
      have hwfm : ∀ c ∈ s.mem, c.wf cfg = true ∧ c.base = .abs := by
        unfold AState.wf at hwf
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true, hnd,
          Bool.false_or] at hwf
        exact fun c hc => ⟨hwf.1.1.2 c hc, hwf.1.2 c hc⟩
      refine storeStrong_sound (base := .abs) hs.mem ?_
        (storeSep_abs (cfg := cfg) (by decide) (fun c hc => (hwfm c hc).1) hlt hin
          (fun c hc hb => by rw [(hwfm c hc).2] at hb; cases hb))
      have := next_lt hH
      simp only [headAV, stored, AV.gam, List.mem_cons, List.not_mem_nil, or_false]; omega
    case mie => show s.mie.mayBe m'.core.mie_ = true; rw [e1]; exact hs.mie
    case mpie => show s.mpie.mayBe m'.core.mpie = true; rw [e2]; exact hs.mpie
    case mpp => show m'.core.mpp.toNat ∈ s.mpp; rw [e3]; exact hs.mpp
    case mieReg => show s.mieReg.gam ρM m'.core.mieReg; rw [e4]; exact hs.mieReg
    case mtvec => show s.mtvec.gam ρM m'.core.mtvec; rw [e5]; exact hs.mtvec
    case mepc => show s.mepc.gam ρM m'.core.mepc; rw [e6]; exact hs.mepc
    case mcause => show s.mcause.gam ρM m'.core.mcause; rw [e7]; exact hs.mcause
    case msc => show s.mscratch.gam ρM m'.core.mscratch; rw [e8]; exact hs.mscratch
  · simp at h10

end E5R.HybridLoop.Proof

namespace E5R.HybridLoop.Proof
open E5R E5R.AI E5R.Hybrid E5R.HybridLoop.Job

/-! ## Composition with the checker -/

/-- The checker accepts the certificate, with the region entry delegated. -/
theorem ai_check : checkHybrid cfg boot Cert.cert = true := by decide +kernel

/-- Every delegated node is accepted, and `post` of it is covered by a
    main-thread node of the certificate. -/
theorem entries_ok : Cert.cert.nodes.all (fun n =>
    !(n.s.pc == regionEntry) || n.s.hnd ||
      (enterOk n.s && Cert.cert.nodes.any fun n' => !n'.s.hnd && (post n.s).leq n'.s)) = true := by
  decide +kernel

theorem delegate_eq : Cert.cert.delegate = [(regionEntry, 0)] := rfl

/-- The region, for the checker's theorem. -/
abbrev region : Region { cfg with hkeep := Cert.cert.hkeep } Cert.cert :=
  regionOf { cfg with hkeep := Cert.cert.hkeep } Cert.cert

theorem hentry : ∀ k (n : Node), (n.s.pc, k) ∈ Cert.cert.delegate → n ∈ Cert.cert.nodes →
    n.s.hnd = false → ∀ m, StateHolds ρM n.s m → ((fun _ => region) k).R m := by
  intro k n hk hn hnd m hs
  rw [delegate_eq, List.mem_singleton, Prod.mk.injEq] at hk
  have h := List.all_eq_true.mp entries_ok n hn
  simp only [hk.1, beq_self_eq_true, Bool.not_true, hnd, Bool.false_or, Bool.and_eq_true,
    List.any_eq_true, Bool.not_eq_true'] at h
  obtain ⟨ha, n', hn', hnd', hleq⟩ := h
  obtain ⟨m', hr, hpost⟩ := adapter ha hs
  exact regionOf_entry hr (mainInv_of_cover hn' hnd' hleq hpost)

/-- **Hybrid safety of the loop demo.** From every boot state the board
    allows, no reachable machine can escape, and every device write on the
    way satisfies the configured property (pwmcmp1 at most 100). -/
theorem loop_safe : Safe B img (StateHolds ρM boot) (EvOk cfg) :=
  check_sound_hybrid ai_check (fun _ => region) hentry (fun _ h => h)

end E5R.HybridLoop.Proof
