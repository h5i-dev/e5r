/-
  `Uart16550<MmioBackend>::send_bytes` (0x800098a6), on the pinned RMK image: PROVED, no contract.

  Original e5r code, Apache-2.0.

  The function (uart_16550, MMIO backend, stride 1 at 0x10000000 on QEMU virt) checks that the
  transmitter holds nothing (LSR bit 5), and, when the struct's flow-control byte (+0x15) is set and
  loopback (MCR bit 4) is off, that CTS (MSR bit 4) is set; it then stores up to min(len, 16) bytes
  (1 if the FIFO-size byte +0x17 is 0xff) from the buffer to THR and returns the count, or 0.
  Each register offset goes through `assert_offset` (a range check that panics at offset ≥ 8).

  PROVED here: `send_bytes`: from `SendEnv` (the struct holds base 0x10000000 and stride 1, the
  buffer and a 0x50-byte stack frame are RAM), every behaviour of the model, for every value the
  UART registers return, reaches the return address with `SendPost`: quiet, the ABI frame (sp and
  every callee-saved register), RAM changed only in the frame [sp-0x50, sp), and the count 0 or
  1..min(len, 16). The THR stores are device-write events; nothing is assumed about the device.
-/
import Projects.rmk.Uart.SendSegs
import Projects.rmk.DevRead

set_option maxRecDepth 100000

namespace E5R.Rmk.Uart
open E5R E5R.Rmk E5R.Rmk.SendFetch E5R.Rmk.Deframer E5R.Rmk.Deframer.Tail

/-- A byte store to a device register: one step, every oracle, one write event, RAM unchanged. -/
theorem lands_sb_dev {P : Machine → Prop} {m : Machine} {rs1 rs2 : Reg} {off len a : Word} {d : DevReg}
    (hal : m.core.pc.getLsbD 0 = false)
    (hf : fetchDecode img m.core.pc = some (.store .b rs1 rs2 off, len))
    (ha : m.core.get rs1 + off = a) (hin : B.inRam a 1 = false)
    (hd : B.device? a = some d) (hdw : d.write = true) (hw : d.width = 1) (hq : Quiet m.core)
    (h : Lands B img P ⟨m.core.goto (m.core.pc + len), m.ram⟩) : Lands B img P m := by
  have key : ∀ o, stepInstr B img m o =
      .ok (m.core.goto (m.core.pc + len)) m.ram [⟨a, devVal .b (m.core.get rs2)⟩] := by
    intro o
    rw [stepInstr_of hal hf, exec_store, ha, interp_store_dev (w := .b) o (Nat.mod_one _) hin rfl hd hdw hw.symm]
    rfl
  refine .step hq (fun o f e => by rw [key o] at e; cases e) fun x evs hx => ?_
  obtain ⟨o, ho⟩ := step_oracle hq hx
  rw [key o] at ho
  injection ho with h1 h2 h3
  have : x = ⟨m.core.goto (m.core.pc + len), m.ram⟩ := by
    cases x; simp only at h1 h2; rw [h1, h2]
  rw [this]; exact h

theorem thr_none : romRead? img (0x10000000 : Word).toNat 1 false = none := rom_none _ (by decide)
theorem mcr_none : romRead? img (0x10000004 : Word).toNat 1 false = none := rom_none _ (by decide)
theorem lsr_none : romRead? img (0x10000005 : Word).toNat 1 false = none := rom_none _ (by decide)
theorem msr_none : romRead? img (0x10000006 : Word).toNat 1 false = none := rom_none _ (by decide)
theorem thr_dev : B.device? 0x10000000 = some ⟨0x10000000, "uart0.rbr_thr_dll", true, true, 1⟩ := by decide
theorem mcr_dev : B.device? 0x10000004 = some ⟨0x10000004, "uart0.mcr", true, true, 1⟩ := by decide
theorem lsr_dev : B.device? 0x10000005 = some ⟨0x10000005, "uart0.lsr", true, false, 1⟩ := by decide
theorem msr_dev : B.device? 0x10000006 = some ⟨0x10000006, "uart0.msr", true, false, 1⟩ := by decide

/-- What the caller provides. -/
structure SendEnv (m : Machine) : Prop where
  pc : m.core.pc = 0x800098a6
  quiet : Quiet m.core
  ra : (m.core.get 1).getLsbD 0 = false
  spAl : (m.core.get 2).toNat % 4 = 0
  /-- the 0x50-byte frame (saves, and assert_offset's byte at sp-0x41) is RAM -/
  sp : 0x80029bc8 + 0x50 ≤ (m.core.get 2).toNat ∧ (m.core.get 2).toNat ≤ 0x81000000
  /-- the Uart16550 struct (a0): base at +0x1c, stride at +0x20, flags at +0x15 and +0x17 -/
  base : ramRead m.ram (m.core.get 10 + 0x0000001c#32) .w = 0x10000000
  stride : (m.ram (m.core.get 10 + 0x00000020#32)).toNat = 1
  selfAl : (m.core.get 10 + 0x0000001c#32).toNat % 4 = 0
  selfIn : 0x80029bc8 ≤ (m.core.get 10).toNat ∧ (m.core.get 10).toNat + 0x21 ≤ 0x81000000
  /-- the struct lies outside the frame -/
  selfSep : (m.core.get 10).toNat + 0x21 ≤ (m.core.get 2).toNat - 0x50 ∨ (m.core.get 2).toNat ≤ (m.core.get 10).toNat
  /-- the buffer (a1, a2 bytes) is RAM -/
  buf : (m.core.get 12).toNat = 0 ∨ B.inRam (m.core.get 11) (m.core.get 12).toNat = true

/-- What `send_bytes` guarantees on return. -/
structure SendPost (m₀ m : Machine) : Prop where
  pc : m.core.pc = m₀.core.get 1
  quiet : Quiet m.core
  sp : m.core.get 2 = m₀.core.get 2
  saved : ∀ r : Reg, r.val ∉ callerSaved → m.core.get r = m₀.core.get r
  ram : ∀ x, ¬ ((m₀.core.get 2).toNat - 0x50 ≤ x.toNat ∧ x.toNat < (m₀.core.get 2).toNat) → m.ram x = m₀.ram x
  count : (m.core.get 10).toNat = 0 ∨
    (1 ≤ (m.core.get 10).toNat ∧ (m.core.get 10).toNat ≤ (m₀.core.get 12).toNat ∧ (m.core.get 10).toNat ≤ 16)

/-- The registers the function's segments write. -/
def W : List Nat := [1, 2, 8, 9, 10, 11, 12, 18, 19, 20, 21, 22, 23]

theorem notW {r : Reg} (h : r.val ∉ W) : r ≠ 1 ∧ r ≠ 2 ∧ r ≠ 8 ∧ r ≠ 9 ∧ r ≠ 10 ∧ r ≠ 11 ∧ r ≠ 12 ∧
    r ≠ 18 ∧ r ≠ 19 ∧ r ≠ 20 ∧ r ≠ 21 ∧ r ≠ 22 ∧ r ≠ 23 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> subst e <;> exact absurd h (by decide)

/-- The frame pointer after the prologue, and assert_offset's byte below it. -/
def fp (c : Core) : Word := alu .add (c.get 2) 0xffffffd0#32
def ao (c : Core) : Word := alu .add (fp c) 0xffffffe0#32 + 0x0000000f#32

/-- Between the prologue and the epilogue, relative to the entry core `c` and RAM `M0`. -/
structure Mid (c : Core) (M0 : Word → BitVec 8) (m : Machine) : Prop where
  quiet : Quiet m.core
  sp : m.core.get 2 = fp c
  regs : ∀ r : Reg, r.val ∉ W → m.core.get r = c.get r
  ram : ∀ x, x ≠ ao c → m.ram x = bProRam c M0 x

/-- At the epilogue, with the count in s3. -/
structure EpiAt (c : Core) (M0 : Word → BitVec 8) (m : Machine) : Prop where
  pc : m.core.pc = 0x80009986
  mid : Mid c M0 m
  count : (m.core.get 19).toNat = 0 ∨
    (1 ≤ (m.core.get 19).toNat ∧ (m.core.get 19).toNat ≤ (c.get 12).toNat ∧ (m.core.get 19).toNat ≤ 16)

theorem fp_nat (c : Core) (h : 0x80029bc8 + 0x50 ≤ (c.get 2).toNat) : (fp c).toNat = (c.get 2).toNat - 0x30 := by
  unfold fp; simp only [alu_add]; bv_omega

theorem ao_nat (c : Core) (h : 0x80029bc8 + 0x50 ≤ (c.get 2).toNat) : (ao c).toNat = (c.get 2).toNat - 0x41 := by
  unfold ao; simp only [alu_add]; have := fp_nat c h; bv_omega

theorem fpo_nat (c : Core) (h : 0x80029bc8 + 0x50 ≤ (c.get 2).toNat) (o : Word) (ho : o.toNat < 0x30) :
    (fp c + o).toNat = (c.get 2).toNat - 0x30 + o.toNat := by
  have := fp_nat c h; bv_omega

theorem rd_fp (c : Core) (h : 0x80029bc8 + 0x50 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000) :
    ∀ (ram : Word → BitVec 8) (o1 o2 v : Word), o1.toNat + 4 ≤ 0x30 → o2.toNat + 4 ≤ 0x30 →
      (o2.toNat + 4 ≤ o1.toNat ∨ o1.toNat + 4 ≤ o2.toNat) →
      ramRead (ramWrite ram (fp c + o1) v .w) (fp c + o2) .w = ramRead ram (fp c + o2) .w := by
  intro ram o1 o2 v h1 h2 h3
  have F := fpo_nat c h.1
  have := h.2
  exact rd_wr_other _ _ _ _ (by rw [F o1 (by omega)]; omega) (by rw [F o2 (by omega)]; omega)
    (by rw [F o1 (by omega), F o2 (by omega)]; omega)

theorem wr_fp (c : Core) (h : 0x80029bc8 + 0x50 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000) (x : Word)
    (hx : ¬ ((fp c).toNat ≤ x.toNat ∧ x.toNat < (fp c).toNat + 0x30)) :
    ∀ (ram : Word → BitVec 8) (o v : Word), o.toNat + 4 ≤ 0x30 → ramWrite ram (fp c + o) v .w x = ram x := by
  intro ram o v h1
  have F := fpo_nat c h.1
  have := h.2
  have := fp_nat c h.1
  exact wr_byte_other _ _ _ _ (by rw [F o (by omega)]; omega) (by rw [F o (by omega)]; omega)

/-- The prologue's saves, read back. -/
theorem slot (c : Core) (M0 : Word → BitVec 8) (h : 0x80029bc8 + 0x50 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000)
    (o : Word) (r : Reg) (hm : (o, r) ∈ [(0x2c#32, (1 : Reg)), (0x28#32, 8), (0x24#32, 9), (0x20#32, 18),
      (0x1c#32, 19), (0x18#32, 20), (0x14#32, 21), (0x10#32, 22), (0x0c#32, 23)]) :
    ramRead (bProRam c M0) (fp c + o) .w = c.get r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  unfold bProRam
  rw [show alu .add (c.get 2) 0xffffffd0#32 = fp c from rfl]
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp (disch := decide) only [rd_fp c h, ramRead_ramWrite_w]

/-- **The epilogue.** -/
theorem epi (c : Core) (M0 : Word → BitVec 8) (E : SendEnv ⟨c, M0⟩) (m : Machine) (h : EpiAt c M0 m) :
    Lands B img (SendPost ⟨c, M0⟩) m := by
  obtain ⟨e, M⟩ := m
  have hs : 0x80029bc8 + 0x50 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000 := E.sp
  have hs1 := hs.1
  have hs2 := hs.2
  have hA : (c.get 2).toNat % 4 = 0 := E.spAl
  have F := fpo_nat c hs.1
  have A := ao_nat c hs.1
  have e2 : e.get 2 = fp c := h.mid.sp
  have sl : ∀ o r, (o, r) ∈ [(0x2c#32, (1 : Reg)), (0x28#32, 8), (0x24#32, 9), (0x20#32, 18),
      (0x1c#32, 19), (0x18#32, 20), (0x14#32, 21), (0x10#32, 22), (0x0c#32, 23)] → o.toNat < 0x30 →
      ramRead M (e.get 2 + o) .w = c.get r := by
    intro o r hm ho
    rw [e2, ← slot c M0 hs o r hm]
    refine ramRead_w_congr _ fun k hk => h.mid.ram _ fun eq => ?_
    have := congrArg BitVec.toNat eq
    rw [A, BitVec.toNat_add, F o ho, BitVec.toNat_ofNat] at this
    omega
  have al : ∀ o : Word, o.toNat < 0x30 → o.toNat % 4 = 0 → (e.get 2 + o).toNat % 4 = 0 := by
    intro o ho h4; rw [e2, F o ho]; omega
  have inr : ∀ o : Word, o.toNat < 0x30 → o.toNat + 4 ≤ 0x30 → B.inRam (e.get 2 + o) 4 = true := by
    intro o ho h4; rw [e2, B_ram, F o ho]; omega
  have hra : (ramRead M (e.get 2 + 0x0000002c#32) .w).getLsbD 0 = false := by
    rw [sl 0x2c#32 1 (by simp) (by decide)]; exact E.ra
  have run := bEpi e M h.pc h.mid.quiet
    (al _ (by decide) (by decide)) (inr _ (by decide) (by decide))
    (al _ (by decide) (by decide)) (inr _ (by decide) (by decide))
    (al _ (by decide) (by decide)) (inr _ (by decide) (by decide))
    (al _ (by decide) (by decide)) (inr _ (by decide) (by decide))
    (al _ (by decide) (by decide)) (inr _ (by decide) (by decide))
    (al _ (by decide) (by decide)) (inr _ (by decide) (by decide))
    (al _ (by decide) (by decide)) (inr _ (by decide) (by decide))
    (al _ (by decide) (by decide)) (inr _ (by decide) (by decide))
    (al _ (by decide) (by decide)) (inr _ (by decide) (by decide)) hra
  refine lands_of_qrun run ⟨?_, Quiet.of_sameCsr (bEpiCsr e M) h.mid.quiet, ?_, ?_, ?_, ?_⟩
  · show (bEpiCore e M).pc = c.get 1
    simp only [bEpiCore, Core.goto_pc]; exact sl 0x2c#32 1 (by simp) (by decide)
  · show (bEpiCore e M).get 2 = c.get 2
    simp [bEpiCore, Core.wr_get_ne, Core.wr_get_self, e2, alu_add, fp]; bv_omega
  · intro r hr
    show (bEpiCore e M).get r = c.get r
    have hr' : r.val ∈ [0, 1, 2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by
      have := r.isLt
      simp only [callerSaved, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega
    have kp : ∀ r : Reg, r.val ∉ W → e.get r = c.get r := h.mid.regs
    obtain ⟨k, hk⟩ := r
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · rfl
    · simp [bEpiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x2c#32 1 (by simp) (by decide)
    · simp [bEpiCore, Core.wr_get_ne, Core.wr_get_self, e2, alu_add, fp]; bv_omega
    · simp [bEpiCore, Core.wr_get_ne]; exact kp 3 (by decide)
    · simp [bEpiCore, Core.wr_get_ne]; exact kp 4 (by decide)
    · simp [bEpiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x28#32 8 (by simp) (by decide)
    · simp [bEpiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x24#32 9 (by simp) (by decide)
    · simp [bEpiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x20#32 18 (by simp) (by decide)
    · simp [bEpiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x1c#32 19 (by simp) (by decide)
    · simp [bEpiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x18#32 20 (by simp) (by decide)
    · simp [bEpiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x14#32 21 (by simp) (by decide)
    · simp [bEpiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x10#32 22 (by simp) (by decide)
    · simp [bEpiCore, Core.wr_get_ne, Core.wr_get_self]; exact sl 0x0c#32 23 (by simp) (by decide)
    · simp [bEpiCore, Core.wr_get_ne]; exact kp 24 (by decide)
    · simp [bEpiCore, Core.wr_get_ne]; exact kp 25 (by decide)
    · simp [bEpiCore, Core.wr_get_ne]; exact kp 26 (by decide)
    · simp [bEpiCore, Core.wr_get_ne]; exact kp 27 (by decide)
  · intro x hx
    have hx : ¬ ((c.get 2).toNat - 0x50 ≤ x.toNat ∧ x.toNat < (c.get 2).toNat) := hx
    show M x = M0 x
    have hfx : ¬ ((fp c).toNat ≤ x.toNat ∧ x.toNat < (fp c).toNat + 0x30) := by
      rw [fp_nat c hs1]; omega
    refine (h.mid.ram x (fun eq => hx (by rw [eq, A]; omega))).trans ?_
    unfold bProRam
    rw [show alu .add (c.get 2) 0xffffffd0#32 = fp c from rfl]
    simp (disch := decide) only [wr_fp c hs x hfx]
  · show ((bEpiCore e M).get 10).toNat = 0 ∨ _
    simp only [bEpiCore, Core.wr_get_ne _ _ _ _ _ (show (10 : Reg) ≠ 1 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (10 : Reg) ≠ 2 by decide), Core.wr_get_ne _ _ _ _ _ (show (10 : Reg) ≠ 8 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (10 : Reg) ≠ 9 by decide), Core.wr_get_ne _ _ _ _ _ (show (10 : Reg) ≠ 18 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (10 : Reg) ≠ 19 by decide), Core.wr_get_ne _ _ _ _ _ (show (10 : Reg) ≠ 20 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (10 : Reg) ≠ 21 by decide), Core.wr_get_ne _ _ _ _ _ (show (10 : Reg) ≠ 22 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (10 : Reg) ≠ 23 by decide), Core.goto_get,
      Core.wr_get_self _ _ _ _ (show (10 : Reg).val ≠ 0 by decide), alu_add]
    rw [show (0 : Word) + e.get 19 = e.get 19 from BitVec.zero_add _]
    exact h.count

/-- A step of `Mid`: the core keeps sp and every register outside `W`, the RAM changes only at the
assert_offset byte. -/
theorem mid_of {c : Core} {M0 : Word → BitVec 8} {e e' : Core} {M M' : Word → BitVec 8}
    (h : Mid c M0 ⟨e, M⟩) (q : Quiet e') (h2 : e'.get 2 = e.get 2)
    (hr : ∀ r : Reg, r.val ∉ W → e'.get r = e.get r) (hm : ∀ x, x ≠ ao c → M' x = M x) :
    Mid c M0 ⟨e', M'⟩ :=
  ⟨q, h2.trans h.sp, fun r hn => (hr r hn).trans (h.regs r hn), fun x hx => (hm x hx).trans (h.ram x hx)⟩

/-- assert_offset's byte store, at sp = fp: the only RAM change. -/
theorem ao_other {c : Core} {e : Core} (M : Word → BitVec 8) (v : Word) (h2 : e.get 2 = fp c) :
    ∀ x, x ≠ ao c → ramWrite M (alu .add (e.get 2) 0xffffffe0#32 + 0x0000000f#32) v .b x = M x := by
  intro x hx; rw [h2]; exact ramPut_ne _ hx

theorem ao_in (c : Core) (h : 0x80029bc8 + 0x50 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000) :
    B.inRam (ao c) 1 = true := by
  rw [B_ram, ao_nat c h.1]; omega

/-- The THR loop at 0x8000996c with k of n bytes left. -/
structure LoopAt (c : Core) (M0 : Word → BitVec 8) (n k : Nat) (m : Machine) : Prop where
  pc : m.core.pc = 0x8000996c
  mid : Mid c M0 m
  cnt : m.core.get 8 = BitVec.ofNat 32 k
  n19 : m.core.get 19 = BitVec.ofNat 32 n
  base : m.core.get 22 = 0x10000000
  buf : m.core.get 23 = c.get 11 + BitVec.ofNat 32 (n - k)

/-- **The THR loop**: k more byte stores (device-write events), then the epilogue. -/
theorem loop (c : Core) (M0 : Word → BitVec 8) (E : SendEnv ⟨c, M0⟩) (n : Nat) (hn1 : 1 ≤ n) (hn : n ≤ 16)
    (hl : n ≤ (c.get 12).toNat) :
    ∀ k, 1 ≤ k → k ≤ n → ∀ m, LoopAt c M0 n k m → Lands B img (EpiAt c M0) m := by
  have hs : 0x80029bc8 + 0x50 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000 := E.sp
  have hb : (c.get 12).toNat = 0 ∨ B.inRam (c.get 11) (c.get 12).toNat = true := E.buf
  have hbuf : B.inRam (c.get 11) (c.get 12).toNat = true := by
    rcases hb with hb | hb
    · omega
    · exact hb
  rw [B_ram] at hbuf
  intro k
  induction k with
  | zero => intro h; omega
  | succ j ih =>
  intro _ hk ⟨e, M⟩ L
  have e2 : e.get 2 = fp c := L.mid.sp
  have e23 : e.get 23 = c.get 11 + BitVec.ofNat 32 (n - (j + 1)) := L.buf
  have r1 := bByte e M L.pc L.mid.quiet (Nat.mod_one _)
    (by rw [e23, B_ram]; constructor <;> bv_omega)
    (Nat.mod_one _) (by rw [e2]; exact ao_in c hs)
  have cs := bByteCsr e M
  have g2 : (bByteCore e M).get 2 = e.get 2 := by
    simp [bByteCore, Core.wr_get_ne, Core.wr_get_self, alu_add]; bv_omega
  have gW : ∀ r : Reg, r.val ∉ W → (bByteCore e M).get r = e.get r := fun r hr => by
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := notW hr
    simp [bByteCore, Core.wr_get_ne, n1, n2, n3, n4, n5, n6, n7, n9, n10, n11, n12, n13]
  have g8 : (bByteCore e M).get 8 = alu .add (e.get 8) 0xffffffff#32 := by
    simp [bByteCore, Core.wr_get_ne, Core.wr_get_self]
  have g19 : (bByteCore e M).get 19 = e.get 19 := by simp [bByteCore, Core.wr_get_ne]
  have g22 : (bByteCore e M).get 22 = e.get 22 := by simp [bByteCore, Core.wr_get_ne]
  have g23 : (bByteCore e M).get 23 = alu .add (e.get 23) 0x00000001#32 := by
    simp [bByteCore, Core.wr_get_ne, Core.wr_get_self]
  have hR : ∀ x, x ≠ ao c → bByteRam e M x = M x := ao_other (c := c) M (alu .add 0 0x00000000#32) e2
  have pK : (bByteCore e M).pc = 0x80009980 := rfl
  generalize bByteCore e M = K at r1 cs g2 gW g8 g19 g22 g23 pK
  generalize bByteRam e M = R at r1 hR
  have qK : Quiet K := Quiet.of_sameCsr cs L.mid.quiet
  have MK : Mid c M0 ⟨K, R⟩ := mid_of L.mid qK g2 gW hR
  refine lands_of_qrun_lands r1 ?_
  refine lands_sb_dev (rs1 := 22) (rs2 := 9) (off := 0x00000000#32) (len := 0x00000004#32)
    (by rw [pK]; decide) (by rw [pK]; exact f80009980) (by rw [g22, L.base]; rfl) (by decide) thr_dev rfl rfl qK ?_
  have K8 : (K.goto (K.pc + 0x00000004#32)).get 8 = BitVec.ofNat 32 j := by
    rw [Core.goto_get, g8, L.cnt, alu_add]; bv_omega
  have M2 : Mid c M0 ⟨K.goto (K.pc + 0x00000004#32), R⟩ :=
    mid_of MK (Quiet.of_sameCsr (Core.sameCsr_goto _ _) qK) rfl (fun _ _ => rfl) (fun _ _ => rfl)
  have p2 : (K.goto (K.pc + 0x00000004#32)).pc = 0x80009984 := by rw [Core.goto_pc, pK]; rfl
  by_cases hj : j = 0
  · subst hj
    have r2 := bDone _ R p2 M2.quiet (by rw [K8]; rfl)
    refine lands_of_qrun r2 ⟨rfl, mid_of M2 (Quiet.of_sameCsr (Core.sameCsr_goto _ _) M2.quiet) rfl
      (fun _ _ => rfl) (fun _ _ => rfl), ?_⟩
    simp only [bDoneCore, Core.goto_get, g19, L.n19, BitVec.toNat_ofNat]
    right; refine ⟨?_, ?_, ?_⟩ <;> omega
  · have r2 := bNext _ R p2 M2.quiet (by
      rw [K8]; simp only [taken, bne_iff_ne, ne_eq]; intro e
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this
      rw [show (0 : Word).toNat = 0 from rfl] at this; omega)
    refine lands_of_qrun_lands r2 (ih (by omega) (by omega) _ ⟨rfl, mid_of M2
      (Quiet.of_sameCsr (Core.sameCsr_goto _ _) M2.quiet) rfl (fun _ _ => rfl) (fun _ _ => rfl), ?_, ?_, ?_, ?_⟩)
    · exact K8
    · show (K.goto (K.pc + 0x00000004#32)).get 19 = _; rw [Core.goto_get, g19]; exact L.n19
    · show (K.goto (K.pc + 0x00000004#32)).get 22 = _; rw [Core.goto_get, g22]; exact L.base
    · show (K.goto (K.pc + 0x00000004#32)).get 23 = _
      rw [Core.goto_get, g23, e23, alu_add, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem ltu16 (x : Word) : taken .ltu x (alu .add 0 0x00000010#32) = decide (x.toNat < 16) := by
  rw [show (alu .add 0 0x00000010#32 : Word) = 0x00000010#32 from by decide]
  simp [taken, BitVec.ult]

/-- The count at 0x8000994c. -/
structure CntAt (c : Core) (M0 : Word → BitVec 8) (m : Machine) : Prop where
  pc : m.core.pc = 0x8000994c
  mid : Mid c M0 m
  s2 : m.core.get 18 = c.get 10
  s3 : m.core.get 19 = c.get 12
  len : (c.get 12).toNat ≠ 0
  s6 : m.core.get 22 = 0x10000000
  s7 : m.core.get 23 = c.get 11

/-- **The count**: n = min(len, 16), or 1 when the FIFO-size byte is 0xff; then the loop. -/
theorem cnt (c : Core) (M0 : Word → BitVec 8) (E : SendEnv ⟨c, M0⟩) (m : Machine) (h : CntAt c M0 m) :
    Lands B img (EpiAt c M0) m := by
  obtain ⟨e, M⟩ := m
  have hsi : 0x80029bc8 ≤ (c.get 10).toNat ∧ (c.get 10).toNat + 0x21 ≤ 0x81000000 := E.selfIn
  have e18 : e.get 18 = c.get 10 := h.s2
  have e19 : e.get 19 = c.get 12 := h.s3
  have hin : B.inRam (e.get 18 + 0x00000017#32) 1 = true := by rw [e18, B_ram]; constructor <;> bv_omega
  have fin : ∀ (e' : Core) (n : Nat), 1 ≤ n → n ≤ 16 → n ≤ (c.get 12).toNat → e'.pc = 0x8000996c → Quiet e' →
      e'.get 2 = e.get 2 → (∀ r : Reg, r.val ∉ W → e'.get r = e.get r) → e'.get 8 = BitVec.ofNat 32 n →
      e'.get 19 = BitVec.ofNat 32 n → e'.get 22 = e.get 22 → e'.get 23 = e.get 23 →
      Lands B img (EpiAt c M0) ⟨e', M⟩ := by
    intro e' n h1 h2 h3 hp q g2 gW g8 g19 g22 g23
    refine loop c M0 E n h1 h2 h3 n h1 (Nat.le_refl _) _ ⟨hp, mid_of h.mid q g2 gW (fun _ _ => rfl), g8, g19,
      g22.trans h.s6, ?_⟩
    rw [g23, h.s7, Nat.sub_self]; exact (BitVec.add_zero _).symm
  have hl0 : (c.get 12).toNat ≠ 0 := h.len
  have hlen : (c.get 12) = BitVec.ofNat 32 (c.get 12).toNat := by simp
  by_cases hlt : (c.get 12).toNat < 16 <;>
    by_cases hff : extend .b false (ramRead M (e.get 18 + 0x00000017#32) .b) = alu .add 0 0x000000ff#32
  · have r := bCnt2 e M h.pc h.mid.quiet (Nat.mod_one _) hin (by rw [ltu16, e19]; simp only [decide_eq_true_iff]; omega)
      (by simp [taken, hff])
    refine lands_of_qrun_lands r (fin _ 1 (Nat.le_refl _) (by decide) (by omega) rfl (Quiet.of_sameCsr (bCnt2Csr e M) h.mid.quiet) ?_ ?_ ?_ ?_ ?_ ?_)
    · simp [bCnt2Core, Core.wr_get_ne]
    · intro r hr
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := notW hr
      simp [bCnt2Core, Core.wr_get_ne, n1, n3, n5, n6, n8, n9]
    · simp [bCnt2Core, Core.wr_get_ne, Core.wr_get_self, alu_add]
    · simp [bCnt2Core, Core.wr_get_ne, Core.wr_get_self, alu_add]
    · simp [bCnt2Core, Core.wr_get_ne]
    · simp [bCnt2Core, Core.wr_get_ne]
  · have r := bCnt3 e M h.pc h.mid.quiet (Nat.mod_one _) hin (by rw [ltu16, e19]; simp only [decide_eq_true_iff]; omega)
      (by simp only [taken, bne_iff_ne, ne_eq]; exact hff)
    refine lands_of_qrun_lands r (fin _ (c.get 12).toNat (by omega) (by omega) (Nat.le_refl _) rfl (Quiet.of_sameCsr (bCnt3Csr e M) h.mid.quiet) ?_ ?_ ?_ ?_ ?_ ?_)
    · simp [bCnt3Core, Core.wr_get_ne]
    · intro r hr
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := notW hr
      simp [bCnt3Core, Core.wr_get_ne, n1, n3, n5, n6, n8, n9]
    · simp [bCnt3Core, Core.wr_get_ne, Core.wr_get_self, alu_add]; exact e19
    · simp [bCnt3Core, Core.wr_get_ne, Core.wr_get_self, alu_add]; exact e19
    · simp [bCnt3Core, Core.wr_get_ne]
    · simp [bCnt3Core, Core.wr_get_ne]
  · have r := bCnt0 e M h.pc h.mid.quiet (Nat.mod_one _) hin (by rw [ltu16, e19]; simp only [decide_eq_false_iff_not]; omega)
      (by simp [taken, hff])
    refine lands_of_qrun_lands r (fin _ 1 (Nat.le_refl _) (by decide) (by omega) rfl (Quiet.of_sameCsr (bCnt0Csr e M) h.mid.quiet) ?_ ?_ ?_ ?_ ?_ ?_)
    · simp [bCnt0Core, Core.wr_get_ne]
    · intro r hr
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := notW hr
      simp [bCnt0Core, Core.wr_get_ne, n1, n3, n5, n6, n8, n9]
    · simp [bCnt0Core, Core.wr_get_ne, Core.wr_get_self, alu_add]
    · simp [bCnt0Core, Core.wr_get_ne, Core.wr_get_self, alu_add]
    · simp [bCnt0Core, Core.wr_get_ne]
    · simp [bCnt0Core, Core.wr_get_ne]
  · have r := bCnt1 e M h.pc h.mid.quiet (Nat.mod_one _) hin (by rw [ltu16, e19]; simp only [decide_eq_false_iff_not]; omega)
      (by simp only [taken, bne_iff_ne, ne_eq]; exact hff)
    refine lands_of_qrun_lands r (fin _ 16 (by decide) (by decide) (by omega) rfl (Quiet.of_sameCsr (bCnt1Csr e M) h.mid.quiet) ?_ ?_ ?_ ?_ ?_ ?_)
    · simp [bCnt1Core, Core.wr_get_ne]
    · intro r hr
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := notW hr
      simp [bCnt1Core, Core.wr_get_ne, n1, n3, n5, n6, n8, n9]
    · simp [bCnt1Core, Core.wr_get_ne, Core.wr_get_self, alu_add]
    · simp [bCnt1Core, Core.wr_get_ne, Core.wr_get_self, alu_add]
    · simp [bCnt1Core, Core.wr_get_ne]
    · simp [bCnt1Core, Core.wr_get_ne]

/-- Facts that hold from the argument moves (0x800098bc) on. -/
structure Gen (c : Core) (M0 : Word → BitVec 8) (m : Machine) : Prop where
  mid : Mid c M0 m
  s2 : m.core.get 18 = c.get 10
  s3 : m.core.get 19 = c.get 12
  len : (c.get 12).toNat ≠ 0
  s7 : m.core.get 23 = c.get 11

theorem gen_of {c : Core} {M0 : Word → BitVec 8} {e e' : Core} {M M' : Word → BitVec 8}
    (h : Gen c M0 ⟨e, M⟩) (q : Quiet e') (h2 : e'.get 2 = e.get 2)
    (hr : ∀ r : Reg, r.val ∉ W → e'.get r = e.get r) (hm : ∀ x, x ≠ ao c → M' x = M x)
    (g18 : e'.get 18 = e.get 18) (g19 : e'.get 19 = e.get 19) (g23 : e'.get 23 = e.get 23) : Gen c M0 ⟨e', M'⟩ :=
  ⟨mid_of h.mid q h2 hr hm, g18.trans h.s2, g19.trans h.s3, h.len, g23.trans h.s7⟩

theorem cnt_of {c : Core} {M0 : Word → BitVec 8} {e : Core} {M : Word → BitVec 8} (h : Gen c M0 ⟨e, M⟩)
    (hp : e.pc = 0x8000994c) (s6 : e.get 22 = 0x10000000) : CntAt c M0 ⟨e, M⟩ :=
  ⟨hp, h.mid, h.s2, h.s3, h.len, s6, h.s7⟩

theorem zero_epi {c : Core} {M0 : Word → BitVec 8} {e : Core} {M : Word → BitVec 8} (h : Mid c M0 ⟨e, M⟩)
    (hp : e.pc = 0x80009986) (h19 : e.get 19 = alu .add 0 0x00000000#32) : EpiAt c M0 ⟨e, M⟩ :=
  ⟨hp, h, .inl (by rw [h19]; rfl)⟩

/-- After the MSR read (0x80009948): CTS clear returns 0, set goes to the count. -/
theorem after_msr (c : Core) (M0 : Word → BitVec 8) (E : SendEnv ⟨c, M0⟩) (e : Core) (M : Word → BitVec 8)
    (G : Gen c M0 ⟨e, M⟩) (hp : e.pc = 0x80009948) (s6 : e.get 22 = 0x10000000) :
    Lands B img (EpiAt c M0) ⟨e, M⟩ := by
  by_cases ht : taken .eq (alu .and (e.get 10) 0x00000010#32) 0 = true
  · have r := bCtsN e M hp G.mid.quiet ht
    refine lands_of_qrun r (zero_epi (mid_of G.mid (Quiet.of_sameCsr (bCtsNCsr e M) G.mid.quiet)
      (by simp [bCtsNCore, Core.wr_get_ne]) (fun r hr => ?_) (fun _ _ => rfl)) rfl
      (by simp [bCtsNCore, Core.wr_get_self]))
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := notW hr
    simp [bCtsNCore, Core.wr_get_ne, n5, n9]
  · have r := bCtsY e M hp G.mid.quiet (Bool.eq_false_iff.mpr ht)
    refine lands_of_qrun_lands r (cnt c M0 E _ (cnt_of (gen_of G (Quiet.of_sameCsr (bCtsYCsr e M) G.mid.quiet)
      (by simp [bCtsYCore, Core.wr_get_ne]) (fun r hr => ?_) (fun _ _ => rfl)
      (by simp [bCtsYCore, Core.wr_get_ne]) (by simp [bCtsYCore, Core.wr_get_ne]) (by simp [bCtsYCore, Core.wr_get_ne]))
      rfl (by simp [bCtsYCore, Core.wr_get_ne, s6])))
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := notW hr
    simp [bCtsYCore, Core.wr_get_ne, n5]

/-- After the MCR read (0x8000991e): loopback goes to the count; otherwise assert_offset(6) and the
MSR read, for every value. -/
theorem after_mcr (c : Core) (M0 : Word → BitVec 8) (E : SendEnv ⟨c, M0⟩) (e : Core) (M : Word → BitVec 8)
    (G : Gen c M0 ⟨e, M⟩) (hp : e.pc = 0x8000991e) (s6 : e.get 22 = 0x10000000) (s4 : e.get 20 = 1)
    (s5 : e.get 21 = 4) : Lands B img (EpiAt c M0) ⟨e, M⟩ := by
  have hs : 0x80029bc8 + 0x50 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000 := E.sp
  have e2 : e.get 2 = fp c := G.mid.sp
  by_cases ht : taken .ne (alu .and (e.get 10) 0x00000010#32) 0 = true
  · have r := bLoop e M hp G.mid.quiet ht
    refine lands_of_qrun_lands r (cnt c M0 E _ (cnt_of (gen_of G (Quiet.of_sameCsr (bLoopCsr e M) G.mid.quiet)
      (by simp [bLoopCore, Core.wr_get_ne]) (fun r hr => ?_) (fun _ _ => rfl)
      (by simp [bLoopCore, Core.wr_get_ne]) (by simp [bLoopCore, Core.wr_get_ne]) (by simp [bLoopCore, Core.wr_get_ne]))
      rfl (by simp [bLoopCore, Core.wr_get_ne, s6])))
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := notW hr
    simp [bLoopCore, Core.wr_get_ne, n5]
  · have r := bMsr e M hp G.mid.quiet (Bool.eq_false_iff.mpr ht) (Nat.mod_one _) (by rw [e2]; exact ao_in c hs)
      (by rw [s4, s5]; decide)
    have cs := bMsrCsr e M
    have pK : (bMsrCore e M).pc = 0x80009944 := rfl
    have g2 : (bMsrCore e M).get 2 = e.get 2 := by
      simp [bMsrCore, Core.wr_get_ne, Core.wr_get_self, alu_add]; bv_omega
    have gW : ∀ r : Reg, r.val ∉ W → (bMsrCore e M).get r = e.get r := fun r hr => by
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := notW hr
      simp [bMsrCore, Core.wr_get_ne, n1, n2, n5, n6, n7, n10, n11]
    have g10 : (bMsrCore e M).get 10 = 0x10000006 := by
      simp [bMsrCore, Core.wr_get_ne, Core.wr_get_self, s4, s5, s6]; decide
    have g18 : (bMsrCore e M).get 18 = e.get 18 := by simp [bMsrCore, Core.wr_get_ne]
    have g19 : (bMsrCore e M).get 19 = e.get 19 := by simp [bMsrCore, Core.wr_get_ne]
    have g22 : (bMsrCore e M).get 22 = e.get 22 := by simp [bMsrCore, Core.wr_get_ne]
    have g23 : (bMsrCore e M).get 23 = e.get 23 := by simp [bMsrCore, Core.wr_get_ne]
    have hR : ∀ x, x ≠ ao c → bMsrRam e M x = M x := ao_other (c := c) M _ e2
    generalize bMsrCore e M = K at r cs pK g2 gW g10 g18 g19 g22 g23
    generalize bMsrRam e M = R at r hR
    have qK : Quiet K := Quiet.of_sameCsr cs G.mid.quiet
    have GK : Gen c M0 ⟨K, R⟩ := gen_of G qK g2 gW hR g18 g19 g23
    refine lands_of_qrun_lands r ?_
    refine lands_lbu_dev (rd := 10) (rs1 := 10) (off := 0x00000000#32) (len := 0x00000004#32)
      (by rw [pK]; decide) (by rw [pK]; exact f80009944) (by rw [g10]; rfl) (by decide) msr_none msr_dev rfl rfl qK
      fun v => ?_
    refine after_msr c M0 E _ R (gen_of GK (Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) qK)
      (Core.wr_get_ne _ _ _ _ _ (by decide)) (fun r hr => Core.wr_get_ne _ _ _ _ _ (notW hr).2.2.2.2.1)
      (fun _ _ => rfl) (Core.wr_get_ne _ _ _ _ _ (by decide)) (Core.wr_get_ne _ _ _ _ _ (by decide))
      (Core.wr_get_ne _ _ _ _ _ (by decide))) (by rw [Core.wr_pc, pK]; rfl)
      (by rw [Core.wr_get_ne _ _ _ _ _ (by decide), g22, s6])

/-- The struct's bytes survive the prologue and the assert_offset stores. -/
theorem selfram (c : Core) (M0 : Word → BitVec 8) (E : SendEnv ⟨c, M0⟩) {m : Machine} (h : Mid c M0 m)
    (x : Word) (h1 : (c.get 10).toNat ≤ x.toNat) (h2 : x.toNat < (c.get 10).toNat + 0x21) : m.ram x = M0 x := by
  have hs : 0x80029bc8 + 0x50 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000 := E.sp
  have sep : (c.get 10).toNat + 0x21 ≤ (c.get 2).toNat - 0x50 ∨ (c.get 2).toNat ≤ (c.get 10).toNat := E.selfSep
  have A := ao_nat c hs.1
  have hfx : ¬ ((fp c).toNat ≤ x.toNat ∧ x.toNat < (fp c).toNat + 0x30) := by rw [fp_nat c hs.1]; omega
  refine (h.ram x fun eq => by rw [eq, A] at h1 h2; omega).trans ?_
  unfold bProRam
  rw [show alu .add (c.get 2) 0xffffffd0#32 = fp c from rfl]
  simp (disch := decide) only [wr_fp c hs x hfx]

theorem self_off (c : Core) (h : 0x80029bc8 ≤ (c.get 10).toNat ∧ (c.get 10).toNat + 0x21 ≤ 0x81000000) (o : Word)
    (ho : o.toNat < 0x21) : (c.get 10 + o).toNat = (c.get 10).toNat + o.toNat := by bv_omega

/-- After the LSR read (0x800098f4): THR busy returns 0; otherwise, without flow control, the count;
with it, assert_offset(4) and the MCR read, for every value. -/
theorem after_lsr (c : Core) (M0 : Word → BitVec 8) (E : SendEnv ⟨c, M0⟩) (e : Core) (M : Word → BitVec 8)
    (G : Gen c M0 ⟨e, M⟩) (hp : e.pc = 0x800098f4) (s6 : e.get 22 = 0x10000000) (s4 : e.get 20 = 1)
    (s5 : e.get 21 = 4) : Lands B img (EpiAt c M0) ⟨e, M⟩ := by
  have hs : 0x80029bc8 + 0x50 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000 := E.sp
  have hsi : 0x80029bc8 ≤ (c.get 10).toNat ∧ (c.get 10).toNat + 0x21 ≤ 0x81000000 := E.selfIn
  have e2 : e.get 2 = fp c := G.mid.sp
  have e18 : e.get 18 = c.get 10 := G.s2
  have hin : B.inRam (e.get 18 + 0x00000015#32) 1 = true := by
    rw [e18, B_ram, self_off c hsi _ (by decide)]; simp only [BitVec.toNat_ofNat]; omega
  by_cases ht : taken .ne (alu .and (e.get 10) 0x00000020#32) 0 = true
  case neg =>
    have r := bFull e M hp G.mid.quiet (Bool.eq_false_iff.mpr ht)
    refine lands_of_qrun r (zero_epi (mid_of G.mid (Quiet.of_sameCsr (bFullCsr e M) G.mid.quiet)
      (by simp [bFullCore, Core.wr_get_ne]) (fun r hr => ?_) (fun _ _ => rfl)) rfl
      (by simp [bFullCore, Core.wr_get_self]))
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := notW hr
    simp [bFullCore, Core.wr_get_ne, n5, n9]
  by_cases hz : taken .eq (extend .b false (ramRead M (e.get 18 + 0x00000015#32) .b)) 0 = true
  · have r := bNoFc e M hp G.mid.quiet ht (Nat.mod_one _) hin hz
    refine lands_of_qrun_lands r (cnt c M0 E _ (cnt_of (gen_of G (Quiet.of_sameCsr (bNoFcCsr e M) G.mid.quiet)
      (by simp [bNoFcCore, Core.wr_get_ne]) (fun r hr => ?_) (fun _ _ => rfl)
      (by simp [bNoFcCore, Core.wr_get_ne]) (by simp [bNoFcCore, Core.wr_get_ne]) (by simp [bNoFcCore, Core.wr_get_ne]))
      rfl (by simp [bNoFcCore, Core.wr_get_ne, s6])))
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := notW hr
    simp [bNoFcCore, Core.wr_get_ne, n5]
  · have r := bMcr e M hp G.mid.quiet ht (Nat.mod_one _) hin (Bool.eq_false_iff.mpr hz) (Nat.mod_one _)
      (by rw [e2]; exact ao_in c hs)
    have cs := bMcrCsr e M
    have pK : (bMcrCore e M).pc = 0x8000991a := rfl
    have g2 : (bMcrCore e M).get 2 = e.get 2 := by
      simp [bMcrCore, Core.wr_get_ne, Core.wr_get_self, alu_add]; bv_omega
    have gW : ∀ r : Reg, r.val ∉ W → (bMcrCore e M).get r = e.get r := fun r hr => by
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := notW hr
      simp [bMcrCore, Core.wr_get_ne, n1, n2, n5, n6, n7]
    have g10 : (bMcrCore e M).get 10 = 0x10000004 := by
      simp [bMcrCore, Core.wr_get_ne, Core.wr_get_self, s5, s6]; decide
    have g18 : (bMcrCore e M).get 18 = e.get 18 := by simp [bMcrCore, Core.wr_get_ne]
    have g19 : (bMcrCore e M).get 19 = e.get 19 := by simp [bMcrCore, Core.wr_get_ne]
    have g20 : (bMcrCore e M).get 20 = e.get 20 := by simp [bMcrCore, Core.wr_get_ne]
    have g21 : (bMcrCore e M).get 21 = e.get 21 := by simp [bMcrCore, Core.wr_get_ne]
    have g22 : (bMcrCore e M).get 22 = e.get 22 := by simp [bMcrCore, Core.wr_get_ne]
    have g23 : (bMcrCore e M).get 23 = e.get 23 := by simp [bMcrCore, Core.wr_get_ne]
    have hR : ∀ x, x ≠ ao c → bMcrRam e M x = M x := ao_other (c := c) M _ e2
    generalize bMcrCore e M = K at r cs pK g2 gW g10 g18 g19 g20 g21 g22 g23
    generalize bMcrRam e M = R at r hR
    have qK : Quiet K := Quiet.of_sameCsr cs G.mid.quiet
    have GK : Gen c M0 ⟨K, R⟩ := gen_of G qK g2 gW hR g18 g19 g23
    refine lands_of_qrun_lands r ?_
    refine lands_lbu_dev (rd := 10) (rs1 := 10) (off := 0x00000000#32) (len := 0x00000004#32)
      (by rw [pK]; decide) (by rw [pK]; exact f8000991a) (by rw [g10]; rfl) (by decide) mcr_none mcr_dev rfl rfl qK
      fun v => ?_
    refine after_mcr c M0 E _ R (gen_of GK (Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) qK)
      (Core.wr_get_ne _ _ _ _ _ (by decide)) (fun r hr => Core.wr_get_ne _ _ _ _ _ (notW hr).2.2.2.2.1)
      (fun _ _ => rfl) (Core.wr_get_ne _ _ _ _ _ (by decide)) (Core.wr_get_ne _ _ _ _ _ (by decide))
      (Core.wr_get_ne _ _ _ _ _ (by decide))) (by rw [Core.wr_pc, pK]; rfl)
      (by rw [Core.wr_get_ne _ _ _ _ _ (by decide), g22, s6]) (by rw [Core.wr_get_ne _ _ _ _ _ (by decide), g20, s4])
      (by rw [Core.wr_get_ne _ _ _ _ _ (by decide), g21, s5])

/-- **`send_bytes`**, every behaviour, every UART value. -/
theorem send_bytes (m₀ : Machine) (E : SendEnv m₀) : Lands B img (SendPost m₀) m₀ := by
  obtain ⟨c, M0⟩ := m₀
  have hs : 0x80029bc8 + 0x50 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000 := E.sp
  have hsi : 0x80029bc8 ≤ (c.get 10).toNat ∧ (c.get 10).toNat + 0x21 ≤ 0x81000000 := E.selfIn
  have hA : (c.get 2).toNat % 4 = 0 := E.spAl
  have F := fpo_nat c hs.1
  have h1 := hs.1
  have h2 := hs.2
  have al : ∀ o : Word, o.toNat < 0x30 → o.toNat % 4 = 0 → (alu .add (c.get 2) 0xffffffd0#32 + o).toNat % 4 = 0 := by
    intro o ho h4; rw [show alu .add (c.get 2) 0xffffffd0#32 = fp c from rfl, F o ho]; omega
  have inr : ∀ o : Word, o.toNat < 0x30 → o.toNat + 4 ≤ 0x30 →
      B.inRam (alu .add (c.get 2) 0xffffffd0#32 + o) 4 = true := by
    intro o ho h4; rw [show alu .add (c.get 2) 0xffffffd0#32 = fp c from rfl, B_ram, F o ho]; omega
  have r0 := bPro c M0 E.pc E.quiet
    (al _ (by decide) (by decide)) (inr _ (by decide) (by decide))
    (al _ (by decide) (by decide)) (inr _ (by decide) (by decide))
    (al _ (by decide) (by decide)) (inr _ (by decide) (by decide))
    (al _ (by decide) (by decide)) (inr _ (by decide) (by decide))
    (al _ (by decide) (by decide)) (inr _ (by decide) (by decide))
    (al _ (by decide) (by decide)) (inr _ (by decide) (by decide))
    (al _ (by decide) (by decide)) (inr _ (by decide) (by decide))
    (al _ (by decide) (by decide)) (inr _ (by decide) (by decide))
    (al _ (by decide) (by decide)) (inr _ (by decide) (by decide))
  refine lands_of_qrun_lands r0 (lands_seq (epi c M0 E) ?_)
  have q0 : Quiet (bProCore c M0) := Quiet.of_sameCsr (bProCsr c M0) E.quiet
  have P2 : (bProCore c M0).get 2 = fp c := by simp [bProCore, Core.wr_get_self]; rfl
  have Pr : ∀ r : Reg, r ≠ 2 → (bProCore c M0).get r = c.get r := fun r hr => by
    simp [bProCore, Core.wr_get_ne, hr]
  have M1 : Mid c M0 ⟨bProCore c M0, bProRam c M0⟩ :=
    ⟨q0, P2, fun r hr => Pr r (notW hr).2.1, fun _ _ => rfl⟩
  have pP : (bProCore c M0).pc = 0x800098ba := rfl
  generalize bProCore c M0 = e at q0 P2 Pr M1 pP
  generalize hM : bProRam c M0 = M at M1
  have e10 : e.get 10 = c.get 10 := Pr 10 (by decide)
  have e11 : e.get 11 = c.get 11 := Pr 11 (by decide)
  have e12 : e.get 12 = c.get 12 := Pr 12 (by decide)
  by_cases hz : taken .eq (e.get 12) 0 = true
  · have r := bZero e M pP q0 hz
    refine lands_of_qrun r (zero_epi (mid_of M1 (Quiet.of_sameCsr (bZeroCsr e M) q0)
      (by simp [bZeroCore, Core.wr_get_ne]) (fun r hr => ?_) (fun _ _ => rfl)) rfl
      (by simp [bZeroCore, Core.wr_get_self]))
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := notW hr
    simp [bZeroCore, Core.wr_get_ne, n9]
  have hl : (c.get 12).toNat ≠ 0 := by
    intro h0; apply hz; rw [e12]; simp only [taken, beq_iff_eq]; exact BitVec.eq_of_toNat_eq h0
  -- assert_offset(5)
  have r1 := bAo5 e M pP q0 (Bool.eq_false_iff.mpr hz) (Nat.mod_one _) (by rw [P2]; exact ao_in c hs)
  have cs1 := bAo5Csr e M
  have p1 : (bAo5Core e M).pc = 0x800098d4 := rfl
  have g2 : (bAo5Core e M).get 2 = e.get 2 := by
    simp [bAo5Core, Core.wr_get_ne, Core.wr_get_self, alu_add]; bv_omega
  have gW : ∀ r : Reg, r.val ∉ W → (bAo5Core e M).get r = e.get r := fun r hr => by
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := notW hr
    simp [bAo5Core, Core.wr_get_ne, n1, n2, n5, n6, n7, n8, n9, n13]
  have g18 : (bAo5Core e M).get 18 = c.get 10 := by
    simp [bAo5Core, Core.wr_get_ne, Core.wr_get_self, alu_add]; exact e10
  have g19 : (bAo5Core e M).get 19 = c.get 12 := by
    simp [bAo5Core, Core.wr_get_ne, Core.wr_get_self, alu_add]; exact e12
  have g23 : (bAo5Core e M).get 23 = c.get 11 := by
    simp [bAo5Core, Core.wr_get_ne, Core.wr_get_self, alu_add]; exact e11
  have hR : ∀ x, x ≠ ao c → bAo5Ram e M x = M x := ao_other (c := c) M _ P2
  generalize bAo5Core e M = K at r1 cs1 p1 g2 gW g18 g19 g23
  generalize bAo5Ram e M = R at r1 hR
  have qK : Quiet K := Quiet.of_sameCsr cs1 q0
  have GK : Gen c M0 ⟨K, R⟩ := ⟨mid_of M1 qK g2 gW hR, g18, g19, hl, g23⟩
  refine lands_of_qrun_lands r1 ?_
  -- the stride and base, the LSR address
  have sr : ∀ o : Word, o.toNat < 0x21 → R (c.get 10 + o) = M0 (c.get 10 + o) := fun o ho =>
    selfram c M0 E GK.mid _ (by rw [self_off c hsi o ho]; omega) (by rw [self_off c hsi o ho]; omega)
  have hX : extend .b false (ramRead R (K.get 18 + 0x00000020#32) .b) = 1 := by
    rw [g18]; show BitVec.ofNat 32 (R (c.get 10 + 0x00000020#32)).toNat &&& 0xff = 1
    rw [sr _ (by decide)]
    have := E.stride
    rw [show (M0 (c.get 10 + 0x00000020#32)).toNat = 1 from this]; rfl
  have hB : ramRead R (K.get 18 + 0x0000001c#32) .w = 0x10000000 := by
    rw [g18, ← E.base]
    refine ramRead_w_congr _ fun k hk => ?_
    rw [BitVec.add_assoc]
    exact sr _ (by rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega)
  have r2 := bLsr K R p1 qK (Nat.mod_one _)
    (by rw [g18, B_ram, self_off c hsi _ (by decide)]; simp only [BitVec.toNat_ofNat]; omega)
    (by rw [hX]; decide) (by rw [g18]; exact E.selfAl)
    (by rw [g18, B_ram, self_off c hsi _ (by decide)]; simp only [BitVec.toNat_ofNat]; omega)
  have cs2 := bLsrCsr K R
  have p2 : (bLsrCore K R).pc = 0x800098f0 := rfl
  have k10 : (bLsrCore K R).get 10 = 0x10000005 := by
    simp [bLsrCore, Core.wr_get_ne, Core.wr_get_self, hX, hB]; decide
  have k20 : (bLsrCore K R).get 20 = 1 := by simp [bLsrCore, Core.wr_get_ne, Core.wr_get_self, hX]
  have k21 : (bLsrCore K R).get 21 = 4 := by simp [bLsrCore, Core.wr_get_ne, Core.wr_get_self, hX]; decide
  have k22 : (bLsrCore K R).get 22 = 0x10000000 := by simp [bLsrCore, Core.wr_get_ne, Core.wr_get_self, hB]
  have k2 : (bLsrCore K R).get 2 = K.get 2 := by simp [bLsrCore, Core.wr_get_ne]
  have kW : ∀ r : Reg, r.val ∉ W → (bLsrCore K R).get r = K.get r := fun r hr => by
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := notW hr
    simp [bLsrCore, Core.wr_get_ne, n5, n6, n10, n11, n12]
  have k18 : (bLsrCore K R).get 18 = K.get 18 := by simp [bLsrCore, Core.wr_get_ne]
  have k19 : (bLsrCore K R).get 19 = K.get 19 := by simp [bLsrCore, Core.wr_get_ne]
  have k23 : (bLsrCore K R).get 23 = K.get 23 := by simp [bLsrCore, Core.wr_get_ne]
  have kR : bLsrRam K R = R := rfl
  generalize bLsrCore K R = D at r2 cs2 p2 k10 k20 k21 k22 k2 kW k18 k19 k23
  rw [kR] at r2
  have qD : Quiet D := Quiet.of_sameCsr cs2 qK
  have GD : Gen c M0 ⟨D, R⟩ := gen_of GK qD k2 kW (fun _ _ => rfl) k18 k19 k23
  refine lands_of_qrun_lands r2 ?_
  refine lands_lbu_dev (rd := 10) (rs1 := 10) (off := 0x00000000#32) (len := 0x00000004#32)
    (by rw [p2]; decide) (by rw [p2]; exact f800098f0) (by rw [k10]; rfl) (by decide) lsr_none lsr_dev rfl rfl qD
    fun v => ?_
  exact after_lsr c M0 E _ R (gen_of GD (Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) qD)
    (Core.wr_get_ne _ _ _ _ _ (by decide)) (fun r hr => Core.wr_get_ne _ _ _ _ _ (notW hr).2.2.2.2.1)
    (fun _ _ => rfl) (Core.wr_get_ne _ _ _ _ _ (by decide)) (Core.wr_get_ne _ _ _ _ _ (by decide))
    (Core.wr_get_ne _ _ _ _ _ (by decide))) (by rw [Core.wr_pc, p2]; rfl)
    (by rw [Core.wr_get_ne _ _ _ _ _ (by decide), k22]) (by rw [Core.wr_get_ne _ _ _ _ _ (by decide), k20])
    (by rw [Core.wr_get_ne _ _ _ _ _ (by decide), k21])

end E5R.Rmk.Uart
