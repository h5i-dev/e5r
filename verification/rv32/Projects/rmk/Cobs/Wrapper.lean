/-
  `cobs::dec::decode_in_place` (pinned RMK image, 0x8001e006), the function `next` calls:
  a 32-byte frame around a call of `decode_in_place_report` (proved in Decode.lean).

    0x8001e006 addi sp,sp,-32 ; sw ra,28(sp) ; sw s0,24(sp) ; mv s0,a0 ; addi a0,sp,12
    0x8001e010 auipc ra,0 ; jalr ra,0x1e(ra)          (call 0x8001e02e, return to 0x8001e018)
    0x8001e018 lw a0,12(sp) ; lw a1,16(sp) ; lw a2,20(sp) ; addi a0,a0,-1 ; or a0,a0,a1
    0x8001e022 sw a0,0(s0) ; sw a2,4(s0) ; lw ra,28(sp) ; lw s0,24(sp) ; addi sp,sp,32 ; ret

  ABI: a0 = 8-byte result, a1 = buffer, a2 = len. Result word 0 = tag - 1 | word4 of the
  inner result: 0xffffffff on success, the error code otherwise (0 empty, 1 invalid);
  word 1 = the inner word 8 (bytes decoded; for an empty input, whatever the inner slot held).
  Stack: 32 bytes here plus the inner 16: [sp - 48, sp).

  Original e5r code, Apache-2.0.
-/
import Projects.rmk.Cobs.Decode

set_option maxRecDepth 100000

namespace E5R.Rmk.Cobs
open E5R E5R.Rmk E5R.Rmk.CobsFetch

def wEntry : Word := 0x8001e006

/-- The call `decode_in_place(a0 = out, a1 = buf, a2 = len)`. -/
structure WEnv (m : Machine) : Prop where
  pc : m.core.pc = wEntry
  quiet : Quiet m.core
  out : B.inRam (m.core.get 10) 8 = true
  outAl : (m.core.get 10).toNat % 4 = 0
  buf : B.inRam (m.core.get 11) (m.core.get 12).toNat = true
  len : (m.core.get 12).toNat ≤ bufLen
  frame : B.inRam (m.core.get 2 - 48) 48 = true
  spAl : (m.core.get 2).toNat % 4 = 0
  outBuf : (m.core.get 10).toNat + 8 ≤ (m.core.get 11).toNat ∨
    (m.core.get 11).toNat + (m.core.get 12).toNat ≤ (m.core.get 10).toNat
  outFrame : (m.core.get 10).toNat + 8 ≤ (m.core.get 2).toNat - 48 ∨
    (m.core.get 2).toNat ≤ (m.core.get 10).toNat
  bufFrame : (m.core.get 11).toNat + (m.core.get 12).toNat ≤ (m.core.get 2).toNat - 48 ∨
    (m.core.get 2).toNat ≤ (m.core.get 11).toNat
  ra : (m.core.get 1).getLsbD 0 = false

/-- Every return of the wrapper. -/
structure WReturns (m₀ m : Machine) : Prop where
  pc : m.core.pc = m₀.core.get 1
  regs : ∀ r : Reg, r.val ∉ clobbered → m.core.get r = m₀.core.get r
  csr : m.core.sameCsr m₀.core
  ram : ∀ x : Word, ¬ ((m₀.core.get 10).toNat ≤ x.toNat ∧ x.toNat < (m₀.core.get 10).toNat + 8) →
    ¬ ((m₀.core.get 11).toNat ≤ x.toNat ∧ x.toNat < (m₀.core.get 11).toNat + (m₀.core.get 12).toNat) →
    ¬ ((m₀.core.get 2).toNat - 48 ≤ x.toNat ∧ x.toNat < (m₀.core.get 2).toNat) → m.ram x = m₀.ram x

/-- The wrapper's result, from the original bytes. -/
def WRes (m₀ m : Machine) : Prop :=
  let a0 := m₀.core.get 10
  let buf := m₀.core.get 11
  let len := (m₀.core.get 12).toNat
  let orig := bufByte m₀.ram buf
  let n := firstZero orig 0 len
  let r := run orig n (n + 1) 0 []
  (len = 0 → ramRead m.ram a0 .w = 0) ∧
  (0 < len →
    ramRead m.ram a0 .w = (if r.1 = .ok then 0xffffffff#32 else 1) ∧
    ramRead m.ram (a0 + 4) .w = BitVec.ofNat 32 r.2.length ∧
    ∀ j, j < len → bufByte m.ram buf j = if h : j < r.2.length then r.2[j] else orig j)

/-- The core at the inner call's entry 0x8001e02e. -/
def wCore (c : Core) : Core :=
  (((((((c.wr 2 (c.get 2 + 0xffffffe0#32) 0x8001e008).goto 0x8001e00a).goto 0x8001e00c).wr 8
    (0 + c.get 10) 0x8001e00e).wr 10 (c.get 2 + 0xffffffe0#32 + 0xc#32) 0x8001e010).wr 1
    0x8001e010 0x8001e014).set 1 0x8001e018).goto 0x8001e02e

/-- RAM after saving ra and s0. -/
def wRam (c : Core) (R : Word → BitVec 8) : Word → BitVec 8 :=
  ramWrite (ramWrite R (c.get 2 + 0xffffffe0#32 + 0x1c#32) (c.get 1) .w) (c.get 2 + 0xffffffe0#32 + 0x18#32)
    (c.get 8) .w

theorem wCore_get (c : Core) (r : Reg) (h1 : r ≠ 1) (h2 : r ≠ 2) (h8 : r ≠ 8) (h10 : r ≠ 10) :
    (wCore c).get r = c.get r := by
  simp [wCore, Core.wr_get_ne, Core.goto_get, Core.get_set, h1, h2, h8, h10]

theorem wCore_sameCsr (c : Core) : (wCore c).sameCsr c := by
  unfold wCore
  exact (Core.sameCsr_goto _ _).trans ((Core.sameCsr_set (Core.sameCsr_refl _) _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
    ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans
    ((Core.sameCsr_goto _ _).trans (Core.sameCsr_wr _ _ _ _)))))))

/-- The wrapper's frame words: aligned, in model RAM. -/
theorem wslot (sp : Word) (hs : B.inRam (sp - 48) 48 = true) (ha : sp.toNat % 4 = 0) (off : Word)
    (hk : off = 0xc#32 ∨ off = 0x10#32 ∨ off = 0x14#32 ∨ off = 0x18#32 ∨ off = 0x1c#32) :
    (sp + 0xffffffe0#32 + off).toNat % 4 = 0 ∧ B.inRam (sp + 0xffffffe0#32 + off) 4 = true := by
  rw [B_ram] at hs ⊢
  have : (sp - 48).toNat = sp.toNat - 48 := by bv_omega
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> bv_omega

theorem wcall (c : Core) (R : Word → BitVec 8) (h : WEnv ⟨c, R⟩) :
    QRun B img 7 ⟨c, R⟩ ⟨wCore c, wRam c R⟩ := by
  obtain ⟨a1, r1⟩ := wslot _ h.frame h.spAl 0x1c#32 (by simp)
  obtain ⟨a2, r2⟩ := wslot _ h.frame h.spAl 0x18#32 (by simp)
  let sp' := c.get 2 + 0xffffffe0#32
  let c1 := c.wr 2 sp' 0x8001e008
  let c2 := c1.goto 0x8001e00a
  let c3 := c2.goto 0x8001e00c
  let c4 := c3.wr 8 (0 + c.get 10) 0x8001e00e
  let c5 := c4.wr 10 (sp' + 0xc#32) 0x8001e010
  let c6 := c5.wr 1 0x8001e010 0x8001e014
  let R1 := ramWrite R (sp' + 0x1c#32) (c.get 1) .w
  have g1 : ∀ r : Reg, r ≠ 2 → c1.get r = c.get r := fun r hr => by simp [c1, Core.wr_get_ne, hr]
  have v2 : c2.get 2 = sp' := by simp [c2, c1, Core.wr_get_self]
  have s1 : DetStep B img ⟨c, R⟩ ⟨c1, R⟩ := dstep f8001e006 h.pc (by rw [exec_opimm, h.pc]; rfl)
  have s2 : DetStep B img ⟨c1, R⟩ ⟨c2, R1⟩ := by
    have := dstep_store (m := ⟨c1, R⟩) f8001e008 rfl (exec_store _ _ _ _ _ _)
      (by rw [show c1.get 2 = sp' by simp [c1, Core.wr_get_self]]; exact a1)
      (by rw [show c1.get 2 = sp' by simp [c1, Core.wr_get_self]]; exact r1)
    rwa [show c1.get 2 = sp' by simp [c1, Core.wr_get_self], g1 1 (by decide)] at this
  have s3 : DetStep B img ⟨c2, R1⟩ ⟨c3, wRam c R⟩ := by
    have := dstep_store (m := ⟨c2, R1⟩) f8001e00a rfl (exec_store _ _ _ _ _ _)
      (by rw [v2]; exact a2) (by rw [v2]; exact r2)
    rwa [v2, show c2.get 8 = c.get 8 by simp [c2]; exact g1 8 (by decide)] at this
  have s4 : DetStep B img ⟨c3, wRam c R⟩ ⟨c4, wRam c R⟩ := dstep f8001e00c rfl (by
    rw [exec_op]; simp only [alu, Core.get_zero]
    rw [show c3.get 10 = c.get 10 by simp [c3, c2]; exact g1 10 (by decide)]; rfl)
  have s5 : DetStep B img ⟨c4, wRam c R⟩ ⟨c5, wRam c R⟩ := dstep f8001e00e rfl (by
    rw [exec_opimm]; simp only [alu]
    rw [show c4.get 2 = sp' by simp [c4, c3, c2, c1, Core.wr_get_ne, Core.wr_get_self]]; rfl)
  have s6 : DetStep B img ⟨c5, wRam c R⟩ ⟨c6, wRam c R⟩ := dstep f8001e010 rfl (by rw [exec_auipc]; rfl)
  have s7 : DetStep B img ⟨c6, wRam c R⟩ ⟨wCore c, wRam c R⟩ := dstep f8001e014 rfl (by
    rw [exec_jalr]
    rw [show c6.get 1 = 0x8001e010#32 by simp [c6, Core.wr_get_self]]
    rw [show (0x8001e010#32 + 0x1e#32) &&& ~~~1 = 0x8001e02e#32 by decide]
    exact jump_ok _ _ (by decide))
  have q := fun (x : Core) (hx : x.sameCsr c) => Quiet.of_sameCsr hx h.quiet
  have k1 : c1.sameCsr c := Core.sameCsr_wr _ _ _ _
  have k2 : c2.sameCsr c := (Core.sameCsr_goto _ _).trans k1
  have k3 : c3.sameCsr c := (Core.sameCsr_goto _ _).trans k2
  have k4 : c4.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k3
  have k5 : c5.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k4
  have k6 : c6.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans k5
  exact .step h.quiet s1 (.step (q _ k1) s2 (.step (q _ k2) s3 (.step (q _ k3) s4 (.step (q _ k4) s5
    (.step (q _ k5) s6 (.single (q _ k6) s7))))))

/-- The wrapper's epilogue core, from the inner call's return. -/
def wEpi (d : Core) (M : Word → BitVec 8) : Core :=
  let sp' := d.get 2
  let t := ramRead M (sp' + 0xc#32) .w
  let w4 := ramRead M (sp' + 0x10#32) .w
  let w8 := ramRead M (sp' + 0x14#32) .w
  let v := (t + 0xffffffff#32) ||| w4
  let M2 := ramWrite (ramWrite M (d.get 8 + 0x0#32) v .w) (d.get 8 + 0x4#32) w8 .w
  ((((((((d.wr 10 t 0x8001e01a).wr 11 w4 0x8001e01c).wr 12 w8 0x8001e01e).wr 10 (t + 0xffffffff#32)
    0x8001e020).wr 10 v 0x8001e022).goto 0x8001e024).goto 0x8001e026).wr 1 (ramRead M2 (sp' + 0x1c#32) .w)
    0x8001e028 |>.wr 8 (ramRead M2 (sp' + 0x18#32) .w) 0x8001e02a |>.wr 2 (sp' + 0x20#32) 0x8001e02c)
    |>.goto (ramRead M2 (sp' + 0x1c#32) .w)

/-- The wrapper's final RAM. -/
def wEpiRam (d : Core) (M : Word → BitVec 8) : Word → BitVec 8 :=
  let sp' := d.get 2
  ramWrite (ramWrite M (d.get 8 + 0x0#32) ((ramRead M (sp' + 0xc#32) .w + 0xffffffff#32) |||
    ramRead M (sp' + 0x10#32) .w) .w) (d.get 8 + 0x4#32) (ramRead M (sp' + 0x14#32) .w) .w

theorem wepi (d : Core) (M : Word → BitVec 8) (hpc : d.pc = 0x8001e018) (hq : Quiet d)
    (hs : ∀ off : Word, (off = 0xc#32 ∨ off = 0x10#32 ∨ off = 0x14#32 ∨ off = 0x18#32 ∨ off = 0x1c#32) →
      (d.get 2 + off).toNat % 4 = 0 ∧ B.inRam (d.get 2 + off) 4 = true)
    (ho : ∀ off : Word, (off = 0x0#32 ∨ off = 0x4#32) →
      (d.get 8 + off).toNat % 4 = 0 ∧ B.inRam (d.get 8 + off) 4 = true)
    (hra : (ramRead (wEpiRam d M) (d.get 2 + 0x1c#32) .w).getLsbD 0 = false) :
    QRun B img 11 ⟨d, M⟩ ⟨wEpi d M, wEpiRam d M⟩ := by
  let sp' := d.get 2
  let t := ramRead M (sp' + 0xc#32) .w
  let w4 := ramRead M (sp' + 0x10#32) .w
  let w8 := ramRead M (sp' + 0x14#32) .w
  let v := (t + 0xffffffff#32) ||| w4
  let M1 := ramWrite M (d.get 8 + 0x0#32) v .w
  let M2 := wEpiRam d M
  let d1 := d.wr 10 t 0x8001e01a
  let d2 := d1.wr 11 w4 0x8001e01c
  let d3 := d2.wr 12 w8 0x8001e01e
  let d4 := d3.wr 10 (t + 0xffffffff#32) 0x8001e020
  let d5 := d4.wr 10 v 0x8001e022
  let d6 := d5.goto 0x8001e024
  let d7 := d6.goto 0x8001e026
  let d8 := d7.wr 1 (ramRead M2 (sp' + 0x1c#32) .w) 0x8001e028
  let d9 := d8.wr 8 (ramRead M2 (sp' + 0x18#32) .w) 0x8001e02a
  let d10 := d9.wr 2 (sp' + 0x20#32) 0x8001e02c
  have g2 : ∀ e : Core, (e = d1 ∨ e = d2 ∨ e = d3 ∨ e = d4 ∨ e = d5 ∨ e = d6 ∨ e = d7 ∨ e = d8 ∨ e = d9) →
      e.get 2 = sp' := by
    intro e he; rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [d9, d8, d7, d6, d5, d4, d3, d2, d1, Core.wr_get_ne, sp']
  have g8 : ∀ e : Core, (e = d5 ∨ e = d6) → e.get 8 = d.get 8 := by
    intro e he; rcases he with rfl | rfl <;> simp [d6, d5, d4, d3, d2, d1, Core.wr_get_ne]
  have ld : ∀ (e e' : Core) (R : Word → BitVec 8) (p off : Word) (rd : Reg)
      (hd : fetchDecode img p = some (Instr.load .w true rd 2 off, 2)) (hp : e.pc = p) (h2 : e.get 2 = sp')
      (ho : off = 0xc#32 ∨ off = 0x10#32 ∨ off = 0x14#32 ∨ off = 0x18#32 ∨ off = 0x1c#32)
      (he : e' = e.wr rd (ramRead R (sp' + off) .w) (p + 2)) (hal : p.getLsbD 0 = false),
      DetStep B img ⟨e, R⟩ ⟨e', R⟩ := by
    intro e e' R p off rd hd hp h2 ho he hal
    obtain ⟨a, r⟩ := hs off ho
    exact dstep_load hd hp (exec_load _ _ _ _ _ _ _) (by rw [h2]; exact a) (by rw [h2]; exact r)
      (by rw [h2, hp, he, extend_w]) hal
  have s1 : DetStep B img ⟨d, M⟩ ⟨d1, M⟩ := ld d d1 M _ _ 10 f8001e018 hpc rfl (by simp) rfl (by decide)
  have s2 : DetStep B img ⟨d1, M⟩ ⟨d2, M⟩ := ld d1 d2 M _ _ 11 f8001e01a rfl (g2 d1 (by simp)) (by simp) rfl (by decide)
  have s3 : DetStep B img ⟨d2, M⟩ ⟨d3, M⟩ := ld d2 d3 M _ _ 12 f8001e01c rfl (g2 d2 (by simp)) (by simp) rfl (by decide)
  have s4 : DetStep B img ⟨d3, M⟩ ⟨d4, M⟩ := dstep f8001e01e rfl (by
    rw [exec_opimm]; simp only [alu]; rw [show d3.get 10 = t by simp [d3, d2, d1, Core.wr_get_ne, Core.wr_get_self]]; rfl)
  have s5 : DetStep B img ⟨d4, M⟩ ⟨d5, M⟩ := dstep f8001e020 rfl (by
    rw [exec_op]; simp only [alu]
    rw [show d4.get 10 = t + 0xffffffff#32 by simp [d4, Core.wr_get_self],
      show d4.get 11 = w4 by simp [d4, d3, d2, Core.wr_get_ne, Core.wr_get_self]]; rfl)
  have s6 : DetStep B img ⟨d5, M⟩ ⟨d6, M1⟩ := by
    obtain ⟨a, r⟩ := ho 0x0#32 (by simp)
    have := dstep_store (m := ⟨d5, M⟩) f8001e022 rfl (exec_store _ _ _ _ _ _)
      (by rw [g8 d5 (by simp)]; exact a) (by rw [g8 d5 (by simp)]; exact r)
    rwa [g8 d5 (by simp), show d5.get 10 = v by simp [d5, Core.wr_get_self]] at this
  have s7 : DetStep B img ⟨d6, M1⟩ ⟨d7, M2⟩ := by
    obtain ⟨a, r⟩ := ho 0x4#32 (by simp)
    have := dstep_store (m := ⟨d6, M1⟩) f8001e024 rfl (exec_store _ _ _ _ _ _)
      (by rw [g8 d6 (by simp)]; exact a) (by rw [g8 d6 (by simp)]; exact r)
    rwa [g8 d6 (by simp), show d6.get 12 = w8 by simp [d6, d5, d4, d3, Core.wr_get_ne, Core.wr_get_self]] at this
  have s8 : DetStep B img ⟨d7, M2⟩ ⟨d8, M2⟩ := ld d7 d8 M2 _ _ 1 f8001e026 rfl (g2 d7 (by simp)) (by simp) rfl (by decide)
  have s9 : DetStep B img ⟨d8, M2⟩ ⟨d9, M2⟩ := ld d8 d9 M2 _ _ 8 f8001e028 rfl (g2 d8 (by simp)) (by simp) rfl (by decide)
  have s10 : DetStep B img ⟨d9, M2⟩ ⟨d10, M2⟩ := dstep f8001e02a rfl (by rw [exec_opimm, g2 d9 (by simp)]; rfl)
  have s11 : DetStep B img ⟨d10, M2⟩ ⟨wEpi d M, M2⟩ := by
    have h1 : d10.get 1 = ramRead M2 (sp' + 0x1c#32) .w := by simp [d10, d9, d8, Core.wr_get_ne, Core.wr_get_self]
    refine dstep f8001e02c rfl ?_
    rw [exec_jalr, Core.set_zero, h1, BitVec.add_zero, clear0 _ hra, jump_ok _ _ hra]
    rfl
  have q := fun (x : Core) (hx : x.sameCsr d) => Quiet.of_sameCsr hx hq
  have k1 : d1.sameCsr d := Core.sameCsr_wr _ _ _ _
  have k2 : d2.sameCsr d := (Core.sameCsr_wr _ _ _ _).trans k1
  have k3 : d3.sameCsr d := (Core.sameCsr_wr _ _ _ _).trans k2
  have k4 : d4.sameCsr d := (Core.sameCsr_wr _ _ _ _).trans k3
  have k5 : d5.sameCsr d := (Core.sameCsr_wr _ _ _ _).trans k4
  have k6 : d6.sameCsr d := (Core.sameCsr_goto _ _).trans k5
  have k7 : d7.sameCsr d := (Core.sameCsr_goto _ _).trans k6
  have k8 : d8.sameCsr d := (Core.sameCsr_wr _ _ _ _).trans k7
  have k9 : d9.sameCsr d := (Core.sameCsr_wr _ _ _ _).trans k8
  have k10 : d10.sameCsr d := (Core.sameCsr_wr _ _ _ _).trans k9
  exact .step hq s1 (.step (q _ k1) s2 (.step (q _ k2) s3 (.step (q _ k3) s4 (.step (q _ k4) s5
    (.step (q _ k5) s6 (.step (q _ k6) s7 (.step (q _ k7) s8 (.step (q _ k8) s9 (.step (q _ k9) s10
    (.single (q _ k10) s11))))))))))

end E5R.Rmk.Cobs
