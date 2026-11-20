/-
  A device read as a node of a checkpoint tree (`Lands`), on the pinned RMK image.

  Original e5r code, Apache-2.0.

  PROVED here:
  * `rom_none`: below the image (address < 0x80000000) a read finds no image byte;
  * `lands_lbu_dev`: an `lbu` from a readable byte-wide device register outside RAM and the image
    is a tree node: it faults under no oracle, and its successors (one for each value the device
    may return) are exactly the core with rd set from that value. The value is the environment's:
    nothing is assumed about it.
-/
import Projects.rmk.Trees
import Projects.rmk.Fetch

namespace E5R.Rmk
open E5R

theorem rom_none (a : Nat) (h : a + 1 ≤ 0x80000000) : romRead? img a 1 false = none := by
  rw [ro_eq]
  simp only [romRead?, romRead?.go, romByte?, List.find?]
  have h1 : decide (0x80000000 ≤ a) = false := by simp; omega
  have h2 : decide (0x800210dc ≤ a) = false := by simp; omega
  simp only [Nat.add_zero, h1, h2, Bool.false_and]
  rfl

theorem lands_lbu_dev {P : Machine → Prop} {m : Machine} {rd rs1 : Reg} {off len a : Word} {d : DevReg}
    (hal : m.core.pc.getLsbD 0 = false)
    (hf : fetchDecode img m.core.pc = some (.load .b false rd rs1 off, len))
    (ha : m.core.get rs1 + off = a) (hin : B.inRam a 1 = false) (hr : romRead? img a.toNat 1 false = none)
    (hd : B.device? a = some d) (hdr : d.read = true) (hw : d.width = 1) (hq : Quiet m.core)
    (h : ∀ v : Word, Lands B img P ⟨m.core.wr rd (extend .b false (devVal .b v)) (m.core.pc + len), m.ram⟩) :
    Lands B img P m := by
  have key : ∀ o, stepInstr B img m o =
      .ok (m.core.wr rd (extend .b false (devVal .b (o 0))) (m.core.pc + len)) m.ram [] := by
    intro o
    rw [stepInstr_of hal hf, exec_load, ha]
    unfold interp
    have e1 : ¬ (a.toNat % Width.b.bytes ≠ 0) := by simp [Width.bytes, Nat.mod_one]
    have e2 : B.inRam a Width.b.bytes = false := hin
    have e3 : romRead? img a.toNat Width.b.bytes false = none := hr
    have e4 : (d.read && decide (Width.b.bytes = d.width)) = true := by simp [hdr, hw, Width.bytes]
    rw [ite_cond_eq_false _ _ (eq_false e1), e2, if_neg (by decide), if_neg (by decide), e3]
    simp only [hd, e4, if_true]
    rfl
  refine .step hq (fun o f e => by rw [key o] at e; cases e) fun x evs hx => ?_
  obtain ⟨o, ho⟩ := step_oracle hq hx
  rw [key o] at ho
  injection ho with h1 h2 h3
  have : x = ⟨m.core.wr rd (extend .b false (devVal .b (o 0))) (m.core.pc + len), m.ram⟩ := by
    cases x; simp only at h1 h2; rw [h1, h2]
  rw [this]; exact h (o 0)

/-- A quiet deterministic run into a tree is a tree. -/
theorem lands_of_qrun_lands {P : Machine → Prop} :
    ∀ {k m m'}, QRun B img k m m' → Lands B img P m' → Lands B img P m := by
  intro k m m' h hp
  induction h with
  | refl => exact hp
  | step hq hs _ ih =>
    refine .step hq (fun o f e => by rw [hs o] at e; cases e) fun x evs hx => ?_
    obtain ⟨rfl, -⟩ := quiet_step hq hs hx
    exact ih hp

end E5R.Rmk
