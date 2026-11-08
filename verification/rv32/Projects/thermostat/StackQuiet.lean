-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.Stack
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.Stack
theorem prologue_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000052) (hs : Accessible B (base c)) :
    ∃ d, Quiet.Steps B img 8 ⟨c,ram⟩ ⟨d,save c ram⟩ ∧
      d.pc = 0x80000062 ∧ d.get 2 = base c ∧
      (∀ r : Reg, r ≠ 2 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 2 (base c) 0x80000054
  let r0 := ram
  let r1 := ramWrite r0 (base c+60#32) (c.get 1) .w
  let c2 := c1.goto 0x80000056
  let r2 := ramWrite r1 (base c+56#32) (c.get 8) .w
  let c3 := c2.goto 0x80000058
  let r3 := ramWrite r2 (base c+52#32) (c.get 9) .w
  let c4 := c3.goto 0x8000005a
  let r4 := ramWrite r3 (base c+48#32) (c.get 18) .w
  let c5 := c4.goto 0x8000005c
  let r5 := ramWrite r4 (base c+44#32) (c.get 19) .w
  let c6 := c5.goto 0x8000005e
  let r6 := ramWrite r5 (base c+40#32) (c.get 20) .w
  let c7 := c6.goto 0x80000060
  let r7 := ramWrite r6 (base c+36#32) (c.get 21) .w
  let c8 := c7.goto 0x80000062
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp]; decide) (by rw [hp]; exact d2147483730) fun o => ?_
    rw [exec_opimm,hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,r0⟩ ⟨c2,r1⟩ := by
    have hk := hs ⟨0,by decide⟩
    change (base c+60#32).toNat % 4 = 0 ∧ B.inRam (base c+60#32) 4 = true at hk
    have ha : c1.get 2 = base c := by simp [c1,Core.wr_get]
    have hv : c1.get 1 = c.get 1 := by simp [c1,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x80000054 : Word).getLsbD 0 = false; decide) d2147483732 fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .w) (a := base c+60#32) (v := c.get 1) o hk.1 hk.2]
    rfl
  have s2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    have hk := hs ⟨1,by decide⟩
    change (base c+56#32).toNat % 4 = 0 ∧ B.inRam (base c+56#32) 4 = true at hk
    have ha : c2.get 2 = base c := by simp [c2, c1,Core.wr_get]
    have hv : c2.get 8 = c.get 8 := by simp [c2, c1,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x80000056 : Word).getLsbD 0 = false; decide) d2147483734 fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .w) (a := base c+56#32) (v := c.get 8) o hk.1 hk.2]
    rfl
  have s3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r3⟩ := by
    have hk := hs ⟨2,by decide⟩
    change (base c+52#32).toNat % 4 = 0 ∧ B.inRam (base c+52#32) 4 = true at hk
    have ha : c3.get 2 = base c := by simp [c3, c2, c1,Core.wr_get]
    have hv : c3.get 9 = c.get 9 := by simp [c3, c2, c1,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x80000058 : Word).getLsbD 0 = false; decide) d2147483736 fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .w) (a := base c+52#32) (v := c.get 9) o hk.1 hk.2]
    rfl
  have s4 : Quiet.Step B img ⟨c4,r3⟩ ⟨c5,r4⟩ := by
    have hk := hs ⟨3,by decide⟩
    change (base c+48#32).toNat % 4 = 0 ∧ B.inRam (base c+48#32) 4 = true at hk
    have ha : c4.get 2 = base c := by simp [c4, c3, c2, c1,Core.wr_get]
    have hv : c4.get 18 = c.get 18 := by simp [c4, c3, c2, c1,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x8000005a : Word).getLsbD 0 = false; decide) d2147483738 fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .w) (a := base c+48#32) (v := c.get 18) o hk.1 hk.2]
    rfl
  have s5 : Quiet.Step B img ⟨c5,r4⟩ ⟨c6,r5⟩ := by
    have hk := hs ⟨4,by decide⟩
    change (base c+44#32).toNat % 4 = 0 ∧ B.inRam (base c+44#32) 4 = true at hk
    have ha : c5.get 2 = base c := by simp [c5, c4, c3, c2, c1,Core.wr_get]
    have hv : c5.get 19 = c.get 19 := by simp [c5, c4, c3, c2, c1,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x8000005c : Word).getLsbD 0 = false; decide) d2147483740 fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .w) (a := base c+44#32) (v := c.get 19) o hk.1 hk.2]
    rfl
  have s6 : Quiet.Step B img ⟨c6,r5⟩ ⟨c7,r6⟩ := by
    have hk := hs ⟨5,by decide⟩
    change (base c+40#32).toNat % 4 = 0 ∧ B.inRam (base c+40#32) 4 = true at hk
    have ha : c6.get 2 = base c := by simp [c6, c5, c4, c3, c2, c1,Core.wr_get]
    have hv : c6.get 20 = c.get 20 := by simp [c6, c5, c4, c3, c2, c1,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x8000005e : Word).getLsbD 0 = false; decide) d2147483742 fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .w) (a := base c+40#32) (v := c.get 20) o hk.1 hk.2]
    rfl
  have s7 : Quiet.Step B img ⟨c7,r6⟩ ⟨c8,r7⟩ := by
    have hk := hs ⟨6,by decide⟩
    change (base c+36#32).toNat % 4 = 0 ∧ B.inRam (base c+36#32) 4 = true at hk
    have ha : c7.get 2 = base c := by simp [c7, c6, c5, c4, c3, c2, c1,Core.wr_get]
    have hv : c7.get 21 = c.get 21 := by simp [c7, c6, c5, c4, c3, c2, c1,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x80000060 : Word).getLsbD 0 = false; decide) d2147483744 fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .w) (a := base c+36#32) (v := c.get 21) o hk.1 hk.2]
    rfl
  refine ⟨c8,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.single s7))))))),rfl,?_,?_,?_⟩
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
  · intro r hr
    simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,hr]
  · exact (Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans
      ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans
      ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans
      ((Core.sameCsr_goto _ _).trans (Core.sameCsr_wr _ _ _ _)))))))

end E5R.Thermostat.Stack
namespace E5R.Thermostat.Stack
theorem epilogue_quiet (B : Board) (before c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x800001ac) (hsp : c.get 2 = base before)
    (ha : Accessible B (base before))
    (hs : ∀ i : Fin 7, ramRead ram (base before + BitVec.ofNat 32 (60-4*i.val)) .w = before.get (reg i)) :
    ∃ d, Quiet.Steps B img 9 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = before.get 1 &&& ~~~1 ∧ d.get 2 = before.get 2 ∧
      (∀ i : Fin 7, d.get (reg i) = before.get (reg i)) ∧
      (∀ r : Reg, r ≠ 1 → r ≠ 2 → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 →
        d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 1 (before.get 1) 0x800001ae
  let c2 := c1.wr 8 (before.get 8) 0x800001b0
  let c3 := c2.wr 9 (before.get 9) 0x800001b2
  let c4 := c3.wr 18 (before.get 18) 0x800001b4
  let c5 := c4.wr 19 (before.get 19) 0x800001b6
  let c6 := c5.wr 20 (before.get 20) 0x800001b8
  let c7 := c6.wr 21 (before.get 21) 0x800001ba
  let c8 := c7.wr 2 (before.get 2) 0x800001bc
  let d := c8.goto (before.get 1 &&& ~~~1)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    have hk := ha ⟨0,by decide⟩
    change (base before+60#32).toNat % 4 = 0 ∧ B.inRam (base before+60#32) 4 = true at hk
    have hv := hs ⟨0,by decide⟩
    change ramRead ram (base before+60#32) .w = before.get 1 at hv
    have hh : c.get 2 = base before := by simp [hsp,Core.wr_get_ne]
    refine QuietDet.step_of (by rw [hp]; decide)
      (by rw [hp]; exact d2147484076) fun o => ?_
    rw [exec_load,hh,interp_load_ram (B := B) (img := img) (w := .w) (a := base before+60#32) o hk.1 hk.2,hv]
    rw [hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    have hk := ha ⟨1,by decide⟩
    change (base before+56#32).toNat % 4 = 0 ∧ B.inRam (base before+56#32) 4 = true at hk
    have hv := hs ⟨1,by decide⟩
    change ramRead ram (base before+56#32) .w = before.get 8 at hv
    have hh : c1.get 2 = base before := by simp [c1, hsp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x800001ae : Word).getLsbD 0 = false; decide)
      (by exact d2147484078) fun o => ?_
    rw [exec_load,hh,interp_load_ram (B := B) (img := img) (w := .w) (a := base before+56#32) o hk.1 hk.2,hv]
    skip
    rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    have hk := ha ⟨2,by decide⟩
    change (base before+52#32).toNat % 4 = 0 ∧ B.inRam (base before+52#32) 4 = true at hk
    have hv := hs ⟨2,by decide⟩
    change ramRead ram (base before+52#32) .w = before.get 9 at hv
    have hh : c2.get 2 = base before := by simp [c2, c1, hsp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x800001b0 : Word).getLsbD 0 = false; decide)
      (by exact d2147484080) fun o => ?_
    rw [exec_load,hh,interp_load_ram (B := B) (img := img) (w := .w) (a := base before+52#32) o hk.1 hk.2,hv]
    skip
    rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    have hk := ha ⟨3,by decide⟩
    change (base before+48#32).toNat % 4 = 0 ∧ B.inRam (base before+48#32) 4 = true at hk
    have hv := hs ⟨3,by decide⟩
    change ramRead ram (base before+48#32) .w = before.get 18 at hv
    have hh : c3.get 2 = base before := by simp [c3, c2, c1, hsp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x800001b2 : Word).getLsbD 0 = false; decide)
      (by exact d2147484082) fun o => ?_
    rw [exec_load,hh,interp_load_ram (B := B) (img := img) (w := .w) (a := base before+48#32) o hk.1 hk.2,hv]
    skip
    rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    have hk := ha ⟨4,by decide⟩
    change (base before+44#32).toNat % 4 = 0 ∧ B.inRam (base before+44#32) 4 = true at hk
    have hv := hs ⟨4,by decide⟩
    change ramRead ram (base before+44#32) .w = before.get 19 at hv
    have hh : c4.get 2 = base before := by simp [c4, c3, c2, c1, hsp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x800001b4 : Word).getLsbD 0 = false; decide)
      (by exact d2147484084) fun o => ?_
    rw [exec_load,hh,interp_load_ram (B := B) (img := img) (w := .w) (a := base before+44#32) o hk.1 hk.2,hv]
    skip
    rfl
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    have hk := ha ⟨5,by decide⟩
    change (base before+40#32).toNat % 4 = 0 ∧ B.inRam (base before+40#32) 4 = true at hk
    have hv := hs ⟨5,by decide⟩
    change ramRead ram (base before+40#32) .w = before.get 20 at hv
    have hh : c5.get 2 = base before := by simp [c5, c4, c3, c2, c1, hsp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x800001b6 : Word).getLsbD 0 = false; decide)
      (by exact d2147484086) fun o => ?_
    rw [exec_load,hh,interp_load_ram (B := B) (img := img) (w := .w) (a := base before+40#32) o hk.1 hk.2,hv]
    skip
    rfl
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    have hk := ha ⟨6,by decide⟩
    change (base before+36#32).toNat % 4 = 0 ∧ B.inRam (base before+36#32) 4 = true at hk
    have hv := hs ⟨6,by decide⟩
    change ramRead ram (base before+36#32) .w = before.get 21 at hv
    have hh : c6.get 2 = base before := by simp [c6, c5, c4, c3, c2, c1, hsp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x800001b8 : Word).getLsbD 0 = false; decide)
      (by exact d2147484088) fun o => ?_
    rw [exec_load,hh,interp_load_ram (B := B) (img := img) (w := .w) (a := base before+36#32) o hk.1 hk.2,hv]
    skip
    rfl
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    have hh : c7.get 2 = base before := by simp [c7,c6,c5,c4,c3,c2,c1,hsp,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x800001ba : Word).getLsbD 0 = false; decide) d2147484090 fun o => ?_
    rw [exec_opimm,hh]
    have hv : alu .add (base before) 64#32 = before.get 2 := by
      simp [alu,base,BitVec.add_assoc]
    rw [hv]
    rfl
  have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨d,ram⟩ := by
    have hh : c8.get 1 = before.get 1 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x800001bc : Word).getLsbD 0 = false; decide) d2147484092 fun o => ?_
    rw [exec_jalr,hh]
    simp only [BitVec.add_zero,Core.set_zero,jump_ok _ _ (clear_bit0 _)]
    rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.single s8)))))))),rfl,?_,?_,?_,?_⟩
  · simp [d,c8,Core.wr_get]
  · intro i
    have hi := i.isLt
    have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 := by omega
    rcases hc with h|h|h|h|h|h|h
    all_goals simp [reg,h,d,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
  · intro r h1 h2 h8 h9 h18 h19 h20 h21
    simp [d,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h1,h2,h8,h9,h18,h19,h20,h21]
  · exact (Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      (Core.sameCsr_wr _ _ _ _))))))))

end E5R.Thermostat.Stack
