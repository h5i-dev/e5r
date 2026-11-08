-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.Apply
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.Apply
theorem copy_contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst : Word)
    (hp : c.pc = 0x800002d8) (hs : c.get 11 = src) (hd : c.get 10 = dst)
    (hsrc : HalfBlock B src) (hdst : HalfBlock B dst) :
    ∃ d, Quiet.Steps B img 11 ⟨c, ram⟩ ⟨d, Copy.copy10 ram src dst⟩ ∧
      d.pc = c.get 1 &&& ~~~1 ∧ d.get 10 = dst ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → d.get r = c.get r) ∧
      d.sameCsr c := by
  let v0 := extend .h true (ramRead ram (src+0#32) .h)
  let v1 := extend .h true (ramRead ram (src+2#32) .h)
  let v2 := extend .h true (ramRead ram (src+4#32) .h)
  let v3 := extend .h true (ramRead ram (src+6#32) .h)
  let v4 := extend .h true (ramRead ram (src+8#32) .h)
  let c1 := c.wr 12 v0 0x800002dc
  let c2 := c1.wr 13 v1 0x800002e0
  let c3 := c2.wr 14 v2 0x800002e4
  let c4 := c3.wr 15 v3 0x800002e8
  let c5 := c4.wr 11 v4 0x800002ec
  let r0 := ram
  let r1 := ramWrite r0 (dst+0#32) v0 .h
  let c6 := c5.goto 0x800002f0
  let r2 := ramWrite r1 (dst+2#32) v1 .h
  let c7 := c6.goto 0x800002f4
  let r3 := ramWrite r2 (dst+4#32) v2 .h
  let c8 := c7.goto 0x800002f8
  let r4 := ramWrite r3 (dst+6#32) v3 .h
  let c9 := c8.goto 0x800002fc
  let r5 := ramWrite r4 (dst+8#32) v4 .h
  let c10 := c9.goto 0x80000300
  let d := c10.goto (c.get 1 &&& ~~~1)
  have s0 : Quiet.Step B img ⟨c, ram⟩ ⟨c1, ram⟩ := by
    have hk := hsrc ⟨0, by decide⟩
    change (src+0#32).toNat % 2 = 0 ∧ B.inRam (src+0#32) 2 = true at hk
    have ha : c.get 11 = src := by simp [hs, Core.wr_get_ne]
    refine QuietDet.step_of (by rw [hp]; decide)
      (by rw [hp]; exact d2147484376) fun o => ?_
    rw [exec_load, ha, interp_load_ram o hk.1 hk.2, hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1, ram⟩ ⟨c2, ram⟩ := by
    have hk := hsrc ⟨1, by decide⟩
    change (src+2#32).toNat % 2 = 0 ∧ B.inRam (src+2#32) 2 = true at hk
    have ha : c1.get 11 = src := by simp [c1, hs, Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x800002dc : Word).getLsbD 0 = false; decide)
      (by exact d2147484380) fun o => ?_
    rw [exec_load, ha, interp_load_ram o hk.1 hk.2]
    rfl
  have s2 : Quiet.Step B img ⟨c2, ram⟩ ⟨c3, ram⟩ := by
    have hk := hsrc ⟨2, by decide⟩
    change (src+4#32).toNat % 2 = 0 ∧ B.inRam (src+4#32) 2 = true at hk
    have ha : c2.get 11 = src := by simp [c2, c1, hs, Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x800002e0 : Word).getLsbD 0 = false; decide)
      (by exact d2147484384) fun o => ?_
    rw [exec_load, ha, interp_load_ram o hk.1 hk.2]
    rfl
  have s3 : Quiet.Step B img ⟨c3, ram⟩ ⟨c4, ram⟩ := by
    have hk := hsrc ⟨3, by decide⟩
    change (src+6#32).toNat % 2 = 0 ∧ B.inRam (src+6#32) 2 = true at hk
    have ha : c3.get 11 = src := by simp [c3, c2, c1, hs, Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x800002e4 : Word).getLsbD 0 = false; decide)
      (by exact d2147484388) fun o => ?_
    rw [exec_load, ha, interp_load_ram o hk.1 hk.2]
    rfl
  have s4 : Quiet.Step B img ⟨c4, ram⟩ ⟨c5, ram⟩ := by
    have hk := hsrc ⟨4, by decide⟩
    change (src+8#32).toNat % 2 = 0 ∧ B.inRam (src+8#32) 2 = true at hk
    have ha : c4.get 11 = src := by simp [c4, c3, c2, c1, hs, Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x800002e8 : Word).getLsbD 0 = false; decide)
      (by exact d2147484392) fun o => ?_
    rw [exec_load, ha, interp_load_ram o hk.1 hk.2]
    rfl
  have s5 : Quiet.Step B img ⟨c5, r0⟩ ⟨c6, r1⟩ := by
    have hk := hdst ⟨0, by decide⟩
    change (dst+0#32).toNat % 2 = 0 ∧ B.inRam (dst+0#32) 2 = true at hk
    have ha : c5.get 10 = dst := by simp [c5, c4, c3, c2, c1, hd, Core.wr_get_ne]
    have hv : c5.get 12 = v0 := by simp [c5, c4, c3, c2, c1, Core.wr_get]
    refine QuietDet.step_of (by change (0x800002ec : Word).getLsbD 0 = false; decide) d2147484396 fun o => ?_
    rw [exec_store, ha, hv, interp_store_ram o hk.1 hk.2]
    rfl
  have s6 : Quiet.Step B img ⟨c6, r1⟩ ⟨c7, r2⟩ := by
    have hk := hdst ⟨1, by decide⟩
    change (dst+2#32).toNat % 2 = 0 ∧ B.inRam (dst+2#32) 2 = true at hk
    have ha : c6.get 10 = dst := by simp [c6, c5, c4, c3, c2, c1, hd, Core.wr_get_ne]
    have hv : c6.get 13 = v1 := by simp [c6, c5, c4, c3, c2, c1, Core.wr_get]
    refine QuietDet.step_of (by change (0x800002f0 : Word).getLsbD 0 = false; decide) d2147484400 fun o => ?_
    rw [exec_store, ha, hv, interp_store_ram o hk.1 hk.2]
    rfl
  have s7 : Quiet.Step B img ⟨c7, r2⟩ ⟨c8, r3⟩ := by
    have hk := hdst ⟨2, by decide⟩
    change (dst+4#32).toNat % 2 = 0 ∧ B.inRam (dst+4#32) 2 = true at hk
    have ha : c7.get 10 = dst := by simp [c7, c6, c5, c4, c3, c2, c1, hd, Core.wr_get_ne]
    have hv : c7.get 14 = v2 := by simp [c7, c6, c5, c4, c3, c2, c1, Core.wr_get]
    refine QuietDet.step_of (by change (0x800002f4 : Word).getLsbD 0 = false; decide) d2147484404 fun o => ?_
    rw [exec_store, ha, hv, interp_store_ram o hk.1 hk.2]
    rfl
  have s8 : Quiet.Step B img ⟨c8, r3⟩ ⟨c9, r4⟩ := by
    have hk := hdst ⟨3, by decide⟩
    change (dst+6#32).toNat % 2 = 0 ∧ B.inRam (dst+6#32) 2 = true at hk
    have ha : c8.get 10 = dst := by simp [c8, c7, c6, c5, c4, c3, c2, c1, hd, Core.wr_get_ne]
    have hv : c8.get 15 = v3 := by simp [c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get]
    refine QuietDet.step_of (by change (0x800002f8 : Word).getLsbD 0 = false; decide) d2147484408 fun o => ?_
    rw [exec_store, ha, hv, interp_store_ram o hk.1 hk.2]
    rfl
  have s9 : Quiet.Step B img ⟨c9, r4⟩ ⟨c10, r5⟩ := by
    have hk := hdst ⟨4, by decide⟩
    change (dst+8#32).toNat % 2 = 0 ∧ B.inRam (dst+8#32) 2 = true at hk
    have ha : c9.get 10 = dst := by simp [c9, c8, c7, c6, c5, c4, c3, c2, c1, hd, Core.wr_get_ne]
    have hv : c9.get 11 = v4 := by simp [c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get]
    refine QuietDet.step_of (by change (0x800002fc : Word).getLsbD 0 = false; decide) d2147484412 fun o => ?_
    rw [exec_store, ha, hv, interp_store_ram o hk.1 hk.2]
    rfl
  have s10 : Quiet.Step B img ⟨c10, r5⟩ ⟨d, r5⟩ := by
    have ha : c10.get 1 = c.get 1 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x80000300 : Word).getLsbD 0 = false; decide) d2147484416 fun o => ?_
    rw [exec_jalr, ha]
    simp only [BitVec.add_zero, Core.set_zero, jump_ok _ _ (clear_bit0 _)]
    rfl
  refine ⟨d, .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.single s10)))))))))), rfl, ?_, ?_, ?_⟩
  · simp [d,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,hd]
  · intro r h11 h12 h13 h14 h15
    simp [d,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h11,h12,h13,h14,h15]
  · exact (Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans
      ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans
      ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans
      ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      (Core.sameCsr_wr _ _ _ _))))))))))

end E5R.Thermostat.Apply
namespace E5R.Thermostat.Apply
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x800002cc) (htag : B.inRam (c.get 12) 1 = true)
    (hstate : HalfBlock B (c.get 11)) (hwrite : HalfBlock B (c.get 12))
    (hout : HalfBlock B (c.get 10)) :
    ∃ n d, n ≤ 15 ∧ Quiet.Steps B img n ⟨c, ram⟩
      ⟨d, Copy.copy10 ram (if ram (c.get 12) = 2#8 then c.get 11 else c.get 12) (c.get 10)⟩ ∧
      d.pc = c.get 1 &&& ~~~1 ∧ d.get 10 = c.get 10 ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → d.get r = c.get r) ∧
      d.sameCsr c := by
  let tag := extend .b false (ramRead ram (c.get 12) .b)
  let c1 := c.wr 13 tag 0x800002d0
  let c2 := c1.wr 14 2#32 0x800002d2
  have he : tag = 2#32 ↔ ram (c.get 12) = 2#8 := by
    dsimp only [tag]
    rw [Memory.load_byte, Memory.option_tag]
  have s0 : Quiet.Step B img ⟨c, ram⟩ ⟨c1, ram⟩ := by
    refine QuietDet.step_of (by rw [hp]; decide) (by rw [hp]; exact d2147484364) fun o => ?_
    rw [exec_load, BitVec.add_zero, interp_load_ram o (by simp only [Width.bytes, Nat.mod_one]) htag, hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1, ram⟩ ⟨c2, ram⟩ := by
    refine QuietDet.step_of (by change (0x800002d0 : Word).getLsbD 0 = false; decide) d2147484368 fun o => ?_
    rw [exec_opimm]
    rfl
  have ha : c2.get 13 = tag := by simp [c2, c1, Core.wr_get]
  have hb : c2.get 14 = 2#32 := by simp [c2, Core.wr_get]
  by_cases ht : tag = 2#32
  · have s2 : Quiet.Step B img ⟨c2, ram⟩ ⟨c2.goto 0x800002d8, ram⟩ := by
      refine QuietDet.step_of (by change (0x800002d2 : Word).getLsbD 0 = false; decide) d2147484370 fun o => ?_
      rw [exec_branch, ite_eq_left (by simp [taken, ha, hb, ht])]
      rw [jump_ok _ _ (by change (0x800002d8 : Word).getLsbD 0 = false; decide)]
      rfl
    obtain ⟨d, hs, hr, hd, hf, hc⟩ := E5R.Thermostat.Apply.copy_contract_quiet B (c2.goto 0x800002d8) ram (c.get 11) (c.get 10)
      rfl (by simp [c2,c1,Core.wr_get_ne]) (by simp [c2,c1,Core.wr_get_ne]) hstate hout
    refine ⟨14, d, by decide, ?_, ?_, hd, ?_, ?_⟩
    · simpa only [ite_eq_left (he.mp ht)] using (.step s0 (.step s1 (.step s2 hs)))
    · simpa [c2,c1,Core.wr_get_ne] using hr
    · intro r h11 h12 h13 h14 h15
      simpa [c2,c1,Core.wr_get_ne,h13,h14] using hf r h11 h12 h13 h14 h15
    · exact hc.trans ((Core.sameCsr_goto _ _).trans
        ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_wr _ _ _ _)))
  · let c3 := c2.goto 0x800002d6
    let c4 := c3.wr 11 (c.get 12) 0x800002d8
    have s2 : Quiet.Step B img ⟨c2, ram⟩ ⟨c3, ram⟩ := by
      refine QuietDet.step_of (by change (0x800002d2 : Word).getLsbD 0 = false; decide) d2147484370 fun o => ?_
      rw [exec_branch, ite_eq_right (by simpa [taken, ha, hb] using ht)]
      rfl
    have s3 : Quiet.Step B img ⟨c3, ram⟩ ⟨c4, ram⟩ := by
      refine QuietDet.step_of (by change (0x800002d6 : Word).getLsbD 0 = false; decide) d2147484374 fun o => ?_
      rw [exec_op]
      simp [c4, c3, c2,c1, Core.wr_get_ne, alu]
    obtain ⟨d, hs, hr, hd, hf, hc⟩ := E5R.Thermostat.Apply.copy_contract_quiet B c4 ram (c.get 12) (c.get 10)
      rfl (by simp [c4,Core.wr_get]) (by simp [c4,c3,c2,c1,Core.wr_get_ne]) hwrite hout
    refine ⟨15, d, by decide, ?_, ?_, hd, ?_, ?_⟩
    · simpa only [ite_eq_right (fun h => ht (he.mpr h))] using (.step s0 (.step s1 (.step s2 (.step s3 hs))))
    · simpa [c4,c3,c2,c1,Core.wr_get_ne] using hr
    · intro r h11 h12 h13 h14 h15
      simpa [c4,c3,c2,c1,Core.wr_get_ne,h11,h13,h14] using hf r h11 h12 h13 h14 h15
    · exact hc.trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans
        ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_wr _ _ _ _))))

end E5R.Thermostat.Apply
namespace E5R.Thermostat.Apply
theorem source_contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (s : Spec.Snapshot) (w : Option Spec.Snapshot)
    (hp : c.pc = 0x800002cc) (htag : B.inRam (c.get 12) 1 = true)
    (hstate : HalfBlock B (c.get 11)) (hwrite : HalfBlock B (c.get 12))
    (hout : HalfBlock B (c.get 10))
    (hs : Encoding.SnapshotAt ram (c.get 11) s) (hw : Encoding.OptionAt ram (c.get 12) w) :
    ∃ n d ram', n ≤ 15 ∧ Quiet.Steps B img n ⟨c, ram⟩ ⟨d, ram'⟩ ∧
      d.pc = c.get 1 &&& ~~~1 ∧ d.get 10 = c.get 10 ∧
      Encoding.SnapshotAt ram' (c.get 10) (Spec.apply s w) ∧
      (∀ x, (∀ i : Fin 10, x ≠ c.get 10 + BitVec.ofNat 32 i.val) → ram' x = ram x) ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → d.get r = c.get r) ∧
      d.sameCsr c := by
  obtain ⟨n,d,hn,he,hp,hd,hf,hc⟩ := E5R.Thermostat.Apply.contract_quiet B c ram hp htag hstate hwrite hout
  refine ⟨n,d,_,hn,he,hp,hd,?_,?_,hf,hc⟩
  · intro i
    rw [Copy.bytes]
    cases w with
    | none =>
      have hw' : ram (c.get 12) = 2#8 := hw
      simpa [hw', Spec.apply] using hs i
    | some sn => simpa [Encoding.option_some_tag hw, Spec.apply] using hw i
  · intro x hx
    exact Copy.frame ram _ _ x hx

end E5R.Thermostat.Apply
