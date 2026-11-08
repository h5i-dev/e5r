-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ReadBody
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.ReadBody
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (src out : Word)
    (hp : c.pc = 0x80000128) (hs : c.get 12 = src) (ho : c.get 10 = out)
    (hsrc : Apply.HalfBlock B src) (hout : Apply.HalfBlock B (out+10#32))
    (htag : B.inRam out 1 = true) :
    ∃ d, Quiet.Steps B img 13 ⟨c,ram⟩ ⟨d,result ram src out⟩ ∧
      d.pc = 0x800001ac ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → d.get r = c.get r) ∧
      d.sameCsr c := by
  let v0 := extend .h true (ramRead ram (src+0#32) .h)
  let v1 := extend .h true (ramRead ram (src+2#32) .h)
  let v2 := extend .h true (ramRead ram (src+4#32) .h)
  let v3 := extend .h true (ramRead ram (src+6#32) .h)
  let v4 := extend .h true (ramRead ram (src+8#32) .h)
  let c1 := c.wr 11 v0 0x8000012c
  let c2 := c1.wr 13 v1 0x80000130
  let c3 := c2.wr 14 v2 0x80000134
  let c4 := c3.wr 15 v3 0x80000138
  let c5 := c4.wr 12 v4 0x8000013c
  let c6 := c5.wr 16 2#32 0x8000013e
  let r0 := ramPut ram out 2#8
  let c7 := c6.goto 0x80000142
  let r1 := ramWrite r0 (out+10#32) v0 .h
  let c8 := c7.goto 0x80000146
  let r2 := ramWrite r1 (out+12#32) v1 .h
  let c9 := c8.goto 0x8000014a
  let r3 := ramWrite r2 (out+14#32) v2 .h
  let c10 := c9.goto 0x8000014e
  let r4 := ramWrite r3 (out+16#32) v3 .h
  let c11 := c10.goto 0x80000152
  let r5 := ramWrite r4 (out+18#32) v4 .h
  let c12 := c11.goto 0x80000156
  let d := c12.goto 0x800001ac
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    have hk := hsrc ⟨0,by decide⟩
    change (src+0#32).toNat % 2 = 0 ∧ B.inRam (src+0#32) 2 = true at hk
    have ha : c.get 12 = src := by simp [hs,Core.wr_get_ne]
    refine QuietDet.step_of (by rw [hp]; decide)
      (by rw [hp]; exact d2147483944) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := src+0#32) o hk.1 hk.2]
    rw [hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    have hk := hsrc ⟨1,by decide⟩
    change (src+2#32).toNat % 2 = 0 ∧ B.inRam (src+2#32) 2 = true at hk
    have ha : c1.get 12 = src := by simp [c1,hs,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x8000012c : Word).getLsbD 0 = false; decide)
      (by exact d2147483948) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := src+2#32) o hk.1 hk.2]
    skip
    rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    have hk := hsrc ⟨2,by decide⟩
    change (src+4#32).toNat % 2 = 0 ∧ B.inRam (src+4#32) 2 = true at hk
    have ha : c2.get 12 = src := by simp [c2,c1,hs,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x80000130 : Word).getLsbD 0 = false; decide)
      (by exact d2147483952) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := src+4#32) o hk.1 hk.2]
    skip
    rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    have hk := hsrc ⟨3,by decide⟩
    change (src+6#32).toNat % 2 = 0 ∧ B.inRam (src+6#32) 2 = true at hk
    have ha : c3.get 12 = src := by simp [c3,c2,c1,hs,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x80000134 : Word).getLsbD 0 = false; decide)
      (by exact d2147483956) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := src+6#32) o hk.1 hk.2]
    skip
    rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    have hk := hsrc ⟨4,by decide⟩
    change (src+8#32).toNat % 2 = 0 ∧ B.inRam (src+8#32) 2 = true at hk
    have ha : c4.get 12 = src := by simp [c4,c3,c2,c1,hs,Core.wr_get_ne]
    refine QuietDet.step_of (by change (0x80000138 : Word).getLsbD 0 = false; decide)
      (by exact d2147483960) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := src+8#32) o hk.1 hk.2]
    skip
    rfl
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000013c : Word).getLsbD 0 = false; decide) d2147483964 fun o => ?_
    rw [exec_opimm]
    rfl
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,r0⟩ := by
    have ha : c6.get 10 = out := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,ho]
    have hv : c6.get 16 = 2#32 := by simp [c6,Core.wr_get]
    refine QuietDet.step_of (by change (0x8000013e : Word).getLsbD 0 = false; decide) d2147483966 fun o => ?_
    rw [exec_store,ha,hv,BitVec.add_zero,
      interp_store_ram (B := B) (img := img) (w := .b) (a := out) (v := 2#32) o (by simp only [Width.bytes,Nat.mod_one]) htag]
    rfl
  have s7 : Quiet.Step B img ⟨c7,r0⟩ ⟨c8,r1⟩ := by
    have hk := hout ⟨0,by decide⟩
    have hk' : (out+10#32).toNat % 2 = 0 ∧ B.inRam (out+10#32) 2 = true := by
      simpa [BitVec.add_assoc] using hk
    have ha : c7.get 10 = out := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,ho]
    have hv : c7.get 11 = v0 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x80000142 : Word).getLsbD 0 = false; decide) d2147483970 fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := out+10#32) o hk'.1 hk'.2]
    rfl
  have s8 : Quiet.Step B img ⟨c8,r1⟩ ⟨c9,r2⟩ := by
    have hk := hout ⟨1,by decide⟩
    have hk' : (out+12#32).toNat % 2 = 0 ∧ B.inRam (out+12#32) 2 = true := by
      simpa [BitVec.add_assoc] using hk
    have ha : c8.get 10 = out := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,ho]
    have hv : c8.get 13 = v1 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x80000146 : Word).getLsbD 0 = false; decide) d2147483974 fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := out+12#32) o hk'.1 hk'.2]
    rfl
  have s9 : Quiet.Step B img ⟨c9,r2⟩ ⟨c10,r3⟩ := by
    have hk := hout ⟨2,by decide⟩
    have hk' : (out+14#32).toNat % 2 = 0 ∧ B.inRam (out+14#32) 2 = true := by
      simpa [BitVec.add_assoc] using hk
    have ha : c9.get 10 = out := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,ho]
    have hv : c9.get 14 = v2 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x8000014a : Word).getLsbD 0 = false; decide) d2147483978 fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := out+14#32) o hk'.1 hk'.2]
    rfl
  have s10 : Quiet.Step B img ⟨c10,r3⟩ ⟨c11,r4⟩ := by
    have hk := hout ⟨3,by decide⟩
    have hk' : (out+16#32).toNat % 2 = 0 ∧ B.inRam (out+16#32) 2 = true := by
      simpa [BitVec.add_assoc] using hk
    have ha : c10.get 10 = out := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,ho]
    have hv : c10.get 15 = v3 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x8000014e : Word).getLsbD 0 = false; decide) d2147483982 fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := out+16#32) o hk'.1 hk'.2]
    rfl
  have s11 : Quiet.Step B img ⟨c11,r4⟩ ⟨c12,r5⟩ := by
    have hk := hout ⟨4,by decide⟩
    have hk' : (out+18#32).toNat % 2 = 0 ∧ B.inRam (out+18#32) 2 = true := by
      simpa [BitVec.add_assoc] using hk
    have ha : c11.get 10 = out := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,ho]
    have hv : c11.get 12 = v4 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x80000152 : Word).getLsbD 0 = false; decide) d2147483986 fun o => ?_
    rw [exec_store,ha,hv,interp_store_ram (B := B) (img := img) (w := .h) (a := out+18#32) o hk'.1 hk'.2]
    rfl
  have s12 : Quiet.Step B img ⟨c12,r5⟩ ⟨d,r5⟩ := by
    refine QuietDet.step_of (by change (0x80000156 : Word).getLsbD 0 = false; decide) d2147483990 fun o => ?_
    rw [exec_jal,Core.set_zero,jump_ok _ _ (by change (0x800001ac : Word).getLsbD 0 = false; decide)]
    rfl
  have hm : r5 = result ram src out := by
    simp [r5,r4,r3,r2,r1,r0,result,Copy.copyFrom,v0,v1,v2,v3,v4,BitVec.add_assoc]
  refine ⟨d,?_,rfl,?_,?_⟩
  · rw [← hm]
    exact .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.single s12))))))))))))
  · intro r h11 h12 h13 h14 h15 h16
    simp [d,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h11,h12,h13,h14,h15,h16]
  · exact (Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_refl c)))))))))))))

end E5R.Thermostat.ReadBody
