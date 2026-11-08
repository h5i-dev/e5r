import Projects.thermostat.CommandPack
import Projects.thermostat.Decimal
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.NumericResult
open E5R E5R.Thermostat

theorem point_some (B : Board) (c : Core) (ram : Word → BitVec 8) (dc : BitVec 16)
    (hp : c.pc = 0x80002098#32) (hresult : Decimal.Result c (some dc)) :
    ∃ d, DetSteps B img 9 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (.ok (.setpoint dc)) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  have htag : c.get 10 = 1#32 := hresult.1
  let c1 := c.wr 10 (1#32) 0x8000209a#32
  let c2 := c1.goto 0x800020a0#32
  let c3 := c2.wr 12 (0#32) 0x800020a2#32
  let c4 := c3.wr 10 (0#32) 0x800020a4#32
  let c5 := c4.wr 10 (0#32) 0x800020a8#32
  let c6 := c5.goto 0x8000220c#32
  let d := CommandPack.execute c6
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wd2147491992) fun o => ?_
    have hv0 : c.get 10 = 1#32 := by simp [Core.wr_get_ne,Core.wr_get,htag]
    rw [exec_opimm,hv0,hp]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x8000209a#32).getLsbD 0 = false;decide) wd2147491994 fun o => ?_
    have hv0 : c1.get 10 = 1#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,htag]
    rw [exec_branch,hv0,Core.get_zero]
    have ht : taken .ne 1#32 (0 : Word) = true := by decide +kernel
    rw [ht]
    simp only [ite_true]
    have hpc : c1.pc = 0x8000209a#32 := rfl
    rw [hpc]
    rw [show 0x8000209a#32+0x6#32 = 0x800020a0#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x800020a0#32).getLsbD 0 = false;decide) wd2147492000 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x800020a2#32).getLsbD 0 = false;decide) wd2147492002 fun o => ?_
    have hv0 : c3.get 10 = 1#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,htag]
    rw [exec_opimm,hv0]
    rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x800020a4#32).getLsbD 0 = false;decide) wd2147492004 fun o => ?_
    have hv0 : c4.get 10 = 0#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,htag]
    rw [exec_opimm,hv0]
    rfl
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x800020a8#32).getLsbD 0 = false;decide) wd2147492008 fun o => ?_
    rw [exec_jal]
    have hpc : c5.pc = 0x800020a8#32 := rfl
    rw [hpc]
    rw [show 0x800020a8#32+0x164#32 = 0x8000220c#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have hpre : DetSteps B img 6 ⟨c,ram⟩ ⟨c6,ram⟩ := .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5)))))
  have hpack := CommandPack.contract B c6 ram rfl
  obtain ⟨hpc,hval,hregs,hcsr⟩ := CommandPack.fields c6
  refine ⟨d,hpre.trans hpack,hpc,?_,?_,hcsr⟩
  · have hm := CommandPack.numeric c6 false (by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]) (by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get])
    have hword : c6.get 11 = c.get 11 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [hword,hresult.2] at hm
    exact hm
  · intro r h1 h2 h3
    rw [hregs r h1 h2]
    simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h1,h2,h3]

theorem point_none (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80002098#32) (hresult : Decimal.Result c (none)) :
    ∃ d, DetSteps B img 10 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (.error 400) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  have htag : c.get 10 = 0#32 := hresult
  let c1 := c.wr 10 (0#32) 0x8000209a#32
  let c2 := c1.goto 0x8000209c#32
  let c3 := c2.wr 11 (400#32) 0x800020a0#32
  let c4 := c3.wr 12 (0#32) 0x800020a2#32
  let c5 := c4.wr 10 (0xffffffff#32) 0x800020a4#32
  let c6 := c5.wr 10 (255#32) 0x800020a8#32
  let c7 := c6.goto 0x8000220c#32
  let d := CommandPack.execute c7
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wd2147491992) fun o => ?_
    have hv0 : c.get 10 = 0#32 := by simp [Core.wr_get_ne,Core.wr_get,htag]
    rw [exec_opimm,hv0,hp]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x8000209a#32).getLsbD 0 = false;decide) wd2147491994 fun o => ?_
    have hv0 : c1.get 10 = 0#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,htag]
    rw [exec_branch,hv0,Core.get_zero]
    have ht : taken .ne 0#32 (0 : Word) = false := by decide +kernel
    rw [ht];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x8000209c#32).getLsbD 0 = false;decide) wd2147491996 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x800020a0#32).getLsbD 0 = false;decide) wd2147492000 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x800020a2#32).getLsbD 0 = false;decide) wd2147492002 fun o => ?_
    have hv0 : c4.get 10 = 0#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,htag]
    rw [exec_opimm,hv0]
    rfl
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x800020a4#32).getLsbD 0 = false;decide) wd2147492004 fun o => ?_
    have hv0 : c5.get 10 = 0xffffffff#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,htag]
    rw [exec_opimm,hv0]
    rfl
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine detStep_of (by change (0x800020a8#32).getLsbD 0 = false;decide) wd2147492008 fun o => ?_
    rw [exec_jal]
    have hpc : c6.pc = 0x800020a8#32 := rfl
    rw [hpc]
    rw [show 0x800020a8#32+0x164#32 = 0x8000220c#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have hpre : DetSteps B img 7 ⟨c,ram⟩ ⟨c7,ram⟩ := .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.single s6))))))
  have hpack := CommandPack.contract B c7 ram rfl
  obtain ⟨hpc,hval,hregs,hcsr⟩ := CommandPack.fields c7
  refine ⟨d,hpre.trans hpack,hpc,?_,?_,hcsr⟩
  · exact CommandPack.error400 c7 (by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]) (by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]) (by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get])
  · intro r h1 h2 h3
    rw [hregs r h1 h2]
    simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h1,h2,h3]

theorem temp_some (B : Board) (c : Core) (ram : Word → BitVec 8) (dc : BitVec 16)
    (hp : c.pc = 0x800020fe#32) (hresult : Decimal.Result c (some dc)) :
    ∃ d, DetSteps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (.ok (.reportTemp dc)) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  have htag : c.get 10 = 1#32 := hresult.1
  let c1 := c.wr 10 (1#32) 0x80002100#32
  let c2 := c1.goto 0x80002208#32
  let c3 := c2.wr 10 (1#32) 0x8000220a#32
  let c4 := c3.wr 12 (0#32) 0x8000220c#32
  let d := CommandPack.execute c4
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wd2147492094) fun o => ?_
    have hv0 : c.get 10 = 1#32 := by simp [Core.wr_get_ne,Core.wr_get,htag]
    rw [exec_opimm,hv0,hp]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80002100#32).getLsbD 0 = false;decide) wd2147492096 fun o => ?_
    have hv0 : c1.get 10 = 1#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,htag]
    rw [exec_branch,hv0,Core.get_zero]
    have ht : taken .ne 1#32 (0 : Word) = true := by decide +kernel
    rw [ht]
    simp only [ite_true]
    have hpc : c1.pc = 0x80002100#32 := rfl
    rw [hpc]
    rw [show 0x80002100#32+0x108#32 = 0x80002208#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80002208#32).getLsbD 0 = false;decide) wd2147492360 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x8000220a#32).getLsbD 0 = false;decide) wd2147492362 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    rfl
  have hpre : DetSteps B img 4 ⟨c,ram⟩ ⟨c4,ram⟩ := .step s0 (.step s1 (.step s2 (.single s3)))
  have hpack := CommandPack.contract B c4 ram rfl
  obtain ⟨hpc,hval,hregs,hcsr⟩ := CommandPack.fields c4
  refine ⟨d,hpre.trans hpack,hpc,?_,?_,hcsr⟩
  · have hm := CommandPack.numeric c4 true (by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]) (by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get])
    have hword : c4.get 11 = c.get 11 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [hword,hresult.2] at hm
    exact hm
  · intro r h1 h2 h3
    rw [hregs r h1 h2]
    simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h1,h2,h3]

theorem temp_none (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x800020fe#32) (hresult : Decimal.Result c (none)) :
    ∃ d, DetSteps B img 9 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (.error 400) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  have htag : c.get 10 = 0#32 := hresult
  let c1 := c.wr 10 (0#32) 0x80002100#32
  let c2 := c1.goto 0x80002104#32
  let c3 := c2.wr 11 (400#32) 0x80002108#32
  let c4 := c3.wr 10 (255#32) 0x8000210c#32
  let c5 := c4.goto 0x8000220a#32
  let c6 := c5.wr 12 (0#32) 0x8000220c#32
  let d := CommandPack.execute c6
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wd2147492094) fun o => ?_
    have hv0 : c.get 10 = 0#32 := by simp [Core.wr_get_ne,Core.wr_get,htag]
    rw [exec_opimm,hv0,hp]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80002100#32).getLsbD 0 = false;decide) wd2147492096 fun o => ?_
    have hv0 : c1.get 10 = 0#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,htag]
    rw [exec_branch,hv0,Core.get_zero]
    have ht : taken .ne 0#32 (0 : Word) = false := by decide +kernel
    rw [ht];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80002104#32).getLsbD 0 = false;decide) wd2147492100 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80002108#32).getLsbD 0 = false;decide) wd2147492104 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x8000210c#32).getLsbD 0 = false;decide) wd2147492108 fun o => ?_
    rw [exec_jal]
    have hpc : c4.pc = 0x8000210c#32 := rfl
    rw [hpc]
    rw [show 0x8000210c#32+0xfe#32 = 0x8000220a#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x8000220a#32).getLsbD 0 = false;decide) wd2147492362 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    rfl
  have hpre : DetSteps B img 6 ⟨c,ram⟩ ⟨c6,ram⟩ := .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5)))))
  have hpack := CommandPack.contract B c6 ram rfl
  obtain ⟨hpc,hval,hregs,hcsr⟩ := CommandPack.fields c6
  refine ⟨d,hpre.trans hpack,hpc,?_,?_,hcsr⟩
  · exact CommandPack.error400 c6 (by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]) (by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]) (by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get])
  · intro r h1 h2 h3
    rw [hregs r h1 h2]
    simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h1,h2,h3]

def decoded (report : Bool) : Option (BitVec 16) → Except Nat Spec.Command
  | none => .error 400
  | some dc => .ok (if report then .reportTemp dc else .setpoint dc)

theorem as_number (report : Bool) (xs : List (BitVec 8)) :
    decoded report (DecimalSpec.parse xs) =
      WireSpec.number (if report then Spec.Command.reportTemp else Spec.Command.setpoint) xs := by
  cases report <;> cases he : DecimalSpec.parse xs <;> simp only [decoded,WireSpec.number,he,Bool.false_eq_true,ite_false,ite_true]

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (report : Bool) (value : Option (BitVec 16))
    (hp : c.pc = if report then 0x800020fe#32 else 0x80002098#32) (h : Decimal.Result c value) :
    ∃ d n, n ≤ 10 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (decoded report value) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  cases report with
  | false =>
    cases value with
    | none =>
      obtain ⟨d,ht,hpc,hresult,hregs,hcsr⟩ := point_none B c ram hp h
      exact ⟨d,10,by decide,ht,hpc,hresult,hregs,hcsr⟩
    | some dc =>
      obtain ⟨d,ht,hpc,hresult,hregs,hcsr⟩ := point_some B c ram dc hp h
      exact ⟨d,9,by decide,ht,hpc,hresult,hregs,hcsr⟩
  | true =>
    cases value with
    | none =>
      obtain ⟨d,ht,hpc,hresult,hregs,hcsr⟩ := temp_none B c ram hp h
      exact ⟨d,9,by decide,ht,hpc,hresult,hregs,hcsr⟩
    | some dc =>
      obtain ⟨d,ht,hpc,hresult,hregs,hcsr⟩ := temp_some B c ram dc hp h
      exact ⟨d,7,by decide,ht,hpc,hresult,hregs,hcsr⟩

end E5R.Thermostat.NumericResult
