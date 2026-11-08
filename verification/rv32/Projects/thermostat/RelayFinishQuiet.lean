-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.RelayFinish
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.CommandPackQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.RelayFinish
theorem success_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (idx : Word) (on : Bool)
    (hp : c.pc = 0x80002200#32) (hi : idx.toNat < 256) (h12 : c.get 12 = idx) (h13 : c.get 13 = if on then 1#32 else 0#32) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (.ok (.relay (idx.setWidth 8) on)) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (idx <<< 8) 0x80002202#32
  let c2 := c1.wr 10 (2#32) 0x80002204#32
  let c3 := c2.wr 11 (if on then 1#32 else 0#32) 0x80002206#32
  let c4 := c3.goto 0x8000220c#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact wd2147492352) fun o => ?_
    have hv0 : c.get 12 = (idx) := by simp [Core.wr_get_ne,Core.wr_get,h12,h13]
    rw [exec_opimm,hv0,hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002202#32).getLsbD 0 = false;decide) wd2147492354 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002204#32).getLsbD 0 = false;decide) wd2147492356 fun o => ?_
    have hv1 : c2.get 13 = (if on then 1#32 else 0#32) := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h12,h13]
    rw [exec_op,Core.get_zero,hv1]
    simp only [alu];rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002206#32).getLsbD 0 = false;decide) wd2147492358 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c3 (0x80002206#32+0x6#32)) ram 0 [] = _
    rw [show 0x80002206#32+0x6#32 = 0x8000220c#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have ht : Quiet.Steps B img 4 ⟨c,ram⟩ ⟨c4,ram⟩ := .step s0 (.step s1 (.step s2 (.single s3)))
  obtain ⟨hpc,hvalue,hregs,hcsr⟩ := CommandPack.fields c4
  refine ⟨CommandPack.execute c4,ht.trans (E5R.Thermostat.CommandPack.contract_quiet B c4 ram rfl),hpc,?_,?_,hcsr⟩
  · rw [hvalue]
    have htag : c4.get 10 = 2#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hfield : c4.get 12 = idx <<< 8 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hbool : c4.get 11 = (if on then 1#32 else 0#32) := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [htag,hfield,hbool];exact CommandBytes.relay idx hi on
  · intro r h1 h2 h3
    rw [hregs r h1 h2];simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h1,h2,h3]

end E5R.Thermostat.RelayFinish
namespace E5R.Thermostat.RelayFinish
theorem notfound_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x800021d8#32) (h10 : c.get 10 = 255#32) (h12 : c.get 12 = 0#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (.error 404) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (404#32) 0x800021dc#32
  let c2 := c1.goto 0x8000220c#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact wd2147492312) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x800021dc#32).getLsbD 0 = false;decide) wd2147492316 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c1 (0x800021dc#32+0x30#32)) ram 0 [] = _
    rw [show 0x800021dc#32+0x30#32 = 0x8000220c#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have ht : Quiet.Steps B img 2 ⟨c,ram⟩ ⟨c2,ram⟩ := .step s0 (.single s1)
  obtain ⟨hpc,hvalue,hregs,hcsr⟩ := CommandPack.fields c2
  refine ⟨CommandPack.execute c2,ht.trans (E5R.Thermostat.CommandPack.contract_quiet B c2 ram rfl),hpc,?_,?_,hcsr⟩
  · rw [hvalue]
    have htag : c2.get 10 = 255#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10]
    have hfield : c2.get 12 = 0#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h12]
    have hstatus : c2.get 11 = 404#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [htag,hfield,hstatus];unfold WireSpec.ResultWord;decide +kernel
  · intro r h1 h2 h3
    rw [hregs r h1 h2];simp [c2,c1,Core.wr_get_ne,Core.wr_get,h1,h2,h3]

end E5R.Thermostat.RelayFinish
namespace E5R.Thermostat.RelayFinish
theorem on_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (idx : Word)
    (hp : c.pc = 0x800021d4#32) (hi : idx.toNat < 256) (h12 : c.get 12 = idx) :
    ∃ d, Quiet.Steps B img 9 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (.ok (.relay (idx.setWidth 8) true)) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 13 1#32 0x800021d6#32
  let c2 := c1.goto 0x80002200#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact wd2147492308) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x800021d6#32).getLsbD 0 = false;decide) wd2147492310 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c1 (0x800021d6#32+42#32)) ram 0 [] = _
    rw [show 0x800021d6#32+42#32 = 0x80002200#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  obtain ⟨d,ht,hpc,hval,hregs,hcsr⟩ := E5R.Thermostat.RelayFinish.success_quiet B c2 ram idx true rfl hi
    (by simp [c2,c1,Core.wr_get_ne,h12]) (by simp [c2,c1,Core.wr_get])
  refine ⟨d,(Quiet.Steps.step s0 (.single s1)).trans ht,hpc,hval,?_,hcsr⟩
  intro r h1 h2 h3 h4;rw [hregs r h1 h2 h3];simp [c2,c1,Core.wr_get_ne,h4]

end E5R.Thermostat.RelayFinish
