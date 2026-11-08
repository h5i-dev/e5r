import Projects.thermostat.CommandPack
import Projects.thermostat.CommandBytes
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ModeFinish
open E5R E5R.Thermostat

theorem error (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x8000220a#32) (htag : c.get 10 = 255#32) (hstatus : c.get 11 = 400#32) :
    ∃ d, DetSteps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (.error 400) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 0#32 0x8000220c#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wd2147492362) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have ht : DetSteps B img 1 ⟨c,ram⟩ ⟨c1,ram⟩ := .single s0
  obtain ⟨hpc,hvalue,hregs,hcsr⟩ := CommandPack.fields c1
  refine ⟨CommandPack.execute c1,ht.trans (CommandPack.contract B c1 ram rfl),hpc,?_,?_,hcsr⟩
  · exact CommandPack.error400 c1 (by simp [c1,Core.wr_get_ne,Core.wr_get,htag]) (by simp [c1,Core.wr_get_ne,Core.wr_get]) (by simp [c1,Core.wr_get_ne,Core.wr_get,hstatus])
  · intro r h1 h2 h3
    rw [hregs r h1 h2];simp [c1,Core.wr_get_ne,Core.wr_get,h1,h2,h3]

theorem off (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80002288#32) :
    ∃ d, DetSteps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (.ok (.mode .off)) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 3#32 0x8000228a#32
  let c2 := c1.goto 0x8000220a#32
  let c3 := c2.wr 12 0#32 0x8000220c#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wd2147492488) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x8000228a#32).getLsbD 0 = false;decide) wd2147492490 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c1 (0x8000228a#32+0xffffff80#32)) ram 0 [] = _
    rw [show 0x8000228a#32+0xffffff80#32 = 0x8000220a#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x8000220a#32).getLsbD 0 = false;decide) wd2147492362 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have ht : DetSteps B img 3 ⟨c,ram⟩ ⟨c3,ram⟩ := .step s0 (.step s1 (.single s2))
  obtain ⟨hpc,hvalue,hregs,hcsr⟩ := CommandPack.fields c3
  refine ⟨CommandPack.execute c3,ht.trans (CommandPack.contract B c3 ram rfl),hpc,?_,?_,hcsr⟩
  · change WireSpec.CommandWord _ _
    rw [hvalue]
    have h10 : c3.get 10 = 3#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have h12 : c3.get 12 = CommandBytes.modeField .off := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,CommandBytes.modeField,Encoding.modeByte]
    rw [h10,h12];exact CommandBytes.mode _ .off
  · intro r h1 h2 h3
    rw [hregs r h1 h2];simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h1,h2,h3]

theorem heat (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80002254#32) :
    ∃ d, DetSteps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (.ok (.mode .heat)) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 3#32 0x80002256#32
  let c2 := c1.wr 12 256#32 0x8000225a#32
  let c3 := c2.goto 0x8000220c#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wd2147492436) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80002256#32).getLsbD 0 = false;decide) wd2147492438 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x8000225a#32).getLsbD 0 = false;decide) wd2147492442 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c2 (0x8000225a#32+0xffffffb2#32)) ram 0 [] = _
    rw [show 0x8000225a#32+0xffffffb2#32 = 0x8000220c#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have ht : DetSteps B img 3 ⟨c,ram⟩ ⟨c3,ram⟩ := .step s0 (.step s1 (.single s2))
  obtain ⟨hpc,hvalue,hregs,hcsr⟩ := CommandPack.fields c3
  refine ⟨CommandPack.execute c3,ht.trans (CommandPack.contract B c3 ram rfl),hpc,?_,?_,hcsr⟩
  · change WireSpec.CommandWord _ _
    rw [hvalue]
    have h10 : c3.get 10 = 3#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have h12 : c3.get 12 = CommandBytes.modeField .heat := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,CommandBytes.modeField,Encoding.modeByte]
    rw [h10,h12];exact CommandBytes.mode _ .heat
  · intro r h1 h2 h3
    rw [hregs r h1 h2];simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h1,h2,h3]

theorem auto (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80002280#32) :
    ∃ d, DetSteps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (.ok (.mode .auto)) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 3#32 0x80002282#32
  let c2 := c1.wr 12 512#32 0x80002286#32
  let c3 := c2.goto 0x8000220c#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wd2147492480) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80002282#32).getLsbD 0 = false;decide) wd2147492482 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80002286#32).getLsbD 0 = false;decide) wd2147492486 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c2 (0x80002286#32+0xffffff86#32)) ram 0 [] = _
    rw [show 0x80002286#32+0xffffff86#32 = 0x8000220c#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have ht : DetSteps B img 3 ⟨c,ram⟩ ⟨c3,ram⟩ := .step s0 (.step s1 (.single s2))
  obtain ⟨hpc,hvalue,hregs,hcsr⟩ := CommandPack.fields c3
  refine ⟨CommandPack.execute c3,ht.trans (CommandPack.contract B c3 ram rfl),hpc,?_,?_,hcsr⟩
  · change WireSpec.CommandWord _ _
    rw [hvalue]
    have h10 : c3.get 10 = 3#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have h12 : c3.get 12 = CommandBytes.modeField .auto := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,CommandBytes.modeField,Encoding.modeByte]
    rw [h10,h12];exact CommandBytes.mode _ .auto
  · intro r h1 h2 h3
    rw [hregs r h1 h2];simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h1,h2,h3]
end E5R.Thermostat.ModeFinish
