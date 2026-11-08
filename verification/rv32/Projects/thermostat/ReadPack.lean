import Projects.thermostat.CommandPack
import Projects.thermostat.CommandBytes
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ReadPack
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80002016#32) :
    ∃ d, DetSteps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (.ok .read) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 0#32 0x80002018#32
  let c2 := c1.wr 10 4#32 0x8000201a#32
  let c3 := c2.goto 0x8000220c#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wd2147491862) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80002018#32).getLsbD 0 = false;decide) wd2147491864 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x8000201a#32).getLsbD 0 = false;decide) wd2147491866 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c2 (0x8000201a#32+0x1f2#32)) ram 0 [] = _
    rw [show 0x8000201a#32+0x1f2#32 = 0x8000220c#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have ht : DetSteps B img 3 ⟨c,ram⟩ ⟨c3,ram⟩ := .step s0 (.step s1 (.single s2))
  obtain ⟨hpc,hvalue,hregs,hcsr⟩ := CommandPack.fields c3
  refine ⟨CommandPack.execute c3,ht.trans (CommandPack.contract B c3 ram rfl),hpc,?_,?_,hcsr⟩
  · change WireSpec.CommandWord _ _
    rw [hvalue]
    have h10 : c3.get 10 = 4#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have h12 : c3.get 12 = 0#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [h10,h12,BitVec.or_zero]
    intro i b hb
    have hi := i.isLt
    have hz : i.val = 0 := by
      by_cases he : i.val = 0
      · exact he
      · have hc : i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
        rcases hc with h|h|h
        all_goals simp only [Encoding.commandByte,h] at hb
        all_goals contradiction
    simp only [Encoding.commandByte,Encoding.commandTag,hz] at hb
    have he := Option.some.inj hb;subst b
    simp only [hz,PackedBytes.byte_or,PackedBytes.shifted0,BitVec.or_zero]
    rfl
  · intro r h1 h2 h3
    rw [hregs r h1 h2];simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h1,h2,h3]

end E5R.Thermostat.ReadPack
