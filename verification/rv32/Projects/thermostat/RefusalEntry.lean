import Projects.thermostat.RefusalCode
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.RefusalEntry
open E5R E5R.Thermostat

theorem present (B : Board) (c : Core) (ram : Word → BitVec 8) (hp : c.pc = 0x800005a2#32) :
    ∃ d, DetSteps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800005aa#32 ∧ d.get 10 = 0#32 ∧ d.get 18 = 0#32 ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 18 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 18 0#32 0x800005a4#32
  let c2 := c1.wr 10 0#32 0x800005a6#32
  let d := c2.goto 0x800005aa#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact rf2147485090) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x800005a4#32).getLsbD 0 = false;decide) rf2147485092 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x800005a6#32).getLsbD 0 = false;decide) rf2147485094 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c2 0x800005aa#32) ram 0 [] = _
    rw [jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step s0 (.step s1 (.single s2)),rfl,?_,?_,?_,by rfl⟩
  · simp [d,c2,Core.wr_get]
  · simp [d,c2,c1,Core.wr_get]
  · intro r h10 h18
    simp [d,c2,c1,Core.wr_get_ne,h10,h18]

theorem missing (B : Board) (c : Core) (ram : Word → BitVec 8) (hp : c.pc = 0x800005a8#32) (hz : c.get 10 = 0#32) :
    ∃ d, DetSteps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800005aa#32 ∧ d.get 10 = 0#32 ∧ d.get 18 = 0#32 ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 18 → d.get r = c.get r) ∧ d.sameCsr c := by
  let d := c.wr 18 0#32 0x800005aa#32
  have st : DetStep B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact rf2147485096) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  refine ⟨d,.single st,rfl,?_,?_,?_,by rfl⟩
  · exact (Core.wr_get_ne _ _ _ _ _ (by decide)).trans hz
  · simp [d,Core.wr_get]
  · intro r h10 h18;exact Core.wr_get_ne _ _ _ _ _ h18
theorem choose (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x800005a2#32 ∨ (c.pc = 0x800005a8#32 ∧ c.get 10 = 0#32)) :
    ∃ d n, n ≤ 3 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800005aa#32 ∧ d.get 10 = 0#32 ∧ d.get 18 = 0#32 ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 18 → d.get r = c.get r) ∧ d.sameCsr c := by
  rcases hp with hp|⟨hp,hz⟩
  · obtain ⟨d,ht,hpc,h10,h18,hf,hc⟩ := present B c ram hp
    exact ⟨d,3,by decide,ht,hpc,h10,h18,hf,hc⟩
  · obtain ⟨d,ht,hpc,h10,h18,hf,hc⟩ := missing B c ram hp hz
    exact ⟨d,1,by decide,ht,hpc,h10,h18,hf,hc⟩
end E5R.Thermostat.RefusalEntry
