import Projects.thermostat.LoopInitCode
namespace E5R.Thermostat.LoopEntry
open E5R E5R.Thermostat

def setup (c : Core) : Core :=
  let c1 := c.wr 23 0x80fff38f#32 0x8000095c#32
  let c2 := c1.wr 23 0x80fff9f0#32 0x80000960#32
  let c3 := c2.wr 21 0xffffffff#32 0x80000962#32
  c3.goto 0x80000978#32

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000958#32) (hsp : c.get 2 = 0x80ffeb90#32) :
    DetSteps B img 4 ⟨c,ram⟩ ⟨setup c,ram⟩ := by
  let c1 := c.wr 23 0x80fff38f#32 0x8000095c#32
  let c2 := c1.wr 23 0x80fff9f0#32 0x80000960#32
  let c3 := c2.wr 21 0xffffffff#32 0x80000962#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact li2147486040) fun o => ?_
    rw [exec_opimm,hsp,hp]
    simp only [alu]
    rw [show 0x80ffeb90#32+2047#32 = 0x80fff38f#32 by decide +kernel]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x8000095c#32).getLsbD 0 = false;decide) li2147486044 fun o => ?_
    have hv : c1.get 23 = 0x80fff38f#32 := by simp [c1,Core.wr_get]
    rw [exec_opimm,hv]
    simp only [alu]
    rw [show 0x80fff38f#32+1633#32 = 0x80fff9f0#32 by decide +kernel]
    rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80000960#32).getLsbD 0 = false;decide) li2147486048 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    simp only [alu,BitVec.zero_add]
    rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨setup c,ram⟩ := by
    refine detStep_of (by change (0x80000962#32).getLsbD 0 = false;decide) li2147486050 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c3 (0x80000962#32+0x16#32)) ram 0 [] = _
    rw [show 0x80000962#32+0x16#32 = 0x80000978#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  exact .step s0 (.step s1 (.step s2 (.single s3)))

theorem fields (c : Core) :
    (setup c).pc = 0x80000978#32 ∧ (setup c).get 23 = 0x80fff9f0#32 ∧
    (setup c).get 21 = 0xffffffff#32 ∧
    (∀ r : Reg, r ≠ 21 → r ≠ 23 → (setup c).get r = c.get r) ∧ (setup c).sameCsr c := by
  refine ⟨rfl,rfl,rfl,?_,by rfl⟩
  intro r h21 h23
  simp [setup,Core.wr_get_ne,h21,h23]
end E5R.Thermostat.LoopEntry
