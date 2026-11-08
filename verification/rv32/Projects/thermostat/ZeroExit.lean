import Projects.thermostat.ZeroMask
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ZeroExit
open E5R E5R.Thermostat

def finish (c : Core) (e : Word) : Core :=
  let c1 := c.wr 12 0#32 0x80005680#32
  let c2 := c1.wr 14 e 0x80005684#32
  let c3 := c2.goto 0x80005688#32
  let c4 := c3.goto 0x8000569e#32
  c4.goto (c.get 1 &&& ~~~1#32)

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (e : Word) (n : Nat)
    (hp : c.pc = 0x8000567e#32) (h12 : c.get 12 = BitVec.ofNat 32 (4*n))
    (h13 : c.get 13 = e) (hn : 4*n < 2^32) :
    DetSteps B img 5 ⟨c,ram⟩ ⟨finish c e,ram⟩ := by
  have hz : (BitVec.ofNat 32 (4*n)) &&& 3#32 = 0#32 := by
    rw [WordZero.and_three,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn]
    have hh : 4*n%4 = 0 := by omega
    rw [hh]
  have hself : e.ult e = false := by change decide (e.toNat < e.toNat) = false;simp
  let c1 := c.wr 12 0#32 0x80005680#32
  let c2 := c1.wr 14 e 0x80005684#32
  let c3 := c2.goto 0x80005688#32
  let c4 := c3.goto 0x8000569e#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact ze2147505790) fun o => ?_
    rw [exec_opimm,h12,hp]
    simp only [alu]
    rw [hz]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80005680#32).getLsbD 0 = false;decide) ze2147505792 fun o => ?_
    have ha : c1.get 13 = e := by simp [c1,Core.wr_get_ne,h13]
    have hb : c1.get 12 = 0#32 := by simp [c1,Core.wr_get]
    rw [exec_op,ha,hb]
    simp only [alu,BitVec.add_zero]
    rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80005684#32).getLsbD 0 = false;decide) ze2147505796 fun o => ?_
    have ha : c2.get 13 = e := by simp [c2,c1,Core.wr_get_ne,h13]
    have hb : c2.get 14 = e := by simp [c2,Core.wr_get]
    rw [exec_branch,ha,hb]
    have ht : taken .ltu e e = false := hself
    rw [ht]
    rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80005688#32).getLsbD 0 = false;decide) ze2147505800 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c3 (0x80005688#32+0x16#32)) ram 0 [] = _
    rw [show 0x80005688#32+0x16#32 = 0x8000569e#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨finish c e,ram⟩ := by
    refine detStep_of (by change (0x8000569e#32).getLsbD 0 = false;decide) ze2147505822 fun o => ?_
    have hra : c4.get 1 = c.get 1 := by simp [c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_jalr,hra,BitVec.add_zero,jump_ok _ _ (clear_bit0 _)]
    rfl
  exact .step s0 (.step s1 (.step s2 (.step s3 (.single s4))))

theorem fields (c : Core) (e : Word) :
    (finish c e).pc = c.get 1 &&& ~~~1#32 ∧
    (∀ r : Reg, r ≠ 12 → r ≠ 14 → (finish c e).get r = c.get r) ∧
    (finish c e).sameCsr c := by
  refine ⟨rfl,?_,by rfl⟩
  intro r h12 h14
  simp [finish,Core.wr_get_ne,h12,h14]
end E5R.Thermostat.ZeroExit
