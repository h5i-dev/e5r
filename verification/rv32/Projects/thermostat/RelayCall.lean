import Projects.thermostat.Param
import Projects.thermostat.DecodeCode
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.RelayCall
open E5R E5R.Thermostat

theorem outside (r k : Reg) (hr : r.val < 10 ∨ 17 < r.val) (hk : 10 ≤ k.val ∧ k.val ≤ 17) : r ≠ k := by
  intro he;have hv := congrArg Fin.val he;omega

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (req : Word)
    (first : Option (List (BitVec 8))) (h : Param.Pre B ram req first)
    (hp : c.pc = 0x80002194#32) (hreq : c.get 10 = req) :
    ∃ d n, n ≤ 206 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x8000219e#32 ∧
      ParamReturn.Result d (first.bind WireSpec.parseU32) ∧
      (∀ r : Reg, r ≠ 1 → r ≠ 5 → r.val < 10 ∨ 17 < r.val → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 0#32 0x80002196#32
  let c2 := c1.wr 1 0x80002196#32 0x8000219a#32
  let a := c2.wr 1 0x8000219e#32 0x8000278a#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wd2147492244) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80002196#32).getLsbD 0 = false;decide) wd2147492246 fun o => ?_
    rw [exec_auipc,BitVec.add_zero];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨a,ram⟩ := by
    refine detStep_of (by change (0x8000219a#32).getLsbD 0 = false;decide) wd2147492250 fun o => ?_
    have hv : c2.get 1 = 0x80002196#32 := by simp [c2,Core.wr_get]
    rw [exec_jalr,hv,show (0x80002196#32+1524#32) &&& ~~~(1 : Word) = 0x8000278a#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  obtain ⟨d,n,hn,ht,hpc,hresult,hframe,hcsr⟩ := Param.contract B a ram req first h rfl
    (by simp [a,c2,c1,Core.wr_get_ne,hreq]) (by simp [a,c2,c1,Core.wr_get_ne,Core.wr_get])
  refine ⟨d,3+n,by omega,(DetSteps.step s0 (.step s1 (.single s2))).trans ht,?_,hresult,?_,hcsr⟩
  · have hra : a.get 1 = 0x8000219e#32 := by simp [a,Core.wr_get]
    rw [hpc,hra];decide +kernel
  · intro r h1 h5 hr
    have h10 := outside r 10 hr (by decide)
    have h11 := outside r 11 hr (by decide)
    rw [hframe r h5 h10 h11 (outside r 12 hr (by decide)) (outside r 13 hr (by decide))
      (outside r 14 hr (by decide)) (outside r 15 hr (by decide))
      (outside r 16 hr (by decide)) (outside r 17 hr (by decide))]
    simp [a,c2,c1,Core.wr_get_ne,h1,h11]
end E5R.Thermostat.RelayCall
