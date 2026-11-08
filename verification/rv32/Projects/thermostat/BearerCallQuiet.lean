-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.BearerCall
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.MemcmpQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.BearerCall
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p len : Word) (xs : List (BitVec 8))
    (hx : ReadBytes.Span B img ram p xs) (hl : xs.length = 7)
    (hy : ReadBytes.Span B img ram 0x80005b75#32 (WireSpec.ascii "Bearer "))
    (hp : c.pc = 0x80000550#32) (h10 : c.get 10 = p) (h11 : c.get 11 = len) :
    ∃ d n, n ≤ 59 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80000566#32 ∧
      d.get 10 = MemcmpSpec.value xs (WireSpec.ascii "Bearer ") ∧
      d.get 24 = p ∧ d.get 25 = len ∧
      (∀ r : Reg, r ≠ 1 → r ≠ 24 → r ≠ 25 → r.val < 10 ∨ 14 < r.val → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 25 len 0x80000552#32
  let c2 := c1.wr 11 0x80006000#32 0x80000556#32
  let c3 := c2.wr 11 0x80005b75#32 0x8000055a#32
  let c4 := c3.wr 12 7#32 0x8000055c#32
  let c5 := c4.wr 24 p 0x8000055e#32
  let c6 := c5.wr 1 0x8000555e#32 0x80000562#32
  let a := c6.wr 1 0x80000566#32 0x80005162#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact be2147485008) fun o => ?_
    rw [exec_op,Core.get_zero,h11,hp]
    simp only [alu];rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80000552#32).getLsbD 0 = false;decide) be2147485010 fun o => ?_
    rw [exec_lui];rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80000556#32).getLsbD 0 = false;decide) be2147485014 fun o => ?_
    have hv : c2.get 11 = 0x80006000#32 := by simp [c2,Core.wr_get]
    rw [exec_opimm,hv];rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000055a#32).getLsbD 0 = false;decide) be2147485018 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000055c#32).getLsbD 0 = false;decide) be2147485020 fun o => ?_
    have hv : c4.get 10 = p := by simp [c4,c3,c2,c1,Core.wr_get_ne,h10]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu];rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000055e#32).getLsbD 0 = false;decide) be2147485022 fun o => ?_
    rw [exec_auipc];rfl
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨a,ram⟩ := by
    refine QuietDet.step_of (by change (0x80000562#32).getLsbD 0 = false;decide) be2147485026 fun o => ?_
    have hv : c6.get 1 = 0x8000555e#32 := by simp [c6,Core.wr_get]
    rw [exec_jalr,hv,show (0x8000555e#32+0xfffffc04#32) &&& ~~~(1 : Word) = 0x80005162#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have a10 : a.get 10 = p := by simp [a,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h10]
  have a11 : a.get 11 = 0x80005b75#32 := by simp [a,c6,c5,c4,c3,Core.wr_get_ne,Core.wr_get]
  have a12 : a.get 12 = BitVec.ofNat 32 xs.length := by simp [a,c6,c5,c4,Core.wr_get_ne,Core.wr_get,hl]
  obtain ⟨d,n,hn,ht,hpc,hval,hframe,hcsr⟩ := E5R.Thermostat.Memcmp.contract_quiet B a ram p 0x80005b75#32 xs (WireSpec.ascii "Bearer ") hx hy hl rfl a10 a11 a12
  have hra : a.get 1 = 0x80000566#32 := by simp [a,Core.wr_get]
  refine ⟨d,7+n,by rw [hl] at hn;omega,(Quiet.Steps.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.single s6))))))).trans ht,?_,hval,?_,?_,?_,hcsr⟩
  · rw [hpc,hra];decide +kernel
  · rw [hframe 24 (by decide)];simp [a,c6,c5,Core.wr_get_ne,Core.wr_get]
  · rw [hframe 25 (by decide)];simp [a,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro r h1 h24 h25 hr
    rw [hframe r hr]
    simp [a,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h1,h24,h25,
      MemcmpLoop.outside r 11 hr (by decide),MemcmpLoop.outside r 12 hr (by decide)]

end E5R.Thermostat.BearerCall
