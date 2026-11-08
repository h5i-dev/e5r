import Projects.thermostat.HeaderCallerCode
import Projects.thermostat.Header
import Projects.thermostat.AuthLiterals
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HeaderCaller
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r ≠ 1 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 28 → r ≠ 29 →
  r.val < 10 ∨ 17 < r.val → d.get r = c.get r

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (req p : Word)
    (raw : List (BitVec 8)) (entries : List HeaderSpec.Entry) (h : Header.Pre B ram req p raw entries)
    (hquery : ReadBytes.Span B img ram 0x80005b68#32 (WireSpec.ascii "authorization"))
    (hp : c.pc = 0x8000052e#32) (h21 : c.get 21 = req) :
    ∃ d n, n ≤ 212*entries.length+19 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80000542#32 ∧
      HeaderResult.BytesAt B ram d (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) ∧ Frame c d ∧ d.sameCsr c := by
  let c1 := c.wr 11 0x80006000#32 0x80000532#32
  let c2 := c1.wr 11 0x80005b68#32 0x80000536#32
  let c3 := c2.wr 12 13#32 0x80000538#32
  let c4 := c3.wr 10 req 0x8000053a#32
  let c5 := c4.wr 1 0x8000253a#32 0x8000053e#32
  let a := c5.wr 1 0x80000542#32 0x800026c0#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact hq2147484974) fun o => ?_
    rw [exec_lui,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80000532#32).getLsbD 0 = false;decide) hq2147484978 fun o => ?_
    have hv : c1.get 11 = 0x80006000#32 := by simp [c1,Core.wr_get]
    rw [exec_opimm,hv];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80000536#32).getLsbD 0 = false;decide) hq2147484982 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80000538#32).getLsbD 0 = false;decide) hq2147484984 fun o => ?_
    have hv : c3.get 21 = req := by simp [c3,c2,c1,Core.wr_get_ne,h21]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu];rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x8000053a#32).getLsbD 0 = false;decide) hq2147484986 fun o => ?_
    rw [exec_auipc];rfl
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨a,ram⟩ := by
    refine detStep_of (by change (0x8000053e#32).getLsbD 0 = false;decide) hq2147484990 fun o => ?_
    have hv : c5.get 1 = 0x8000253a#32 := by simp [c5,Core.wr_get]
    rw [exec_jalr,hv,show (0x8000253a#32+390#32) &&& ~~~(1 : Word) = 0x800026c0#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  obtain ⟨d,n,hn,ht,hpc,hresult,hframe,hcsr⟩ := Header.bytes_contract B a ram req p 0x80005b68#32 raw
    (WireSpec.ascii "authorization") entries h hquery rfl rfl
    (by simp [a,c5,c4,Core.wr_get_ne,Core.wr_get]) (by simp [a,c5,c4,c3,c2,Core.wr_get_ne,Core.wr_get])
    (by simp [a,c5,c4,c3,Core.wr_get_ne,Core.wr_get])
  have hra : a.get 1 = 0x80000542#32 := by simp [a,Core.wr_get]
  refine ⟨d,6+n,by omega,(DetSteps.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5)))))).trans ht,?_,hresult,?_,hcsr⟩
  · rw [hpc,hra];decide +kernel
  · intro r h1 h5 h6 h7 h28 h29 hr
    rw [hframe r h5 h6 h7 h28 h29 hr]
    simp [a,c5,c4,c3,c2,c1,Core.wr_get_ne,h1,Header.outside r 10 hr (by decide),Header.outside r 11 hr (by decide),Header.outside r 12 hr (by decide)]
end E5R.Thermostat.HeaderCaller
