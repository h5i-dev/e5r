-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.SmallCopyStart
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.SmallCopyStart
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (dst : Word) (n : Nat)
    (hp : c.pc = 0x80005182#32) (h10 : c.get 10 = dst) (h12 : c.get 12 = BitVec.ofNat 32 n)
    (hn : n < 16) (hw : dst.toNat+n < 2^32) :
    ∃ d k, k ≤ 9 ∧ Quiet.Steps B img k ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if n = 0 then 0x8000530c#32 else 0x800052fc#32) ∧
      d.get 2 = c.get 2+0xfffffff0#32 ∧ d.get 13 = dst ∧ d.get 12 = BitVec.ofNat 32 n ∧
      Frame c d ∧ d.sameCsr c := by
  let c1 := c.wr 6 0x80005182#32 0x80005186#32
  let c2 := c1.goto 0x8000518a#32
  let c3 := c2.wr 2 (c.get 2+0xfffffff0#32) 0x8000518c#32
  let c4 := c3.wr 13 16#32 0x8000518e#32
  let c5 := c4.goto 0x80005200#32
  let c6 := c5.wr 13 dst 0x80005202#32
  let c7 := c6.wr 14 (dst+BitVec.ofNat 32 n) 0x80005206#32
  let a := c7.goto (if n = 0 then 0x8000520a#32 else 0x800052fc#32)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact cp2147504514) fun o => ?_
    rw [exec_auipc,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005186#32).getLsbD 0 = false;decide) cp2147504518 fun o => ?_
    have hv : c1.get 6 = 0x80005182#32 := by simp [c1,Core.wr_get]
    rw [exec_jalr,hv]
    change interp B img o (jump c1 ((0x80005182#32+8#32) &&& ~~~1)) ram 0 [] = _
    rw [show (0x80005182#32+8#32) &&& ~~~1 = 0x8000518a#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000518a#32).getLsbD 0 = false;decide) cp2147504522 fun o => ?_
    have hv : c2.get 2 = c.get 2 := by simp [c2,c1,Core.wr_get_ne]
    rw [exec_opimm,hv];rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000518c#32).getLsbD 0 = false;decide) cp2147504524 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000518e#32).getLsbD 0 = false;decide) cp2147504526 fun o => ?_
    have hv12 : c4.get 12 = BitVec.ofNat 32 n := by simp [c4,c3,c2,c1,Core.wr_get_ne,h12]
    have hv13 : c4.get 13 = 16#32 := by simp [c4,Core.wr_get]
    rw [exec_branch,hv12,hv13,ParamMath.ult n 16 (by omega) (by decide),decide_eq_true hn]
    simp only [ite_true]
    change interp B img o (jump c4 0x80005200#32) ram 0 [] = _
    rw [jump_ok _ _ (by decide)];rfl
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005200#32).getLsbD 0 = false;decide) cp2147504640 fun o => ?_
    have hv : c5.get 10 = dst := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,h10]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005202#32).getLsbD 0 = false;decide) cp2147504642 fun o => ?_
    have hv10 : c6.get 10 = dst := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h10]
    have hv12 : c6.get 12 = BitVec.ofNat 32 n := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h12]
    rw [exec_op,hv10,hv12];rfl
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨a,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005206#32).getLsbD 0 = false;decide) cp2147504646 fun o => ?_
    have hv10 : c7.get 10 = dst := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h10]
    have hv14 : c7.get 14 = dst+BitVec.ofNat 32 n := by simp [c7,Core.wr_get]
    rw [exec_branch,hv10,hv14,end_guard dst n hn hw]
    by_cases hz : n = 0
    · simp only [hz,Nat.lt_irrefl,decide_false,Bool.false_eq_true,ite_false,a,ite_true];rfl
    · have hnz : 0 < n := by omega
      rw [decide_eq_true hnz];simp only [ite_true,a,ite_eq_right hz]
      change interp B img o (jump c7 0x800052fc#32) ram 0 [] = _
      rw [jump_ok _ _ (by decide)];rfl
  have ta : Quiet.Steps B img 8 ⟨c,ram⟩ ⟨a,ram⟩ := .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.single s7)))))))
  have aframe : Frame c a := by
    intro r h2 h6 h13 h14
    simp [a,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h2,h6,h13,h14]
  have asp : a.get 2 = c.get 2+0xfffffff0#32 := by simp [a,c7,c6,c5,c4,c3,Core.wr_get_ne,Core.wr_get]
  have a13 : a.get 13 = dst := by simp [a,c7,c6,Core.wr_get_ne,Core.wr_get]
  have a12 : a.get 12 = BitVec.ofNat 32 n := (aframe 12 (by decide) (by decide) (by decide) (by decide)).trans h12
  by_cases hz : n = 0
  · let d := a.goto 0x8000530c#32
    have apc : a.pc = 0x8000520a#32 := by simp only [a,Core.goto_pc,hz,ite_true]
    have st : Quiet.Step B img ⟨a,ram⟩ ⟨d,ram⟩ := by
      refine QuietDet.step_of (by rw [apc];decide) (by rw [apc];exact cp2147504650) fun o => ?_
      rw [exec_jal,apc]
      change interp B img o (jump a 0x8000530c#32) ram 0 [] = _
      rw [jump_ok _ _ (by decide)];rfl
    exact ⟨d,9,by decide,ta.trans (.single st),by simp only [hz,ite_true];rfl,asp,a13,a12,aframe,by rfl⟩
  · exact ⟨a,8,by decide,ta,by simp only [a,Core.goto_pc,ite_eq_right hz],asp,a13,a12,aframe,by rfl⟩

end E5R.Thermostat.SmallCopyStart
