-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ZeroEntry
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.ZeroEntry
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (n : Nat)
    (hp : c.pc = 0x80005638#32) (h10 : c.get 10 = p) (h11 : c.get 11 = 0#32)
    (h12 : c.get 12 = BitVec.ofNat 32 (4*n)) (hn : 4 ≤ n)
    (ha : p.toNat%4 = 0) (htop : p.toNat+4*n < 2^32) :
    Quiet.Steps B img 14 ⟨c,ram⟩ ⟨setup c p n,ram⟩ := by
  have hlen : (BitVec.ofNat 32 (4*n)).toNat = 4*n := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have hshort : taken .ltu (BitVec.ofNat 32 (4*n)) 16#32 = false := by
    change decide ((BitVec.ofNat 32 (4*n)).toNat < 16) = false
    rw [hlen]
    simp only [decide_eq_false_iff_not]
    omega
  have hmask : (BitVec.ofNat 32 (4*n)) &&& 0xfffffffc#32 = BitVec.ofNat 32 (4*n) :=
    WordZero.and_low_clear _ (by rw [hlen];omega)
  have hcmp' : p.ult (BitVec.ofNat 32 (4*n)+p) = true := by
    change decide (p.toNat < (BitVec.ofNat 32 (4*n)+p).toNat) = true
    rw [BitVec.add_comm,WordZero.add_nat p (4*n) htop]
    simp only [decide_eq_true_eq]
    omega
  have hshort' : (BitVec.ofNat 32 (4*n)).ult 16#32 = false := hshort
  have hneg := WordZero.neg_and_three p ha
  have hneg' : (-p) &&& 3#32 = 0#32 := by simpa using hneg
  have hself : p.ult p = false := by change decide (p.toNat < p.toNat) = false;simp
  let len := BitVec.ofNat 32 (4*n)
  let c1 := c.wr 13 16#32 0x8000563a#32
  let c2 := c1.goto 0x8000563e#32
  let c3 := c2.wr 13 (0#32-p) 0x80005642#32
  let c4 := c3.wr 13 0#32 0x80005644#32
  let c5 := c4.wr 14 p 0x80005648#32
  let c6 := c5.goto 0x8000565a#32
  let c7 := c6.wr 12 len 0x8000565c#32
  let c8 := c7.wr 13 len 0x80005660#32
  let c9 := c8.wr 13 (len+p) 0x80005662#32
  let c10 := c9.goto 0x80005666#32
  let c11 := c10.wr 15 0x01010000#32 0x8000566a#32
  let c12 := c11.wr 16 0#32 0x8000566e#32
  let c13 := c12.wr 15 0x01010101#32 0x80005672#32
  let c14 := c13.wr 15 0#32 0x80005676#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact ze2147505720) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp]
    simp only [alu,BitVec.zero_add,BitVec.add_zero,BitVec.sub_zero,BitVec.zero_and]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (2147505722#32).getLsbD 0 = false;decide) ze2147505722 fun o => ?_
    have h0 : c1.get 12 = len := by simp [c1,Core.wr_get,Core.get_zero,h10,h11,h12,len]
    have h1 : c1.get 13 = 16#32 := by simp [c1,Core.wr_get,Core.get_zero,h10,h11,h12,len]
    rw [exec_branch,h0,h1]
    rw [hshort]
    rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (2147505726#32).getLsbD 0 = false;decide) ze2147505726 fun o => ?_
    have h0 : c2.get 0 = 0#32 := by simp [c1,c2,Core.wr_get,Core.get_zero,h10,h11,h12,len]
    have h1 : c2.get 10 = p := by simp [c1,c2,Core.wr_get,Core.get_zero,h10,h11,h12,len]
    rw [exec_op,h0,h1]
    simp only [alu,BitVec.zero_add,BitVec.add_zero,BitVec.sub_zero,BitVec.zero_and]
    rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (2147505730#32).getLsbD 0 = false;decide) ze2147505730 fun o => ?_
    have h0 : c3.get 13 = 0#32-p := by simp [c1,c2,c3,Core.wr_get,Core.get_zero,h10,h11,h12,len]
    rw [exec_opimm,h0]
    simp only [alu]
    rw [hneg]
    rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (2147505732#32).getLsbD 0 = false;decide) ze2147505732 fun o => ?_
    have h0 : c4.get 10 = p := by simp [c1,c2,c3,c4,Core.wr_get,Core.get_zero,h10,h11,h12,len]
    have h1 : c4.get 13 = 0#32 := by simp [c1,c2,c3,c4,Core.wr_get,Core.get_zero,h10,h11,h12,len]
    rw [exec_op,h0,h1]
    simp only [alu,BitVec.zero_add,BitVec.add_zero,BitVec.sub_zero,BitVec.zero_and]
    rfl
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (2147505736#32).getLsbD 0 = false;decide) ze2147505736 fun o => ?_
    have h0 : c5.get 10 = p := by simp [c1,c2,c3,c4,c5,Core.wr_get,Core.get_zero,h10,h11,h12,len]
    have h1 : c5.get 14 = p := by simp [c1,c2,c3,c4,c5,Core.wr_get,Core.get_zero,h10,h11,h12,len]
    rw [exec_branch,h0,h1]
    have ht : taken .geu p p = true := by simp [taken,hself]
    rw [ht]
    simp only [ite_true]
    change interp B img o (jump c5 (0x80005648#32+0x12#32)) ram 0 [] = _
    rw [show 0x80005648#32+0x12#32 = 0x8000565a#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (2147505754#32).getLsbD 0 = false;decide) ze2147505754 fun o => ?_
    have h0 : c6.get 12 = len := by simp [c1,c2,c3,c4,c5,c6,Core.wr_get,Core.get_zero,h10,h11,h12,len]
    have h1 : c6.get 13 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,Core.wr_get,Core.get_zero,h10,h11,h12,len]
    rw [exec_op,h0,h1]
    simp only [alu,BitVec.zero_add,BitVec.add_zero,BitVec.sub_zero,BitVec.zero_and]
    rfl
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (2147505756#32).getLsbD 0 = false;decide) ze2147505756 fun o => ?_
    have h0 : c7.get 12 = len := by simp [c1,c2,c3,c4,c5,c6,c7,Core.wr_get,Core.get_zero,h10,h11,h12,len]
    rw [exec_opimm,h0]
    simp only [alu]
    rw [hmask]
    rfl
  have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine QuietDet.step_of (by change (2147505760#32).getLsbD 0 = false;decide) ze2147505760 fun o => ?_
    have h0 : c8.get 13 = len := by simp [c1,c2,c3,c4,c5,c6,c7,c8,Core.wr_get,Core.get_zero,h10,h11,h12,len]
    have h1 : c8.get 14 = p := by simp [c1,c2,c3,c4,c5,c6,c7,c8,Core.wr_get,Core.get_zero,h10,h11,h12,len]
    rw [exec_op,h0,h1]
    simp only [alu,BitVec.zero_add,BitVec.add_zero,BitVec.sub_zero,BitVec.zero_and]
    rfl
  have s9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine QuietDet.step_of (by change (2147505762#32).getLsbD 0 = false;decide) ze2147505762 fun o => ?_
    have h0 : c9.get 14 = p := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,Core.wr_get,Core.get_zero,h10,h11,h12,len]
    have h1 : c9.get 13 = len+p := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,Core.wr_get,Core.get_zero,h10,h11,h12,len]
    rw [exec_branch,h0,h1]
    have ht : taken .geu p (len+p) = false := by simp [taken,hcmp',len]
    rw [ht]
    rfl
  have s10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine QuietDet.step_of (by change (2147505766#32).getLsbD 0 = false;decide) ze2147505766 fun o => ?_
    rw [exec_lui]
    simp only [alu,BitVec.zero_add,BitVec.add_zero,BitVec.sub_zero,BitVec.zero_and]
    rfl
  have s11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine QuietDet.step_of (by change (2147505770#32).getLsbD 0 = false;decide) ze2147505770 fun o => ?_
    have h0 : c11.get 11 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,Core.wr_get,Core.get_zero,h10,h11,h12,len]
    rw [exec_opimm,h0]
    simp only [alu,BitVec.zero_add,BitVec.add_zero,BitVec.sub_zero,BitVec.zero_and]
    rfl
  have s12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine QuietDet.step_of (by change (2147505774#32).getLsbD 0 = false;decide) ze2147505774 fun o => ?_
    have h0 : c12.get 15 = 0x01010000#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,Core.wr_get,Core.get_zero,h10,h11,h12,len]
    rw [exec_opimm,h0]
    simp only [alu]
    rw [show 0x01010000#32+0x101#32 = 0x01010101#32 by decide +kernel]
    rfl
  have s13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine QuietDet.step_of (by change (2147505778#32).getLsbD 0 = false;decide) ze2147505778 fun o => ?_
    have h0 : c13.get 16 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,Core.wr_get,Core.get_zero,h10,h11,h12,len]
    have h1 : c13.get 15 = 0x01010101#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,Core.wr_get,Core.get_zero,h10,h11,h12,len]
    rw [exec_mul_checked,h0,h1]
    simp only [muldiv,BitVec.zero_mul]
    rfl
  exact .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.single s13)))))))))))))

end E5R.Thermostat.ZeroEntry
