import Projects.thermostat.HeadObservedByte
import Projects.thermostat.HeadFoldMath
import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadTeFoldRaw
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (ptr literal : Word) (actual expected : BitVec 8) (h20 : c.get 20=ptr) (h13 : c.get 13=literal) (inputByte : ReadBytes.Byte B img ram ptr actual) (literalByte : ReadBytes.Byte B img ram literal expected)
    (hp : c.pc=0x8000328e#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800032a2#32 ∧
      d.get 12=HeadFoldMath.word actual ∧ d.get 14=alu .sll (alu .sltu (alu .add (BitVec.ofNat 32 actual.toNat) 0xffffffbf#32) 26#32) 5#32 ∧ d.get 29=BitVec.ofNat 32 expected.toNat ∧ (∀ r : Reg, r≠12 → r≠14 → r≠29 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (BitVec.ofNat 32 actual.toNat) 0x80003292#32
  let c2 := c1.wr 14 (alu .add (BitVec.ofNat 32 actual.toNat) 0xffffffbf#32) 0x80003296#32
  let c3 := c2.wr 29 (BitVec.ofNat 32 expected.toNat) 0x8000329a#32
  let c4 := c3.wr 14 (alu .sltu (alu .add (BitVec.ofNat 32 actual.toNat) 0xffffffbf#32) 26#32) 0x8000329e#32
  let c5 := c4.wr 14 (alu .sll (alu .sltu (alu .add (BitVec.ofNat 32 actual.toNat) 0xffffffbf#32) 26#32) 5#32) 0x800032a0#32
  let c6 := c5.wr 12 (HeadFoldMath.word actual) 0x800032a2#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496590) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h20,BitVec.add_zero,HeadObservedByte.load inputByte o]
    rw [ReadBytes.extend_byte,←Memory.ofNat_width];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003292#32).getLsbD 0=false;decide) hh2147496594 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v12 : c1.get 12=BitVec.ofNat 32 actual.toNat := by simp [c1,Core.wr_get_ne,Core.wr_get,h20,h13]
    rw [exec_opimm,v12];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80003296#32).getLsbD 0=false;decide) hh2147496598 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v13 : c2.get 13=literal := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h20,h13]
    rw [exec_load,v13,BitVec.add_zero,HeadObservedByte.load literalByte o]
    rw [ReadBytes.extend_byte,←Memory.ofNat_width];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x8000329a#32).getLsbD 0=false;decide) hh2147496602 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v14 : c3.get 14=alu .add (BitVec.ofNat 32 actual.toNat) 0xffffffbf#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h20,h13]
    rw [exec_opimm,v14];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x8000329e#32).getLsbD 0=false;decide) hh2147496606 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v14 : c4.get 14=alu .sltu (alu .add (BitVec.ofNat 32 actual.toNat) 0xffffffbf#32) 26#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h20,h13]
    rw [exec_opimm,v14];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800032a0#32).getLsbD 0=false;decide) hh2147496608 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v12 : c5.get 12=BitVec.ofNat 32 actual.toNat := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h20,h13]
    have v14 : c5.get 14=alu .sll (alu .sltu (alu .add (BitVec.ofNat 32 actual.toNat) 0xffffffbf#32) 26#32) 5#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h20,h13]
    rw [exec_op,v12,v14];first | rfl | (rw [hp];rfl)
  refine ⟨c6,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h20,h13]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h20,h13]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h20,h13]
  · intro reg h12 h14 h29;simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h20,h13,h12,h14,h29]
end E5R.Thermostat.HeadTeFoldRaw
