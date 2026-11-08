import Projects.thermostat.HeadObservedByte
import Projects.thermostat.HeadFoldMath
import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadClFoldRaw
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (ptr literal : Word) (actual expected : BitVec 8) (h31 : c.get 31=ptr) (h30 : c.get 30=literal) (inputByte : ReadBytes.Byte B img ram ptr actual) (literalByte : ReadBytes.Byte B img ram literal expected)
    (hp : c.pc=0x800031ba#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800031d0#32 ∧
      d.get 19=BitVec.ofNat 32 actual.toNat ∧ d.get 29=HeadFoldMath.word actual ∧ d.get 12=BitVec.ofNat 32 expected.toNat ∧ (∀ r : Reg, r≠19 → r≠29 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 19 (BitVec.ofNat 32 actual.toNat) 0x800031be#32
  let c2 := c1.wr 29 (alu .add (BitVec.ofNat 32 actual.toNat) 0xffffffbf#32) 0x800031c2#32
  let c3 := c2.wr 12 (BitVec.ofNat 32 expected.toNat) 0x800031c6#32
  let c4 := c3.wr 29 (alu .sltu (alu .add (BitVec.ofNat 32 actual.toNat) 0xffffffbf#32) 26#32) 0x800031ca#32
  let c5 := c4.wr 29 (alu .sll (alu .sltu (alu .add (BitVec.ofNat 32 actual.toNat) 0xffffffbf#32) 26#32) 5#32) 0x800031cc#32
  let c6 := c5.wr 29 (HeadFoldMath.word actual) 0x800031d0#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496378) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h31,BitVec.add_zero,HeadObservedByte.load inputByte o]
    rw [ReadBytes.extend_byte,←Memory.ofNat_width];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800031be#32).getLsbD 0=false;decide) hh2147496382 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v19 : c1.get 19=BitVec.ofNat 32 actual.toNat := by simp [c1,Core.wr_get_ne,Core.wr_get,h31,h30]
    rw [exec_opimm,v19];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800031c2#32).getLsbD 0=false;decide) hh2147496386 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v30 : c2.get 30=literal := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h31,h30]
    rw [exec_load,v30,BitVec.add_zero,HeadObservedByte.load literalByte o]
    rw [ReadBytes.extend_byte,←Memory.ofNat_width];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800031c6#32).getLsbD 0=false;decide) hh2147496390 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v29 : c3.get 29=alu .add (BitVec.ofNat 32 actual.toNat) 0xffffffbf#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h31,h30]
    rw [exec_opimm,v29];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800031ca#32).getLsbD 0=false;decide) hh2147496394 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v29 : c4.get 29=alu .sltu (alu .add (BitVec.ofNat 32 actual.toNat) 0xffffffbf#32) 26#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h31,h30]
    rw [exec_opimm,v29];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800031cc#32).getLsbD 0=false;decide) hh2147496396 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v19 : c5.get 19=BitVec.ofNat 32 actual.toNat := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h31,h30]
    have v29 : c5.get 29=alu .sll (alu .sltu (alu .add (BitVec.ofNat 32 actual.toNat) 0xffffffbf#32) 26#32) 5#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h31,h30]
    rw [exec_op,v19,v29];first | rfl | (rw [hp];rfl)
  refine ⟨c6,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h31,h30]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h31,h30]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h31,h30]
  · intro reg h19 h29 h12;simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h31,h30,h19,h29,h12]
end E5R.Thermostat.HeadClFoldRaw
