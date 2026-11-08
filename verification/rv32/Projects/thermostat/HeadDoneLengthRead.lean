import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadDoneLengthRead
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp low high transfer length : Word) (h2 : c.get 2=sp) (h23 : c.get 23=transfer) (h24 : c.get 24=length) (h312 : ramRead ram (sp+312#32) .w=low) (h316 : ramRead ram (sp+316#32) .w=high) (stack : Memory.Block B sp 327) (ha : sp.toNat%4=0)
    (hp : c.pc=0x80003462#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003470#32 ∧
      d.get 18=low ∧ d.get 19=high ∧ d.get 10=alu .and transfer 1#32 ∧ d.get 24=length+2#32 ∧ (∀ r : Reg, r≠18 → r≠19 → r≠10 → r≠24 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 18 (low) 0x80003466#32
  let c2 := c1.wr 19 (high) 0x8000346a#32
  let c3 := c2.wr 10 (alu .and transfer 1#32) 0x8000346e#32
  let c4 := c3.wr 24 (length+2#32) 0x80003470#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147497058) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v2 : c.get 2=sp := by simp [Core.wr_get_ne,Core.wr_get,h2,h23,h24]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 78 ha) (Memory.block_access stack (off := 312) (by decide) (by decide)),h312];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003466#32).getLsbD 0=false;decide) hh2147497062 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h23,h24]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 79 ha) (Memory.block_access stack (off := 316) (by decide) (by decide)),h316];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000346a#32).getLsbD 0=false;decide) hh2147497066 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v23 : c2.get 23=transfer := by simp [c2,c1,Core.wr_get_ne,h23]
    rw [exec_opimm,v23];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x8000346e#32).getLsbD 0=false;decide) hh2147497070 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v24 : c3.get 24=length := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h23,h24]
    rw [exec_opimm,v24];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h23,h24]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h23,h24]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h23,h24]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h23,h24]
  · intro reg h18 h19 h10 h24;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h23,h24,h18,h19,h10,h24]
end E5R.Thermostat.HeadDoneLengthRead
