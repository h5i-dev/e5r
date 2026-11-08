import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadTeSetup
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp start length : Word) (h2 : c.get 2=sp) (h24 : c.get 24=start) (hraw : ramRead ram (sp+48#32) .w=length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0)
    (hp : c.pc=0x80003274#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003284#32 ∧
      d.get 10=17#32 ∧ d.get 11=length-start ∧ d.get 13=0x80005dee#32 ∧ (∀ r : Reg, r≠10 → r≠11 → r≠13 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (length) 0x80003276#32
  let c2 := c1.wr 11 (length-start) 0x8000327a#32
  let c3 := c2.wr 10 (17#32) 0x8000327c#32
  let c4 := c3.wr 13 (0x80006000#32) 0x80003280#32
  let c5 := c4.wr 13 (0x80005dee#32) 0x80003284#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496564) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 12 ha)
     (Memory.block_access stack (off := 48) (by decide) (by decide)),hraw];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003276#32).getLsbD 0=false;decide) hh2147496566 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v10 : c1.get 10=length := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    have v24 : c1.get 24=start := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    rw [exec_op,v10,v24];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000327a#32).getLsbD 0=false;decide) hh2147496570 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x8000327c#32).getLsbD 0=false;decide) hh2147496572 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80003280#32).getLsbD 0=false;decide) hh2147496576 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v13 : c4.get 13=0x80006000#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    rw [exec_opimm,v13];first | rfl | (rw [hp];rfl)
  refine ⟨c5,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
  · intro reg h10 h11 h13;simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h10,h11,h13]
end E5R.Thermostat.HeadTeSetup
