import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadClOverflowRaw
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp high low limit : Word) (h2 : c.get 2=sp) (h13 : c.get 13=high) (h14 : c.get 14=low) (hlimit : ramRead ram (sp+8#32) .w=limit) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0)
    (hp : c.pc=0x80003244#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003252#32 ∧
      d.get 12=alu .or (alu .sltu limit low) (alu .sltu (0 : Word) high) ∧ d.get 29=alu .sltu limit low ∧ (∀ r : Reg, r≠12 → r≠29 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (alu .sltu (0 : Word) high) 0x80003248#32
  let c2 := c1.wr 29 (limit) 0x8000324a#32
  let c3 := c2.wr 29 (alu .sltu limit low) 0x8000324e#32
  let c4 := c3.wr 12 (alu .or (alu .sltu limit low) (alu .sltu (0 : Word) high)) 0x80003252#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496516) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_op,Core.get_zero,h13];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003248#32).getLsbD 0=false;decide) hh2147496520 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 2 ha)
     (Memory.block_access stack (off := 8) (by decide) (by decide)),hlimit];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000324a#32).getLsbD 0=false;decide) hh2147496522 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v29 : c2.get 29=limit := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14]
    have v14 : c2.get 14=low := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14]
    rw [exec_op,v29,v14];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x8000324e#32).getLsbD 0=false;decide) hh2147496526 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v29 : c3.get 29=alu .sltu limit low := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14]
    have v12 : c3.get 12=alu .sltu (0 : Word) high := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14]
    rw [exec_op,v29,v12];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14]
  · intro reg h12 h29;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h12,h29]
end E5R.Thermostat.HeadClOverflowRaw
