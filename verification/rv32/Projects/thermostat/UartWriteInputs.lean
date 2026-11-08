import Projects.thermostat.UartWriteCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.UartWriteInputs
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (obj io src len : Word) :=
  ramWrite (ram) (obj+12#32) (io) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (obj io src len : Word) (h10 : c.get 10=obj) (hm : Memory.Block B obj 41) (ha : obj.toNat%4=0)
    (h0 : ramRead ram obj .w=io) (h4 : ramRead ram (obj+4#32) .w=src) (h8 : ramRead ram (obj+8#32) .w=len)
    (hp : c.pc=0x800007ae#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,memory ram obj io src len⟩ ∧ d.pc=0x800007c8#32 ∧
      d.get 14=io ∧ d.get 11=src ∧ d.get 12=len ∧ (∀ r : Reg, r≠14 → r≠11 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (io) 0x800007b0#32
  let c2 := c1.wr 11 (src) 0x800007b2#32
  let c3 := c2.wr 12 (len) 0x800007b4#32
  let r1 := ramWrite ram (obj+12#32) (io) .w
  let c4 := c3.goto 0x800007b6#32
  let c5 := c4.goto 0x800007c8#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact uw2147485614) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have hv : c.get 10=obj := by simp [Core.wr_get_ne,Core.wr_get,h10,h0,h4,h8]
    rw [exec_load,hv,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o ha (by simpa only [BitVec.add_zero] using Memory.block_access hm (off := 0) (by decide) (by decide)),h0];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800007b0#32).getLsbD 0=false;decide) uw2147485616 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have hv : c1.get 10=obj := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h0,h4,h8]
    rw [exec_load,hv,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 1 ha) (Memory.block_access hm (off := 4) (by decide) (by decide)),h4];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800007b2#32).getLsbD 0=false;decide) uw2147485618 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have hv : c2.get 10=obj := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h0,h4,h8]
    rw [exec_load,hv,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide)),h8];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,r1⟩ := by
    refine Quiet.step_of (by change (0x800007b4#32).getLsbD 0=false;decide) uw2147485620 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 r1 [],[]⟩
    have v10 : c3.get 10=obj := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h0,h4,h8]
    have v14 : c3.get 14=io := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h0,h4,h8]
    rw [exec_store,v10,v14,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r1⟩ ⟨c5,r1⟩ := by
    refine Quiet.step_of (by change (0x800007b6#32).getLsbD 0=false;decide) uw2147485622 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r1 0 [] [] = ⟨.ok c5 r1 [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c4 0x800007c8#32) r1 0 [] [] = _
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c5,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h0,h4,h8]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h0,h4,h8]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h0,h4,h8]
  · intro reg h14 h11 h12;simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h0,h4,h8,h14,h11,h12]
end E5R.Thermostat.UartWriteInputs
