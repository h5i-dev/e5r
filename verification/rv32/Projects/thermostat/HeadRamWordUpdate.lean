import Projects.thermostat.MemcpyCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadRamWordUpdate
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (src dst value : Word) :=
  ramWrite (ram) (dst+0#32) (value) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst value : Word) (h16 : c.get 16=src) (h14 : c.get 14=dst) (hvalue : ramRead ram src .w=value) (has : src.toNat%4=0) (had : dst.toNat%4=0) (source : B.inRam src 4=true) (destination : B.inRam dst 4=true)
    (hp : c.pc=0x80005212#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,memory ram src dst value⟩ ∧ d.pc=0x8000521e#32 ∧
      d.get 17=value ∧ d.get 14=dst+4#32 ∧ d.get 16=src+4#32 ∧ (∀ r : Reg, r≠17 → r≠14 → r≠16 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 17 (value) 0x80005216#32
  let r1 := ramWrite ram (dst+0#32) (value) .w
  let c2 := c1.goto 0x8000521a#32
  let c3 := c2.wr 14 (dst+4#32) 0x8000521c#32
  let c4 := c3.wr 16 (src+4#32) 0x8000521e#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact cp2147504658) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h16,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o has source,hvalue];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x80005216#32).getLsbD 0=false;decide) cp2147504662 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v14 : c1.get 14=dst := by simp [c1,Core.wr_get_ne,Core.wr_get,h16,h14]
    have v17 : c1.get 17=value := by simp [c1,Core.wr_get_ne,Core.wr_get,h16,h14]
    rw [exec_store,v14,v17,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (by simpa only [Width.bytes,BitVec.add_zero] using had) (by simpa only [Width.bytes,BitVec.add_zero] using destination)];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r1⟩ := by
    refine Quiet.step_of (by change (0x8000521a#32).getLsbD 0=false;decide) cp2147504666 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r1 [],[]⟩
    have v14 : c2.get 14=dst := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h16,h14]
    rw [exec_opimm,v14];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r1⟩ ⟨c4,r1⟩ := by
    refine Quiet.step_of (by change (0x8000521c#32).getLsbD 0=false;decide) cp2147504668 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r1 0 [] [] = ⟨.ok c4 r1 [],[]⟩
    have v16 : c3.get 16=src := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h16,h14]
    rw [exec_opimm,v16];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h16,h14]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h16,h14]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h16,h14]
  · intro reg h17 h14 h16;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h16,h14,h17,h14,h16]
end E5R.Thermostat.HeadRamWordUpdate
