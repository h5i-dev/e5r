import Projects.thermostat.ReadCallSite
import Projects.thermostat.RamRun
import Projects.thermostat.Marshal
set_option linter.unusedSimpArgs false
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ReadDispatch
open E5R E5R.Thermostat

def next (c : Core) (ram : Word → BitVec 8) : Core :=
  let c1 := c.wr 11 2 0x80001a3a#32
  let c2 := c1.wr 18 (extend .b false (ramRead ram 0x80fffd42#32 .b)) 0x80001a3e#32
  let c3 := c2.wr 10 (extend .b false (ramRead ram 0x80fffd38#32 .b)) 0x80001a42#32
  c3.goto 0x80001a7e#32

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot)
    (hp : c.pc = 0x80001a38#32) (hfp : c.get 8 = 0x80fff814#32)
    (hm : Memory.Block B 0x80ffeb40#32 5312)
    (ho : Outcome.At ram 0x80fffd38#32 (.ok ⟨none,s⟩)) :
    DetSteps B img 4 ⟨c,ram⟩ ⟨next c ram,ram⟩ := by
  have ha : B.inRam (0x80fffd42#32) 1 = true := by
    exact Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4610) (width := 1) hm (by decide) (by decide)
  have hb : B.inRam (0x80fffd38#32) 1 = true := by
    exact Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4600) (width := 1) hm (by decide) (by decide)
  have hne : taken .ne (extend .b false (ramRead ram 0x80fffd42#32 .b)) 2 = true := by
    have h0 := ho.2 ⟨0,by decide⟩
    change ram (0x80fffd38#32+10#32+0#32) = Encoding.boolByte (s.relays 0) at h0
    have hh : ram 0x80fffd42#32 = Encoding.boolByte (s.relays 0) := h0
    rw [Memory.load_byte,hh]
    cases s.relays 0 <;> decide
  let c1 := c.wr 11 2 0x80001a3a#32
  let c2 := c1.wr 18 (extend .b false (ramRead ram 0x80fffd42#32 .b)) 0x80001a3e#32
  let c3 := c2.wr 10 (extend .b false (ramRead ram 0x80fffd38#32 .b)) 0x80001a42#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact rs2147490360) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp]
    simp only [alu,BitVec.zero_add]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80001a3a#32 : Word).getLsbD 0 = false;decide) rs2147490362 fun o => ?_
    have ha1 : c1.get 8+1326#32 = 0x80fffd42#32 := by simp [c1,Core.wr_get_ne,hfp]
    rw [exec_load,ha1,interp_load_ram (B := B) (img := img) (w := .b) o (by decide) ha]
    rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80001a3e#32 : Word).getLsbD 0 = false;decide) rs2147490366 fun o => ?_
    have ha2 : c2.get 8+1316#32 = 0x80fffd38#32 := by simp [c2,c1,Core.wr_get_ne,hfp]
    rw [exec_load,ha2,interp_load_ram (B := B) (img := img) (w := .b) o (by decide) hb]
    rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨next c ram,ram⟩ := by
    refine detStep_of (by change (0x80001a42#32 : Word).getLsbD 0 = false;decide) rs2147490370 fun o => ?_
    have h18 : c3.get 18 = extend .b false (ramRead ram 0x80fffd42#32 .b) := by simp [c3,c2,Core.wr_get]
    have h11 : c3.get 11 = 2 := by simp [c3,c2,c1,Core.wr_get]
    rw [exec_branch,h18,h11,hne]
    simp only [ite_true]
    change interp B img o (jump c3 0x80001a7e#32) ram 0 [] = _
    rw [jump_ok c3 _ (by decide)]
    rfl
  exact .step s0 (.step s1 (.step s2 (.single s3)))

theorem fields (c : Core) (ram : Word → BitVec 8) :
    (next c ram).pc = 0x80001a7e#32 ∧ (next c ram).get 2 = c.get 2 ∧
    (next c ram).get 8 = c.get 8 ∧ (next c ram).get 9 = c.get 9 ∧
    (next c ram).get 25 = c.get 25 ∧ (next c ram).sameCsr c :=
  ⟨rfl,rfl,rfl,rfl,rfl,by rfl⟩

theorem tag (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot)
    (ho : Outcome.At ram 0x80fffd38#32 (.ok ⟨none,s⟩)) : (next c ram).get 10 = 2#32 := by
  have ht : ram 0x80fffd38#32 = 2#8 := ho.1
  simp [next,Core.wr_get,Memory.load_byte,ht]

theorem first (c : Core) (ram : Word → BitVec 8) :
    byteOf ((next c ram).get 18) 0 = ram 0x80fffd42#32 := by
  simp [next,Core.wr_get,Marshal.byte_load]

end E5R.Thermostat.ReadDispatch
