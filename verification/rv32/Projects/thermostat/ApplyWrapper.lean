import Projects.thermostat.Upper
import Projects.thermostat.CommitCode
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ApplyWrapper
open E5R E5R.Thermostat

def low (c : Core) : Word := c.get 2+0xfffffff0#32
def saved (c : Core) : Word := low c+12#32
def save (c : Core) (ram : Word → BitVec 8) := ramWrite ram (saved c) (c.get 1) .w
def inner (c : Core) : Core :=
  let c1 := c.wr 2 (low c) 0x80001e3a
  let c2 := c1.goto 0x80001e3c
  let c3 := c2.wr 1 0x7ffffe3c 0x80001e40
  c3.wr 1 0x80001e44 0x800002cc

theorem enter (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80001e38) (hr : B.inRam (saved c) 4 = true)
    (ha : (saved c).toNat % 4 = 0) :
    DetSteps B img 4 ⟨c,ram⟩ ⟨inner c,save c ram⟩ := by
  let c1 := c.wr 2 (low c) 0x80001e3a
  let c2 := c1.goto 0x80001e3c
  let c3 := c2.wr 1 0x7ffffe3c 0x80001e40
  have h0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact t2147491384) fun o => ?_
    rw [exec_opimm,hp];rfl
  have h1 : DetStep B img ⟨c1,ram⟩ ⟨c2,save c ram⟩ := by
    refine detStep_of (by change (0x80001e3a : Word).getLsbD 0 = false;decide) t2147491386 fun o => ?_
    have hs : c1.get 2 = low c := by simp [c1,Core.wr_get]
    have hv : c1.get 1 = c.get 1 := by simp [c1,Core.wr_get_ne]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) (a := low c+12#32) (v := c.get 1) o ha hr]
    rfl
  have h2 : DetStep B img ⟨c2,save c ram⟩ ⟨c3,save c ram⟩ := by
    refine detStep_of (by change (0x80001e3c : Word).getLsbD 0 = false;decide) t2147491388 fun o => ?_
    rw [exec_auipc]
    have hv : 0x80001e3c#32+0xffffe000#32 = 0x7ffffe3c#32 := by decide +kernel
    change interp B img o (.done (c2.wr 1 (0x80001e3c#32+0xffffe000#32) (0x80001e3c#32+4#32))) (save c ram) 0 [] = _
    rw [hv]
    rfl
  have h3 : DetStep B img ⟨c3,save c ram⟩ ⟨inner c,save c ram⟩ := by
    refine detStep_of (by change (0x80001e40 : Word).getLsbD 0 = false;decide) t2147491392 fun o => ?_
    have hv : c3.get 1 = 0x7ffffe3c := by simp [c3,Core.wr_get]
    rw [exec_jalr,hv]
    rfl
  exact .step h0 (.step h1 (.step h2 (.single h3)))

theorem inner_reg (c : Core) (r : Reg) (h1 : r ≠ 1) (h2 : r ≠ 2) :
    (inner c).get r = c.get r := by simp [inner,Core.wr_get_ne,h1,h2]
theorem inner_sp (c : Core) : (inner c).get 2 = low c := by simp [inner,Core.wr_get,Core.wr_get_ne]
theorem inner_ra (c : Core) : (inner c).get 1 = 0x80001e44 := by simp [inner,Core.wr_get]

theorem suffix (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80001e44) (hr : B.inRam (c.get 2+12#32) 4 = true)
    (ha : (c.get 2+12#32).toNat % 4 = 0)
    (hv : ramRead ram (c.get 2+12#32) .w = 0x800006ea) :
    ∃ d, DetSteps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800006ea ∧
      d.get 2 = c.get 2+16#32 ∧ (∀ r : Reg, r ≠ 1 → r ≠ 2 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 1 0x800006ea 0x80001e46
  let c2 := c1.wr 2 (c.get 2+16#32) 0x80001e48
  let d := c2.goto 0x800006ea
  have h0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact t2147491396) fun o => ?_
    rw [exec_load,interp_load_ram (B := B) (img := img) (w := .w) (a := c.get 2+12#32) o ha hr,hv,hp];rfl
  have h1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80001e46 : Word).getLsbD 0 = false;decide) t2147491398 fun o => ?_
    have hs : c1.get 2 = c.get 2 := by simp [c1,Core.wr_get_ne]
    rw [exec_opimm,hs];rfl
  have h2 : DetStep B img ⟨c2,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x80001e48 : Word).getLsbD 0 = false;decide) t2147491400 fun o => ?_
    have hr1 : c2.get 1 = 0x800006ea := by simp [c2,c1,Core.wr_get,Core.wr_get_ne]
    rw [exec_jalr,hr1];rfl
  refine ⟨d,.step h0 (.step h1 (.single h2)),rfl,?_,?_,by rfl⟩
  · simp [d,c2,Core.wr_get]
  · intro r h1' h2'
    simp [d,c2,c1,Core.wr_get_ne,h1',h2']
theorem inner_upper (c : Core) : Upper.Frame c (inner c) := by
  intro r hr
  exact inner_reg c r (Upper.ne_low r hr 1 (by decide)) (Upper.ne_low r hr 2 (by decide))
end E5R.Thermostat.ApplyWrapper
