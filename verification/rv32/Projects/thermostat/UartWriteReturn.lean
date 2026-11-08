import Projects.thermostat.UartWriteCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
namespace E5R.Thermostat.UartWriteReturn
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (obj : Word) := ramWrite ram (obj+40#32) 1#32 .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (obj : Word)
    (hp : c.pc=0x8000081e#32) (h10 : c.get 10=obj) (hm : Memory.Block B obj 41) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,memory ram obj⟩ ∧ d.pc=c.get 1 &&& ~~~1 ∧
      d.get 11=1#32 ∧ (∀ r : Reg, r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 11 1#32 0x80000820#32
  let b := a.goto 0x80000824#32
  let d := b.goto (c.get 1 &&& ~~~1)
  have ta : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact uw2147485726) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have tb : Quiet.Step B img ⟨a,ram⟩ ⟨b,memory ram obj⟩ := by
    refine Quiet.step_of (by change (0x80000820#32).getLsbD 0=false;decide) uw2147485728 fun o => ?_
    have a10 : a.get 10=obj := by simp [a,Core.wr_get_ne,h10]
    have a11 : a.get 11=1#32 := by simp [a,Core.wr_get]
    rw [exec_store,a10,a11,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _)
      (Memory.block_access hm (off := 40) (by decide) (by decide))];rfl
  have td : Quiet.Step B img ⟨b,memory ram obj⟩ ⟨d,memory ram obj⟩ := by
    refine Quiet.step_of (by change (0x80000824#32).getLsbD 0=false;decide) uw2147485732 fun o => ?_
    have b1 : b.get 1=c.get 1 := by simp [b,a,Core.wr_get_ne]
    rw [exec_jalr,b1,BitVec.add_zero]
    change Observed.interp B img o (jump b (c.get 1 &&& ~~~1)) (memory ram obj) 0 [] [] = _
    rw [jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨d,.step ta (.step tb (.single td)),rfl,?_,?_,by rfl⟩
  · simp [d,b,a,Core.wr_get]
  · intro reg hr;simp [d,b,a,Core.wr_get_ne,hr]

theorem complete (ram : Word → BitVec 8) (obj : Word) : memory ram obj (obj+40#32)=1#8 := by
  simp [memory,ramWrite,ramPut,byteOf]
end E5R.Thermostat.UartWriteReturn
