import Projects.thermostat.WriteEntryCode
import Projects.thermostat.Encoding
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.WriteEntry
open E5R E5R.Thermostat

theorem actor_byte (admin : Bool) : byteOf (BitVec.ofNat 32 (Encoding.boolByte admin).toNat) 0 = Encoding.boolByte admin := by
  cases admin <;> decide +kernel

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (eng sp req : Word) (admin : Bool)
    (hp : c.pc = 0x800005e2#32) (h23 : c.get 23 = eng) (hsp : c.get 2 = sp) (h21 : c.get 21 = req)
    (he : Memory.Block B eng 25) (hs : Memory.Block B sp 10)
    (hadmin : ram (eng+24#32) = Encoding.boolByte admin) :
    ∃ d, DetSteps B img 5 ⟨c,ram⟩ ⟨d,ramPut ram (sp+9#32) (Encoding.boolByte admin)⟩ ∧
      d.pc = 0x80001f6e#32 ∧ d.get 10 = req ∧ d.get 1 = 0x800005f4#32 ∧
      (∀ r : Reg, r ≠ 1 → r ≠ 10 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (BitVec.ofNat 32 (Encoding.boolByte admin).toNat) 0x800005e6#32
  let c2 := c1.goto 0x800005ea#32
  let c3 := c2.wr 10 req 0x800005ec#32
  let c4 := c3.wr 1 0x800025ec#32 0x800005f0#32
  let d := c4.wr 1 0x800005f4#32 0x80001f6e#32
  let r := ramPut ram (sp+9#32) (Encoding.boolByte admin)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact we2147485154) fun o => ?_
    rw [exec_load,h23,interp_load_ram (B := B) (img := img) (w := .b) o (by change (eng+24#32).toNat%1 = 0;omega)
      (Memory.block_access he (off := 24) (by decide) (by decide)),Memory.load_byte]
    change interp B img o (.done (c.wr 10 (BitVec.ofNat 32 (ram (eng+24#32)).toNat) (c.pc+4#32))) ram 0 [] = _
    rw [hadmin,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,r⟩ := by
    refine detStep_of (by change (0x800005e6#32).getLsbD 0 = false;decide) we2147485158 fun o => ?_
    have v2 : c1.get 2 = sp := by simp [c1,Core.wr_get_ne,hsp]
    have v10 : c1.get 10 = BitVec.ofNat 32 (Encoding.boolByte admin).toNat := by simp [c1,Core.wr_get]
    rw [exec_store,v2,v10,interp_store_ram (B := B) (img := img) (w := .b) o (by change (sp+9#32).toNat%1 = 0;omega)
      (Memory.block_access hs (off := 9) (by decide) (by decide))]
    change Result.ok (c1.goto 0x800005ea#32) (ramPut ram (sp+9#32) (byteOf (BitVec.ofNat 32 (Encoding.boolByte admin).toNat) 0)) [] = _
    rw [actor_byte]
  have s2 : DetStep B img ⟨c2,r⟩ ⟨c3,r⟩ := by
    refine detStep_of (by change (0x800005ea#32).getLsbD 0 = false;decide) we2147485162 fun o => ?_
    have v21 : c2.get 21 = req := by simp [c2,c1,Core.wr_get_ne,h21]
    rw [exec_op,Core.get_zero,v21]
    simp only [alu];rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s3 : DetStep B img ⟨c3,r⟩ ⟨c4,r⟩ := by
    refine detStep_of (by change (0x800005ec#32).getLsbD 0 = false;decide) we2147485164 fun o => ?_
    rw [exec_auipc];rfl
  have s4 : DetStep B img ⟨c4,r⟩ ⟨d,r⟩ := by
    refine detStep_of (by change (0x800005f0#32).getLsbD 0 = false;decide) we2147485168 fun o => ?_
    have v1 : c4.get 1 = 0x800025ec#32 := by simp [c4,Core.wr_get]
    rw [exec_jalr,v1,show (0x800025ec#32+0xfffff982#32) &&& ~~~(1 : Word) = 0x80001f6e#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.single s4)))),rfl,?_,?_,?_,by rfl⟩
  · simp [d,c4,c3,Core.wr_get_ne,Core.wr_get]
  · simp [d,Core.wr_get]
  · intro reg h1 h10;simp [d,c4,c3,c2,c1,Core.wr_get_ne,h1,h10]
end E5R.Thermostat.WriteEntry
