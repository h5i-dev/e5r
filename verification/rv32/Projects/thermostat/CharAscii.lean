import Projects.thermostat.WriteCharCode
import Projects.thermostat.SmallCopyTurn
import Projects.thermostat.StoreBytes
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.CharAscii
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) (b : BitVec 8) : Word → BitVec 8 :=
  ramPut (ramWrite ram (sp+8#32) 0#32 .w) (sp+8#32) b

/-- Actual ASCII arm, including zeroed UTF-8 scratch word and real byte store. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (b : BitVec 8)
    (hp : c.pc = 0x8000230e#32) (hsp : c.get 2 = sp) (h11 : c.get 11 = BitVec.ofNat 32 b.toNat)
    (hm : Memory.Block B sp 32) (ha : sp.toNat%4 = 0) (hb : b.toNat < 128) :
    ∃ d, DetSteps B img 6 ⟨c,ram⟩ ⟨d,memory ram sp b⟩ ∧ d.pc = 0x80002388#32 ∧ d.get 8 = 1#32 ∧
      (∀ r : Reg, r ≠ 8 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 128#32 0x80002312#32
  let c2 := c1.goto 0x80002314#32
  let c3 := c2.goto 0x80002318#32
  let c4 := c3.goto 0x8000231c#32
  let c5 := c4.wr 8 1#32 0x8000231e#32
  let d := c5.goto 0x80002388#32
  let r0 := ramWrite ram (sp+8#32) 0#32 .w
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact ch2147492622) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,r0⟩ := by
    refine detStep_of (by change (0x80002312#32).getLsbD 0 = false;decide) ch2147492626 fun o => ?_
    have hs : c1.get 2 = sp := (Core.wr_get_ne _ _ _ _ _ (by decide)).trans hsp
    rw [exec_store,hs,Core.get_zero,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide))];rfl
  have s2 : DetStep B img ⟨c2,r0⟩ ⟨c3,r0⟩ := by
    refine detStep_of (by change (0x80002314#32).getLsbD 0 = false;decide) ch2147492628 fun o => ?_
    have hv11 : c2.get 11 = BitVec.ofNat 32 b.toNat := by simp [c2,c1,Core.wr_get_ne,h11]
    have hv12 : c2.get 12 = 128#32 := by simp [c2,c1,Core.wr_get]
    have ht : taken .geu (BitVec.ofNat 32 b.toNat) 128#32 = false := by
      simp only [taken,BitVec.ult,BitVec.toNat_ofNat]
      change (!decide (b.toNat%4294967296 < 128)) = false
      rw [Nat.mod_eq_of_lt (by omega),decide_eq_true hb];rfl
    rw [exec_branch,hv11,hv12,ht];rfl
  have s3 : DetStep B img ⟨c3,r0⟩ ⟨c4,memory ram sp b⟩ := by
    refine detStep_of (by change (0x80002318#32).getLsbD 0 = false;decide) ch2147492632 fun o => ?_
    have hs : c3.get 2 = sp := by simp [c3,c2,c1,Core.wr_get_ne,hsp]
    have hv : c3.get 11 = BitVec.ofNat 32 b.toNat := by simp [c3,c2,c1,Core.wr_get_ne,h11]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .b) o
      (by exact Nat.mod_one _) (Memory.block_access hm (off := 8) (by decide) (by decide))]
    change interp B img o (.done c4) (ramPut r0 (sp+8#32) (byteOf (BitVec.ofNat 32 b.toNat) 0)) 0 [] = _
    rw [SmallCopyTurn.byte_word];rfl
  have s4 : DetStep B img ⟨c4,memory ram sp b⟩ ⟨c5,memory ram sp b⟩ := by
    refine detStep_of (by change (0x8000231c#32).getLsbD 0 = false;decide) ch2147492636 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have s5 : DetStep B img ⟨c5,memory ram sp b⟩ ⟨d,memory ram sp b⟩ := by
    refine detStep_of (by change (0x8000231e#32).getLsbD 0 = false;decide) ch2147492638 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c5 0x80002388#32) (memory ram sp b) 0 [] = _
    rw [jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5))))),rfl,?_,?_,by rfl⟩
  · simp [d,c5,Core.wr_get]
  · intro r h8 h12;simp [d,c5,c4,c3,c2,c1,Core.wr_get_ne,h8,h12]

theorem byte (ram : Word → BitVec 8) (sp : Word) (b : BitVec 8) : memory ram sp b (sp+8#32) = b := ramPut_eq _ _ _

theorem frame (ram : Word → BitVec 8) (sp x : Word) (b : BitVec 8)
    (hx : ∀ i : Fin 4, x ≠ (sp+8#32)+BitVec.ofNat 32 i.val) : memory ram sp b x = ram x := by
  have h0 : x ≠ sp+8#32 := by simpa only [BitVec.add_zero] using hx ⟨0,by decide⟩
  rw [memory,ramPut_ne _ h0,StoreBytes.frame _ _ _ _ .w hx]
end E5R.Thermostat.CharAscii
