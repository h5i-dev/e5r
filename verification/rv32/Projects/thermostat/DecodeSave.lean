import Projects.thermostat.TrimCode
import Projects.thermostat.Bytes
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.DecodeSave
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) (c : Core) : Word → BitVec 8 :=
  ramWrite (ramWrite (ramWrite ram (sp+12#32) (c.get 1) .w) (sp+8#32) (c.get 8) .w) (sp+4#32) (c.get 9) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc = 0x80001f6e#32) (hsp : c.get 2 = sp+16#32)
    (hm : Memory.Block B sp 16) (ha : sp.toNat%4 = 0) :
    ∃ d, DetSteps B img 4 ⟨c,ram⟩ ⟨d,memory ram sp c⟩ ∧ d.pc = 0x80001f76#32 ∧
      d.get 2 = sp ∧ (∀ r : Reg, r ≠ 2 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 2 sp 0x80001f70#32
  let c2 := c1.goto 0x80001f72#32
  let c3 := c2.goto 0x80001f74#32
  let d := c3.goto 0x80001f76#32
  let r1 := ramWrite ram (sp+12#32) (c.get 1) .w
  let r2 := ramWrite r1 (sp+8#32) (c.get 8) .w
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact tr2147491694) fun o => ?_
    rw [exec_opimm,hsp]
    simp only [alu]
    rw [BitVec.add_assoc,show 16#32+0xfffffff0#32 = 0#32 by decide +kernel,BitVec.add_zero,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine detStep_of (by change (0x80001f70#32).getLsbD 0 = false;decide) tr2147491696 fun o => ?_
    have h2 : c1.get 2 = sp := by simp [c1,Core.wr_get]
    have h1 : c1.get 1 = c.get 1 := by simp [c1,Core.wr_get_ne]
    rw [exec_store,h2,h1,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide))];rfl
  have s2 : DetStep B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine detStep_of (by change (0x80001f72#32).getLsbD 0 = false;decide) tr2147491698 fun o => ?_
    have h2 : c2.get 2 = sp := by simp [c2,c1,Core.wr_get]
    have h8 : c2.get 8 = c.get 8 := by simp [c2,c1,Core.wr_get_ne]
    rw [exec_store,h2,h8,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide))];rfl
  have s3 : DetStep B img ⟨c3,r2⟩ ⟨d,memory ram sp c⟩ := by
    refine detStep_of (by change (0x80001f74#32).getLsbD 0 = false;decide) tr2147491700 fun o => ?_
    have h2 : c3.get 2 = sp := by simp [c3,c2,c1,Core.wr_get]
    have h9 : c3.get 9 = c.get 9 := by simp [c3,c2,c1,Core.wr_get_ne]
    rw [exec_store,h2,h9,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 1 ha) (Memory.block_access hm (off := 4) (by decide) (by decide))];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.single s3))),rfl,?_,?_,by rfl⟩
  · simp [d,c3,c2,c1,Core.wr_get]
  · intro r hr;simp [d,c3,c2,c1,Core.wr_get_ne,hr]

theorem frame (ram : Word → BitVec 8) (sp : Word) (c : Core) (x : Word)
    (hx : ∀ i : Fin 16, x ≠ sp+BitVec.ofNat 32 i.val) : memory ram sp c x = ram x := by
  unfold memory
  rw [ramWrite_w_other _ _ _ _ (by
    intro k hk;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨4+k,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by
    intro k hk;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨8+k,by omega⟩)]
  exact ramWrite_w_other _ _ _ _ (by
    intro k hk;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨12+k,by omega⟩)

theorem saved (ram : Word → BitVec 8) (sp : Word) (c : Core) :
    ramRead (memory ram sp c) (sp+12#32) .w = c.get 1 ∧
    ramRead (memory ram sp c) (sp+8#32) .w = c.get 8 ∧
    ramRead (memory ram sp c) (sp+4#32) .w = c.get 9 := by
  have hd (a b : Nat) (ha : a < 16) (hb : b < 16) (ha4 : a%4 = 0) (hb4 : b%4 = 0) (hne : a ≠ b) :
      ∀ i j : Fin 4, sp+BitVec.ofNat 32 a+BitVec.ofNat 32 i.val ≠ sp+BitVec.ofNat 32 b+BitVec.ofNat 32 j.val :=
    Memory.word_disjoint sp a b (by omega) (by omega) ha4 hb4 hne
  refine ⟨?_,?_,?_⟩
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (hd 12 4 (by decide) (by decide) (by decide) (by decide) (by decide)),
      Memory.read_word_write_other _ _ _ _ (hd 12 8 (by decide) (by decide) (by decide) (by decide) (by decide)),ramRead_ramWrite_w]
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (hd 8 4 (by decide) (by decide) (by decide) (by decide) (by decide)),ramRead_ramWrite_w]
  · exact ramRead_ramWrite_w _ _ _

theorem preserves_span {B ram p xs} (hs : Bytes.Span B ram p xs) (sp : Word) (c : Core)
    (hsep : ∀ i : Fin xs.length, ∀ j : Fin 16, p+BitVec.ofNat 32 i.val ≠ sp+BitVec.ofNat 32 j.val) :
    Bytes.Span B (memory ram sp c) p xs := by
  exact ⟨hs.length,hs.nowrap,hs.memory,fun i => (frame ram sp c _ (hsep i)).trans (hs.bytes i)⟩
end E5R.Thermostat.DecodeSave
