import Projects.thermostat.CopyInitData
namespace E5R.Thermostat.CopyTwoStore
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc=0x80005240#32) (h2 : c.get 2=sp) (h16 : c.get 16=sp+14#32)
    (h17 : c.get 17=0x227b#32) (hm : Memory.Block B sp 16) (ha : sp.toNat%4=0) :
    ∃ d, DetSteps B img 2 ⟨c,CopyUnalignedScratch.memory ram sp⟩ ⟨d,CopyInitData.halfRam ram sp⟩ ∧
      d.pc=0x80005246#32 ∧ d.get 17=0x227b0000#32 ∧
      (∀ r : Reg, r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.goto 0x80005244#32
  let d := a.wr 17 0x227b0000#32 0x80005246#32
  have s0 : DetStep B img ⟨c,CopyUnalignedScratch.memory ram sp⟩ ⟨a,CopyInitData.halfRam ram sp⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact cp2147504704) fun o => ?_
    rw [exec_store,h16,h17,BitVec.add_zero,interp_store_ram (B := B) (img := img) (w := .h) o
      (Memory.half_aligned sp 7 (by omega)) (Memory.block_access hm (off := 14) (by decide) (by decide)),hp]
    rfl
  have s1 : DetStep B img ⟨a,CopyInitData.halfRam ram sp⟩ ⟨d,CopyInitData.halfRam ram sp⟩ := by
    refine detStep_of (by change (0x80005244#32).getLsbD 0=false;decide) cp2147504708 fun o => ?_
    have a2 : a.get 2=sp := h2
    rw [exec_load,a2,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide)),CopyInitData.half_word]
    rfl
  refine ⟨d,.step s0 (.single s1),rfl,?_,?_,by rfl⟩
  · simp [d,Core.wr_get]
  · intro r hr;simp [d,a,Core.wr_get_ne,hr]
end E5R.Thermostat.CopyTwoStore
