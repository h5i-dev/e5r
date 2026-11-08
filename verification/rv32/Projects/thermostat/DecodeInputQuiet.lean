-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.DecodeInput
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.DecodeSaveQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.DecodeInput
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp req p : Word) (body : List (BitVec 8))
    (hp : c.pc = 0x80001f6e#32) (hsp : c.get 2 = sp+16#32) (hreq : c.get 10 = req)
    (hm : Memory.Block B sp 16) (ha : sp.toNat%4 = 0) (h : BodyAt B ram req p body)
    (hsep : Separate req sp)
    (hbsep : ∀ i : Fin body.length, ∀ j : Fin 16, p+BitVec.ofNat 32 i.val ≠ sp+BitVec.ofNat 32 j.val) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,DecodeSave.memory ram sp c⟩ ∧ d.pc = 0x80001f7e#32 ∧
      d.get 2 = sp ∧ d.get 11 = p ∧ d.get 12 = BitVec.ofNat 32 body.length ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,hsteps,apc,asp,aregs,acsr⟩ := E5R.Thermostat.DecodeSave.contract_quiet B c ram sp hp hsp hm ha
  let r := DecodeSave.memory ram sp c
  have h' : BodyAt B r req p body := body_preserved h sp c hsep hbsep
  let b := a.wr 12 (BitVec.ofNat 32 body.length) 0x80001f7a#32
  let d := b.wr 11 p 0x80001f7e#32
  have a10 : a.get 10 = req := (aregs 10 (by decide)).trans hreq
  have s0 : Quiet.Step B img ⟨a,r⟩ ⟨b,r⟩ := by
    refine QuietDet.step_of (by rw [apc];decide) (by rw [apc];exact tr2147491702) fun o => ?_
    rw [exec_load,a10,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned req 81 h.aligned) (Memory.block_access h.object (off := 324) (by decide) (by decide)),h'.length,apc];rfl
  have s1 : Quiet.Step B img ⟨b,r⟩ ⟨d,r⟩ := by
    refine QuietDet.step_of (by change (0x80001f7a#32).getLsbD 0 = false;decide) tr2147491706 fun o => ?_
    have b10 : b.get 10 = req := by simp [b,Core.wr_get_ne,a10]
    rw [exec_load,b10,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned req 80 h.aligned) (Memory.block_access h.object (off := 320) (by decide) (by decide)),h'.pointer];rfl
  refine ⟨d,hsteps.trans (.step s0 (.single s1)),rfl,?_,?_,?_,?_,(Core.sameCsr_wr b 11 _ _).trans ((Core.sameCsr_wr a 12 _ _).trans acsr)⟩
  · simpa [d,b,Core.wr_get_ne] using asp
  · simp [d,Core.wr_get]
  · simp [d,b,Core.wr_get_ne,Core.wr_get]
  · intro r h1 h2 h3
    have hh : d.get r = a.get r := by simp [d,b,Core.wr_get_ne,h2,h3]
    exact hh.trans (aregs r h1)

end E5R.Thermostat.DecodeInput
