-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.I16SmallPair
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.I16SmallPair
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp ptr : Word) (bt bu : BitVec 8)
    (hp : c.pc = 0x80004f2a#32) (hs : c.get 2 = sp) (h11 : c.get 11 = ptr)
    (ht : ReadBytes.Byte B img ram ptr bt) (hu : ReadBytes.Byte B img ram (ptr+1#32) bu)
    (hm : Memory.Block B sp 16) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,memory ram sp bt bu⟩ ∧ d.pc = 0x80004f3a#32 ∧
      d.get 14 = BitVec.ofNat 32 bt.toNat ∧ d.get 11 = BitVec.ofNat 32 bu.toNat ∧
      (∀ r : Reg, r ≠ 14 → r ≠ 11 → d.get r = c.get r) ∧ d.sameCsr c := by
  let a := c.wr 14 (BitVec.ofNat 32 bt.toNat) 0x80004f2e#32
  let b := a.wr 11 (BitVec.ofNat 32 bu.toNat) 0x80004f32#32
  let r0 := ramPut ram (sp+6#32) bt
  let u := b.goto 0x80004f36#32
  let d := u.goto 0x80004f3a#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact di2147503914) fun o => ?_
    rw [exec_load,h11,BitVec.add_zero,ReadBytes.load ht,ReadBytes.extend_byte,←Memory.ofNat_width,hp];rfl
  have s1 : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f2e#32).getLsbD 0 = false;decide) di2147503918 fun o => ?_
    have hv : a.get 11 = ptr := by simp [a,Core.wr_get_ne,h11]
    rw [exec_load,hv,ReadBytes.load hu,ReadBytes.extend_byte,←Memory.ofNat_width];rfl
  have s2 : Quiet.Step B img ⟨b,ram⟩ ⟨u,r0⟩ := by
    refine QuietDet.step_of (by change (0x80004f32#32).getLsbD 0 = false;decide) di2147503922 fun o => ?_
    have hsp : b.get 2 = sp := by simp [b,a,Core.wr_get_ne,hs]
    have hv : b.get 14 = BitVec.ofNat 32 bt.toNat := by simp [b,a,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .b) o
      (Nat.mod_one _) (Memory.block_access hm (off := 6) (by decide) (by decide))]
    change interp B img o (.done u) (ramPut ram (sp+6#32) (byteOf (BitVec.ofNat 32 bt.toNat) 0)) 0 [] = _
    rw [SmallCopyTurn.byte_word];rfl
  have s3 : Quiet.Step B img ⟨u,r0⟩ ⟨d,memory ram sp bt bu⟩ := by
    refine QuietDet.step_of (by change (0x80004f36#32).getLsbD 0 = false;decide) di2147503926 fun o => ?_
    have hsp : u.get 2 = sp := by simp [u,b,a,Core.wr_get_ne,hs]
    have hv : u.get 11 = BitVec.ofNat 32 bu.toNat := by simp [u,b,Core.wr_get]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .b) o
      (Nat.mod_one _) (Memory.block_access hm (off := 7) (by decide) (by decide))]
    change interp B img o (.done d) (ramPut r0 (sp+7#32) (byteOf (BitVec.ofNat 32 bu.toNat) 0)) 0 [] = _
    rw [SmallCopyTurn.byte_word];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.single s3))),rfl,?_,?_,?_,by rfl⟩
  · simp [d,u,b,a,Core.wr_get_ne,Core.wr_get]
  · simp [d,u,b,Core.wr_get]
  · intro r h14 h11;simp [d,u,b,a,Core.wr_get_ne,h14,h11]

end E5R.Thermostat.I16SmallPair
