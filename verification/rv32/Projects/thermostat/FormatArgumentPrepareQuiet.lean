-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.FormatArgumentPrepare
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.FormatArgumentPrepare
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (args desc ptr method : Word) (idx : Nat) (hi : idx < 8)
    (h9 : c.get 9 = args) (h12 : c.get 12 = desc) (h21 : c.get 21 = 192#32)
    (h23 : c.get 23 = 128#32) (h25 : c.get 25 = 192#32) (h24 : c.get 24 = BitVec.ofNat 32 idx)
    (hm : Memory.Block B (args+BitVec.ofNat 32 (8*idx)) 8)
    (ha : (args+BitVec.ofNat 32 (8*idx)).toNat%4 = 0)
    (hptr : ramRead ram (args+BitVec.ofNat 32 (8*idx)) .w = ptr)
    (hmethod : ramRead ram ((args+BitVec.ofNat 32 (8*idx))+4#32) .w = method)
    (hp : c.pc = 0x800049e8#32) :
    ∃ d, Quiet.Steps B img 9 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800049cc#32 ∧
      d.get 10 = ptr ∧ d.get 20 = desc+1#32 ∧ d.get 11 = args+BitVec.ofNat 32 (8*idx) ∧ d.get 12 = method ∧ (∀ r : Reg, r ≠ 10 → r ≠ 20 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (0xc0000000#32) 0x800049ec#32
  let c2 := c1.wr 20 (desc+1#32) 0x800049f0#32
  let c3 := c2.goto 0x80004a04#32
  let c4 := c3.goto 0x80004a08#32
  let c5 := c4.goto 0x800049c0#32
  let c6 := c5.wr 10 (BitVec.ofNat 32 (8*idx)) 0x800049c4#32
  let c7 := c6.wr 11 (args+BitVec.ofNat 32 (8*idx)) 0x800049c8#32
  let c8 := c7.wr 10 (ptr) 0x800049ca#32
  let c9 := c8.wr 12 (method) 0x800049cc#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact fe2147502568) fun o => ?_
    rw [exec_opimm,h21,hp];first | rfl | (rw [hp]; rfl)
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x800049ec#32).getLsbD 0 = false;decide) fe2147502572 fun o => ?_
    have hv : c1.get 12 = desc := by simp [c1,Core.wr_get_ne,Core.wr_get,h9,h12,h21,h23,h25,h24]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x800049f0#32).getLsbD 0 = false;decide) fe2147502576 fun o => ?_
    have hv : c2.get 10 = 0xc0000000#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h9,h12,h21,h23,h25,h24]
    rw [exec_branch,hv,Core.get_zero,show E5R.taken .lt (0xc0000000#32) (0 : Word) = true by decide]
    simp only [ite_true,ite_false]
    try simp only [hp]
    rw [jump_ok _ _ (by change (0x80004a04#32).getLsbD 0 = false;decide)];first | rfl | (rw [hp]; rfl)
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004a04#32).getLsbD 0 = false;decide) fe2147502596 fun o => ?_
    have hv0 : c3.get 21 = 192#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h12,h21,h23,h25,h24]
    have hv1 : c3.get 23 = 128#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h12,h21,h23,h25,h24]
    rw [exec_branch,hv0,hv1,show taken .eq 192#32 128#32 = false by decide]
    simp only [ite_false];first | rfl | (rw [hp]; rfl)
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004a08#32).getLsbD 0 = false;decide) fe2147502600 fun o => ?_
    have hv0 : c4.get 21 = 192#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h12,h21,h23,h25,h24]
    have hv1 : c4.get 25 = 192#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h12,h21,h23,h25,h24]
    rw [exec_branch,hv0,hv1,show taken .eq 192#32 192#32 = true by decide]
    simp only [ite_true]
    change interp B img o (jump c4 (0x80004a08#32+0xffffffb8#32)) ram 0 [] = _
    rw [show 0x80004a08#32+0xffffffb8#32 = 0x800049c0#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x800049c0#32).getLsbD 0 = false;decide) fe2147502528 fun o => ?_
    have hv : c5.get 24 = BitVec.ofNat 32 idx := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h12,h21,h23,h25,h24]
    rw [exec_opimm,hv]
    change interp B img o (.done (c5.wr 10 ((BitVec.ofNat 32 idx) <<< 3) 0x800049c4#32)) ram 0 [] = _
    rw [FormatBits.index8 idx hi];first | rfl | (rw [hp]; rfl)
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (0x800049c4#32).getLsbD 0 = false;decide) fe2147502532 fun o => ?_
    have hv0 : c6.get 9 = args := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h12,h21,h23,h25,h24]
    have hv1 : c6.get 10 = BitVec.ofNat 32 (8*idx) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h12,h21,h23,h25,h24]
    rw [exec_op,hv0,hv1];first | rfl | (rw [hp]; rfl)
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (0x800049c8#32).getLsbD 0 = false;decide) fe2147502536 fun o => ?_
    have hv : c7.get 11 = args+BitVec.ofNat 32 (8*idx) := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h12,h21,h23,h25,h24]
    rw [exec_load,hv,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .w) o ha
      (by simpa only [BitVec.add_zero] using Memory.block_access hm (off := 0) (by decide) (by decide)),hptr];first | rfl | (rw [hp]; rfl)
  have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine QuietDet.step_of (by change (0x800049ca#32).getLsbD 0 = false;decide) fe2147502538 fun o => ?_
    have hv : c8.get 11 = args+BitVec.ofNat 32 (8*idx) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h12,h21,h23,h25,h24]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (args+BitVec.ofNat 32 (8*idx)) 1 ha) (Memory.block_access hm (off := 4) (by decide) (by decide)),hmethod];first | rfl | (rw [hp]; rfl)
  refine ⟨c9,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.single s8)))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h12,h21,h23,h25,h24]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h12,h21,h23,h25,h24]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h12,h21,h23,h25,h24]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h12,h21,h23,h25,h24]
  · intro r h10 h20 h11 h12
    simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h9,h12,h21,h23,h25,h24,h10,h20,h11,h12]

end E5R.Thermostat.FormatArgumentPrepare
