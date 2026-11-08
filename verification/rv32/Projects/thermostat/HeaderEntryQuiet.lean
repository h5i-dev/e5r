-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.HeaderEntry
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.HeaderEntry
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (table raw query : Word)
    (rawLength : Nat) (e : HeaderSpec.Entry) (hc : HeaderInput.Cell B ram table rawLength e)
    (hl : rawLength < 2^32) (hp : c.pc = 0x800026e8#32)
    (h16 : c.get 16 = table) (h15 : c.get 15 = raw) (h11 : c.get 11 = query)
    (h12 : c.get 12 = BitVec.ofNat 32 rawLength) (h13 : c.get 13 = 13#32) :
    ∃ d n, n ≤ 10 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if e.nameEnd-e.nameStart = 13 then 0x80002706#32 else 0x800026e2#32) ∧
      (e.nameEnd-e.nameStart = 13 → d.get 10 = raw+BitVec.ofNat 32 e.nameStart ∧ d.get 14 = query ∧ d.get 5 = 13#32) ∧
      (∀ r : Reg, r ≠ 5 → r ≠ 10 → r ≠ 14 → d.get r = c.get r) ∧ d.sameCsr c := by
  have hbounds := hc.bounds
  change e.nameStart ≤ e.nameEnd ∧ e.nameEnd ≤ rawLength ∧ e.valueStart ≤ e.valueEnd ∧ e.valueEnd ≤ rawLength at hbounds
  obtain ⟨hse,heraw,hvs,hveraw⟩ := hbounds
  have hs : e.nameStart < 2^32 := by omega
  have he : e.nameEnd < 2^32 := by omega
  let c1 := c.wr 10 (BitVec.ofNat 32 e.nameStart) 0x800026ec#32
  let c2 := c1.wr 14 (BitVec.ofNat 32 e.nameEnd) 0x800026f0#32
  let c3 := c2.goto 0x800026f4#32
  let c4 := c3.goto 0x800026f8#32
  let c5 := c4.wr 14 (BitVec.ofNat 32 (e.nameEnd-e.nameStart)) 0x800026fa#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact hd2147493608) fun o => ?_
    rw [exec_load,h16,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .w) o hc.aligned
      (by simpa using Memory.block_access hc.block (off := 0) (by decide) (by decide)),hc.nameStart,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x800026ec#32).getLsbD 0 = false;decide) hd2147493612 fun o => ?_
    have hv : c1.get 16 = table := by simp [c1,Core.wr_get_ne,h16]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned table 1 hc.aligned)
      (Memory.block_access hc.block (off := 4) (by decide) (by decide)),hc.nameEnd];rfl
  have v10 : c2.get 10 = BitVec.ofNat 32 e.nameStart := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
  have v14 : c2.get 14 = BitVec.ofNat 32 e.nameEnd := by simp [c2,Core.wr_get]
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x800026f0#32).getLsbD 0 = false;decide) hd2147493616 fun o => ?_
    rw [exec_branch,v14,v10,ParamMath.ult e.nameEnd e.nameStart he hs,decide_eq_false (by omega)];rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x800026f4#32).getLsbD 0 = false;decide) hd2147493620 fun o => ?_
    have v12 : c3.get 12 = BitVec.ofNat 32 rawLength := by simp [c3,c2,c1,Core.wr_get_ne,h12]
    have vv14 : c3.get 14 = BitVec.ofNat 32 e.nameEnd := v14
    rw [exec_branch,v12,vv14,ParamMath.ult rawLength e.nameEnd hl he,decide_eq_false (by omega)];rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x800026f8#32).getLsbD 0 = false;decide) hd2147493624 fun o => ?_
    have vv14 : c4.get 14 = BitVec.ofNat 32 e.nameEnd := v14
    have vv10 : c4.get 10 = BitVec.ofNat 32 e.nameStart := v10
    rw [exec_op,vv14,vv10]
    change interp B img o (.done (c4.wr 14 (BitVec.ofNat 32 e.nameEnd-BitVec.ofNat 32 e.nameStart) 0x800026fa#32)) ram 0 [] = _
    rw [ParamMath.difference _ _ hc.bounds.1];rfl
  have pre : Quiet.Steps B img 5 ⟨c,ram⟩ ⟨c5,ram⟩ := .step s0 (.step s1 (.step s2 (.step s3 (.single s4))))
  have v14' : c5.get 14 = BitVec.ofNat 32 (e.nameEnd-e.nameStart) := by simp [c5,Core.wr_get]
  have v13 : c5.get 13 = 13#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,h13]
  by_cases hn : e.nameEnd-e.nameStart = 13
  · let c6 := c5.goto 0x800026fe#32
    let c7 := c6.goto 0x80002700#32
    let c8 := c7.wr 10 (raw+BitVec.ofNat 32 e.nameStart) 0x80002702#32
    let c9 := c8.wr 14 query 0x80002704#32
    let d := c9.wr 5 13#32 0x80002706#32
    have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
      refine QuietDet.step_of (by change (0x800026fa#32).getLsbD 0 = false;decide) hd2147493626 fun o => ?_
      rw [exec_branch,v14',v13,hn];rfl
    have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
      refine QuietDet.step_of (by change (0x800026fe#32).getLsbD 0 = false;decide) hd2147493630 fun o => ?_
      have vv13 : c6.get 13 = 13#32 := v13
      rw [exec_branch,vv13,Core.get_zero];rfl
    have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
      refine QuietDet.step_of (by change (0x80002700#32).getLsbD 0 = false;decide) hd2147493632 fun o => ?_
      have vv15 : c7.get 15 = raw := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h15]
      have vv10 : c7.get 10 = BitVec.ofNat 32 e.nameStart := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
      rw [exec_op,vv10,vv15]
      simp only [alu];rw [BitVec.add_comm (BitVec.ofNat 32 e.nameStart) raw];rfl
    have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
      refine QuietDet.step_of (by change (0x80002702#32).getLsbD 0 = false;decide) hd2147493634 fun o => ?_
      have vv11 : c8.get 11 = query := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h11]
      rw [exec_op,Core.get_zero,vv11]
      simp only [alu];rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
    have s9 : Quiet.Step B img ⟨c9,ram⟩ ⟨d,ram⟩ := by
      refine QuietDet.step_of (by change (0x80002704#32).getLsbD 0 = false;decide) hd2147493636 fun o => ?_
      have vv13 : c9.get 13 = 13#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h13]
      rw [exec_op,Core.get_zero,vv13];rfl
    refine ⟨d,10,by omega,pre.trans (.step s5 (.step s6 (.step s7 (.step s8 (.single s9))))),by simp [d,hn],?_,?_,by rfl⟩
    · intro _;simp [d,c9,c8,Core.wr_get_ne,Core.wr_get]
    · intro r h1 h2 h3;simp [d,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h1,h2,h3]
  · let d := c5.goto 0x800026e2#32
    have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨d,ram⟩ := by
      refine QuietDet.step_of (by change (0x800026fa#32).getLsbD 0 = false;decide) hd2147493626 fun o => ?_
      rw [exec_branch,v14',v13]
      change interp B img o (if taken .ne (BitVec.ofNat 32 (e.nameEnd-e.nameStart)) (BitVec.ofNat 32 13) then _ else _) ram 0 [] = _
      rw [Usize.ne _ 13 (by omega) (by decide),decide_eq_true hn];simp only [ite_true]
      change interp B img o (jump c5 (0x800026fa#32+0xffffffe8#32)) ram 0 [] = _
      rw [show 0x800026fa#32+0xffffffe8#32 = 0x800026e2#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    refine ⟨d,6,by omega,pre.trans (.single s5),by simp [d,hn],?_,?_,by rfl⟩
    · intro hh;contradiction
    · intro r h1 h2 h3;simp [d,c5,c4,c3,c2,c1,Core.wr_get_ne,h2,h3]

end E5R.Thermostat.HeaderEntry
