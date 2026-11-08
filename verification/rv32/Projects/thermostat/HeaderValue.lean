import Projects.thermostat.HeaderInput
import Projects.thermostat.HeaderCode
import Projects.thermostat.ParamMath
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HeaderValue
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (table p : Word)
    (raw : List (BitVec 8)) (e : HeaderSpec.Entry) (hc : HeaderInput.Cell B ram table raw.length e)
    (hraw : Bytes.Span B ram p raw) (hp : c.pc = 0x80002738#32)
    (h16 : c.get 16 = table) (h15 : c.get 15 = p) (h12 : c.get 12 = BitVec.ofNat 32 raw.length) :
    ∃ d, DetSteps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = c.get 1 &&& ~~~1 ∧
      d.get 10 = p+BitVec.ofNat 32 e.valueStart ∧
      d.get 11 = BitVec.ofNat 32 (HeaderSpec.value raw e).length ∧
      Bytes.Span B ram (d.get 10) (HeaderSpec.value raw e) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → d.get r = c.get r) ∧ d.sameCsr c := by
  have hb := hc.bounds
  change e.nameStart ≤ e.nameEnd ∧ e.nameEnd ≤ raw.length ∧ e.valueStart ≤ e.valueEnd ∧ e.valueEnd ≤ raw.length at hb
  obtain ⟨_,_,hse,heraw⟩ := hb
  have hlen := hraw.length
  have hs : e.valueStart < 2^32 := by omega
  have he : e.valueEnd < 2^32 := by omega
  let c1 := c.wr 10 (BitVec.ofNat 32 e.valueStart) 0x8000273c#32
  let c2 := c1.wr 11 (BitVec.ofNat 32 e.valueEnd) 0x80002740#32
  let c3 := c2.goto 0x80002744#32
  let c4 := c3.goto 0x80002748#32
  let c5 := c4.wr 11 (BitVec.ofNat 32 (e.valueEnd-e.valueStart)) 0x8000274a#32
  let c6 := c5.wr 10 (p+BitVec.ofNat 32 e.valueStart) 0x8000274c#32
  let d := c6.goto (c.get 1 &&& ~~~1)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact hd2147493688) fun o => ?_
    rw [exec_load,h16,interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned table 2 hc.aligned)
      (Memory.block_access hc.block (off := 8) (by decide) (by decide)),hc.valueStart,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x8000273c#32).getLsbD 0 = false;decide) hd2147493692 fun o => ?_
    have hv : c1.get 16 = table := by simp [c1,Core.wr_get_ne,h16]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned table 3 hc.aligned)
      (Memory.block_access hc.block (off := 12) (by decide) (by decide)),hc.valueEnd];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80002740#32).getLsbD 0 = false;decide) hd2147493696 fun o => ?_
    have v10 : c2.get 10 = BitVec.ofNat 32 e.valueStart := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    have v11 : c2.get 11 = BitVec.ofNat 32 e.valueEnd := by simp [c2,Core.wr_get]
    rw [exec_branch,v11,v10,ParamMath.ult _ _ he hs,decide_eq_false (by omega)];rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80002744#32).getLsbD 0 = false;decide) hd2147493700 fun o => ?_
    have v12 : c3.get 12 = BitVec.ofNat 32 raw.length := by simp [c3,c2,c1,Core.wr_get_ne,h12]
    have v11 : c3.get 11 = BitVec.ofNat 32 e.valueEnd := by simp [c3,c2,Core.wr_get]
    rw [exec_branch,v12,v11,ParamMath.ult _ _ hlen he,decide_eq_false (by omega)];rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80002748#32).getLsbD 0 = false;decide) hd2147493704 fun o => ?_
    have v10 : c4.get 10 = BitVec.ofNat 32 e.valueStart := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have v11 : c4.get 11 = BitVec.ofNat 32 e.valueEnd := by simp [c4,c3,c2,Core.wr_get]
    rw [exec_op,v11,v10]
    change interp B img o (.done (c4.wr 11 (BitVec.ofNat 32 e.valueEnd-BitVec.ofNat 32 e.valueStart) 0x8000274a#32)) ram 0 [] = _
    rw [ParamMath.difference _ _ hse];rfl
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x8000274a#32).getLsbD 0 = false;decide) hd2147493706 fun o => ?_
    have v10 : c5.get 10 = BitVec.ofNat 32 e.valueStart := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have v15 : c5.get 15 = p := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,h15]
    rw [exec_op,v10,v15];simp only [alu];rw [BitVec.add_comm (BitVec.ofNat 32 e.valueStart) p];rfl
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x8000274c#32).getLsbD 0 = false;decide) hd2147493708 fun o => ?_
    have v1 : c6.get 1 = c.get 1 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_jalr,v1,BitVec.add_zero,jump_ok _ _ (clear_bit0 _)];rfl
  have ptr : d.get 10 = p+BitVec.ofNat 32 e.valueStart := by simp [d,c6,Core.wr_get]
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.single s6)))))),rfl,ptr,?_,?_,?_,by rfl⟩
  · rw [HeaderInput.value_length hc.bounds]
    simp [d,c6,c5,Core.wr_get_ne,Core.wr_get]
  · rw [ptr];exact HeaderInput.value_span hraw hc.bounds
  · intro r h1 h2;simp [d,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h1,h2]
end E5R.Thermostat.HeaderValue
