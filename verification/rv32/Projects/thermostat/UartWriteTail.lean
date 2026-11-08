import Projects.thermostat.UartWriteCode
import Projects.thermostat.QuietRam
import Projects.thermostat.StoreWords
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.UartWriteTail
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (obj src len : Word) :=
  ramWrite (ram) (obj+36#32) (1#32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (obj src len : Word) (h10 : c.get 10=obj) (h11 : c.get 11=len)
    (hm : Memory.Block B obj 41) (ha : obj.toNat%4=0)
    (h20 : ramRead ram (obj+20#32) .w=len) (h16 : ramRead ram (obj+16#32) .w=src)
    (hp : c.pc=0x8000080a#32) :
    ∃ d, Quiet.Steps B img 8 ⟨c,ram⟩ ⟨d,memory ram obj src len⟩ ∧ d.pc=0x800007c8#32 ∧
      d.get 12=0#32 ∧ d.get 14=src ∧ d.get 11=src+len ∧ (∀ r : Reg, r≠12 → r≠14 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (len) 0x8000080c#32
  let c2 := c1.wr 14 (1#32) 0x8000080e#32
  let r1 := ramWrite ram (obj+36#32) (1#32) .b
  let c3 := c2.goto 0x80000812#32
  let c4 := c3.goto 0x80000816#32
  let c5 := c4.wr 14 (src) 0x80000818#32
  let c6 := c5.wr 12 (0#32) 0x8000081a#32
  let c7 := c6.wr 11 (src+len) 0x8000081c#32
  let c8 := c7.goto 0x800007c8#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact uw2147485706) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have vo : c.get 10=obj := by simp [Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_load,vo,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 5 ha) (Memory.block_access hm (off := 20) (by decide) (by decide))]
    have hv : ramRead ram (obj+20#32) .w=len := h20
    rw [hv];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000080c#32).getLsbD 0=false;decide) uw2147485708 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,r1⟩ := by
    refine Quiet.step_of (by change (0x8000080e#32).getLsbD 0=false;decide) uw2147485710 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 r1 [],[]⟩
    have vo : c2.get 10=obj := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    have vv : c2.get 14=1#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_store,vo,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 36) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r1⟩ ⟨c4,r1⟩ := by
    refine Quiet.step_of (by change (0x80000812#32).getLsbD 0=false;decide) uw2147485714 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r1 0 [] [] = ⟨.ok c4 r1 [],[]⟩
    have v12 : c3.get 12=len := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    have v11 : c3.get 11=len := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_branch,v12,v11,show taken .ltu len len=false by simp [taken,BitVec.ult]]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r1⟩ ⟨c5,r1⟩ := by
    refine Quiet.step_of (by change (0x80000816#32).getLsbD 0=false;decide) uw2147485718 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r1 0 [] [] = ⟨.ok c5 r1 [],[]⟩
    have vo : c4.get 10=obj := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_load,vo,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 4 ha) (Memory.block_access hm (off := 16) (by decide) (by decide))]
    have hv : ramRead r1 (obj+16#32) .w=src := by rw [StoreWords.read_other ram (obj+16#32) (obj+36#32) 1#32 .b (StoreWords.offsets obj 16 4 36 1 (by decide) (by decide) (Or.inl (by decide)))];exact h16
    rw [hv];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r1⟩ ⟨c6,r1⟩ := by
    refine Quiet.step_of (by change (0x80000818#32).getLsbD 0=false;decide) uw2147485720 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r1 0 [] [] = ⟨.ok c6 r1 [],[]⟩
    have v12 : c5.get 12=len := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    have v11 : c5.get 11=len := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_op,v12,v11];simp only [alu,BitVec.sub_self];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r1⟩ ⟨c7,r1⟩ := by
    refine Quiet.step_of (by change (0x8000081a#32).getLsbD 0=false;decide) uw2147485722 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r1 0 [] [] = ⟨.ok c7 r1 [],[]⟩
    have v11 : c6.get 11=len := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    have v14 : c6.get 14=src := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_op,v11,v14]
    change Observed.interp B img o (.done (c6.wr 11 (len+src) 0x8000081c#32)) r1 0 [] [] = _
    rw [BitVec.add_comm len src];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r1⟩ ⟨c8,r1⟩ := by
    refine Quiet.step_of (by change (0x8000081c#32).getLsbD 0=false;decide) uw2147485724 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r1 0 [] [] = ⟨.ok c8 r1 [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c7 (0x8000081c#32+0xffffffac#32)) r1 0 [] [] = _
    rw [show 0x8000081c#32+0xffffffac#32=0x800007c8#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c8,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.single t7))))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · intro reg h12 h14 h11;simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h14,h11]
end E5R.Thermostat.UartWriteTail
