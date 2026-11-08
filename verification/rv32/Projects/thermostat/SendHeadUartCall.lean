import Projects.thermostat.SendCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HttpDecMath
import Projects.thermostat.StoreRead
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.SendHeadUartCall
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (obj io src body flag : Word) (len : Nat) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (obj+20#32) (body) .w) (obj+44#32) (flag) .b) (obj+48#32) (io) .w) (obj+52#32) (src) .w) (obj+56#32) (BitVec.ofNat 32 len) .w) (obj+88#32) (0#32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (obj io src body flag : Word) (len : Nat) (hl : len≤120) (h8 : c.get 8=obj) (h18 : c.get 18=obj+48#32) (h19 : c.get 19=src) (h10 : c.get 10=body) (h11 : c.get 11=BitVec.ofNat 32 len) (h22 : c.get 22=flag) (hm : Memory.Block B obj 89) (ha : obj.toNat%4=0) (hio : ramRead ram (obj+16#32) .w=io)
    (hp : c.pc=0x80000408#32) :
    ∃ d, Quiet.Steps B img 12 ⟨c,ram⟩ ⟨d,memory ram obj io src body flag len⟩ ∧ d.pc=0x80000786#32 ∧
      d.get 12=193#32 ∧ d.get 10=obj+48#32 ∧ d.get 1=2147484718#32 ∧ (∀ r : Reg, r≠12 → r≠10 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (193#32) 0x8000040c#32
  let r1 := ramWrite ram (obj+20#32) (body) .w
  let c2 := c1.goto 0x8000040e#32
  let r2 := ramWrite r1 (obj+44#32) (flag) .b
  let c3 := c2.goto 0x80000412#32
  let c4 := c3.goto 0x80000416#32
  let c5 := c4.wr 10 (io) 0x80000418#32
  let r3 := ramWrite r2 (obj+48#32) (io) .w
  let c6 := c5.goto 0x8000041a#32
  let r4 := ramWrite r3 (obj+52#32) (src) .w
  let c7 := c6.goto 0x8000041e#32
  let r5 := ramWrite r4 (obj+56#32) (BitVec.ofNat 32 len) .w
  let c8 := c7.goto 0x80000420#32
  let r6 := ramWrite r5 (obj+88#32) (0#32) .b
  let c9 := c8.goto 0x80000424#32
  let c10 := c9.wr 10 (obj+48#32) 0x80000426#32
  let c11 := c10.wr 1 (2147484710#32) 0x8000042a#32
  let c12 := c11.wr 1 (2147484718#32) 0x80000786#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact se2147484680) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x8000040c#32).getLsbD 0=false;decide) se2147484684 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v8 : c1.get 8=obj := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h18,h19,h10,h11,h22]
    have v10 : c1.get 10=body := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h18,h19,h10,h11,h22]
    rw [exec_store,v8,v10,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 5 ha) (Memory.block_access hm (off := 20) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine Quiet.step_of (by change (0x8000040e#32).getLsbD 0=false;decide) se2147484686 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r2 [],[]⟩
    have v8 : c2.get 8=obj := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h19,h10,h11,h22]
    have v22 : c2.get 22=flag := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h19,h10,h11,h22]
    rw [exec_store,v8,v22,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 44) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r2⟩ := by
    refine Quiet.step_of (by change (0x80000412#32).getLsbD 0=false;decide) se2147484690 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r2 0 [] [] = ⟨.ok c4 r2 [],[]⟩
    have v11 : c3.get 11=BitVec.ofNat 32 len := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h19,h10,h11,h22]
    have v12 : c3.get 12=193#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h19,h10,h11,h22]
    rw [exec_branch,v11,v12,HttpDecMath.branch_geu len 193 (by omega) (by decide),show decide (193≤len)=false by simp [show ¬193≤len by omega]];simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r2⟩ ⟨c5,r2⟩ := by
    refine Quiet.step_of (by change (0x80000416#32).getLsbD 0=false;decide) se2147484694 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r2 0 [] [] = ⟨.ok c5 r2 [],[]⟩
    have v8 : c4.get 8=obj := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h19,h10,h11,h22]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 4 ha) (Memory.block_access hm (off := 16) (by decide) (by decide))]
    have he : ramRead r2 (obj+16#32) .w=ramRead ram (obj+16#32) .w := by
      change ramRead (ramWrite (ramWrite ram (obj+20#32) body .w) (obj+44#32) flag .b) (obj+16#32) .w=_
      rw [StoreRead.other _ _ _ _ .w .b (StoreWords.offsets obj 16 4 44 1 (by decide) (by decide) (by decide)),StoreRead.other _ _ _ _ .w .w (StoreWords.offsets obj 16 4 20 4 (by decide) (by decide) (by decide))]
    rw [he,hio];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r2⟩ ⟨c6,r3⟩ := by
    refine Quiet.step_of (by change (0x80000418#32).getLsbD 0=false;decide) se2147484696 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r2 0 [] [] = ⟨.ok c6 r3 [],[]⟩
    have v8 : c5.get 8=obj := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h19,h10,h11,h22]
    have v10 : c5.get 10=io := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h19,h10,h11,h22]
    rw [exec_store,v8,v10,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 12 ha) (Memory.block_access hm (off := 48) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r3⟩ ⟨c7,r4⟩ := by
    refine Quiet.step_of (by change (0x8000041a#32).getLsbD 0=false;decide) se2147484698 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r3 0 [] [] = ⟨.ok c7 r4 [],[]⟩
    have v8 : c6.get 8=obj := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h19,h10,h11,h22]
    have v19 : c6.get 19=src := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h19,h10,h11,h22]
    rw [exec_store,v8,v19,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 13 ha) (Memory.block_access hm (off := 52) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r4⟩ ⟨c8,r5⟩ := by
    refine Quiet.step_of (by change (0x8000041e#32).getLsbD 0=false;decide) se2147484702 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r4 0 [] [] = ⟨.ok c8 r5 [],[]⟩
    have v8 : c7.get 8=obj := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h19,h10,h11,h22]
    have v11 : c7.get 11=BitVec.ofNat 32 len := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h19,h10,h11,h22]
    rw [exec_store,v8,v11,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 14 ha) (Memory.block_access hm (off := 56) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r5⟩ ⟨c9,r6⟩ := by
    refine Quiet.step_of (by change (0x80000420#32).getLsbD 0=false;decide) se2147484704 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r5 0 [] [] = ⟨.ok c9 r6 [],[]⟩
    have v8 : c8.get 8=obj := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h19,h10,h11,h22]
    
    rw [exec_store,v8,Core.get_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 88) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r6⟩ ⟨c10,r6⟩ := by
    refine Quiet.step_of (by change (0x80000424#32).getLsbD 0=false;decide) se2147484708 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r6 0 [] [] = ⟨.ok c10 r6 [],[]⟩
    have v18 : c9.get 18=obj+48#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h19,h10,h11,h22]
    rw [exec_op,Core.get_zero,v18,(show alu .add (0 : Word) (obj+48#32)=obj+48#32 from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r6⟩ ⟨c11,r6⟩ := by
    refine Quiet.step_of (by change (0x80000426#32).getLsbD 0=false;decide) se2147484710 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r6 0 [] [] = ⟨.ok c11 r6 [],[]⟩
    rw [exec_auipc,show c10.pc=2147484710#32 by rfl,BitVec.add_zero];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r6⟩ ⟨c12,r6⟩ := by
    refine Quiet.step_of (by change (0x8000042a#32).getLsbD 0=false;decide) se2147484714 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r6 0 [] [] = ⟨.ok c12 r6 [],[]⟩
    have v1 : c11.get 1=2147484710#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h19,h10,h11,h22]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c11.set 1 (2147484714#32+4#32)) ((2147484710#32+864#32) &&& ~~~1)) r6 0 [] [] = _
    rw [show (2147484710#32+864#32) &&& ~~~1=0x80000786#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c12,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.single t11))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h19,h10,h11,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h19,h10,h11,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h19,h10,h11,h22]
  · intro reg h12 h10 h1;simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h18,h19,h10,h11,h22,h12,h10,h1]
end E5R.Thermostat.SendHeadUartCall
