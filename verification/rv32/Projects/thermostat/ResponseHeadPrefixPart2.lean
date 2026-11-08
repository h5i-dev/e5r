import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.ResponseHeadMath
import Projects.thermostat.HttpDecTensMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseHeadPrefixPart2
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (frame+28#32) (body) .w) (frame+32#32) (flag) .w) (dst+12#32) (32#32) .b) (frame+40#32) (192#32) .w) (frame+36#32) ((BitVec.ofNat 32 status)) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat) (hlo : 100≤status) (hhi : status≤599) (hct : ctlen≤16) (h2 : c.get 2=(frame+16#32)) (h5 : c.get 5=13#32) (h6 : c.get 6=(BitVec.ofNat 32 (48+(status/10)%10))) (h7 : c.get 7=(((BitVec.ofNat 32 (status/100))) <<< 1)) (h10 : c.get 10=dst) (h11 : c.get 11=192#32) (h12 : c.get 12=(BitVec.ofNat 32 status)) (h13 : c.get 13=ctptr) (h14 : c.get 14=(BitVec.ofNat 32 ctlen)) (h15 : c.get 15=body) (h16 : c.get 16=flag) (h17 : c.get 17=(BitVec.ofNat 32 (48+status%10))) (h28 : c.get 28=32#32) (hstack : Memory.Block B frame 96) (ha : frame.toNat%4=0) (hdst : Memory.Block B dst 192)
    (hp : c.pc=0x80003fd4#32) :
    ∃ d, Quiet.Steps B img 14 ⟨c,ram⟩ ⟨d,memory ram frame dst ctptr body flag status ctlen⟩ ∧ d.pc=0x80003584#32 ∧
      d.get 27=ctptr ∧ d.get 26=(BitVec.ofNat 32 ctlen) ∧ d.get 13=(BitVec.ofNat 32 status) ∧ d.get 12=13#32 ∧ d.get 23=dst ∧ d.get 1=0x80003ffa#32 ∧ (∀ r : Reg, r≠27 → r≠26 → r≠13 → r≠12 → r≠23 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80003fd8#32
  let c2 := c1.wr 27 (ctptr) 0x80003fda#32
  let c3 := c2.wr 26 ((BitVec.ofNat 32 ctlen)) 0x80003fdc#32
  let r1 := ramWrite ram (frame+28#32) (body) .w
  let c4 := c3.goto 0x80003fde#32
  let r2 := ramWrite r1 (frame+32#32) (flag) .w
  let c5 := c4.goto 0x80003fe0#32
  let c6 := c5.wr 13 (32#32) 0x80003fe4#32
  let r3 := ramWrite r2 (dst+12#32) (32#32) .b
  let c7 := c6.goto 0x80003fe8#32
  let c8 := c7.wr 13 ((BitVec.ofNat 32 status)) 0x80003fea#32
  let c9 := c8.wr 12 (13#32) 0x80003fec#32
  let c10 := c9.wr 23 (dst) 0x80003fee#32
  let r4 := ramWrite r3 (frame+40#32) (192#32) .w
  let c11 := c10.goto 0x80003ff0#32
  let r5 := ramWrite r4 (frame+36#32) ((BitVec.ofNat 32 status)) .w
  let c12 := c11.goto 0x80003ff2#32
  let c13 := c12.wr 1 (2147495922#32) 0x80003ff6#32
  let c14 := c13.wr 1 (0x80003ffa#32) 0x80003584#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147499988) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v11 : c.get 11=192#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    have v5 : c.get 5=13#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_branch,v11,v5,(by decide +kernel : taken .ltu (192#32) (13#32)=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003fd8#32).getLsbD 0=false;decide) rh2147499992 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v13 : c1.get 13=ctptr := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_op,Core.get_zero,v13]
    change Observed.interp B img o (.done (c1.wr 27 (alu .add (0#32) (ctptr)) (c1.pc+2#32))) ram 0 [] [] = _
    rw [(by exact BitVec.zero_add _ : alu .add (0#32) (ctptr)=ctptr)]
    first | rfl | (rw [hp]; rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80003fda#32).getLsbD 0=false;decide) rh2147499994 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v14 : c2.get 14=(BitVec.ofNat 32 ctlen) := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_op,Core.get_zero,v14]
    change Observed.interp B img o (.done (c2.wr 26 (alu .add (0#32) ((BitVec.ofNat 32 ctlen))) (c2.pc+2#32))) ram 0 [] [] = _
    rw [(by exact BitVec.zero_add _ : alu .add (0#32) ((BitVec.ofNat 32 ctlen))=(BitVec.ofNat 32 ctlen))]
    first | rfl | (rw [hp]; rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,r1⟩ := by
    refine Quiet.step_of (by change (0x80003fdc#32).getLsbD 0=false;decide) rh2147499996 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 r1 [],[]⟩
    have v2 : c3.get 2=(frame+16#32) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    have v15 : c3.get 15=body := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_store,v2,v15]
    rw [BitVec.add_assoc,show 16#32+12#32=28#32 by decide +kernel]
    rw [Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 7 ha) (Memory.block_access hstack (off := 28) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r1⟩ ⟨c5,r2⟩ := by
    refine Quiet.step_of (by change (0x80003fde#32).getLsbD 0=false;decide) rh2147499998 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r1 0 [] [] = ⟨.ok c5 r2 [],[]⟩
    have v2 : c4.get 2=(frame+16#32) := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    have v16 : c4.get 16=flag := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_store,v2,v16]
    rw [BitVec.add_assoc,show 16#32+16#32=32#32 by decide +kernel]
    rw [Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 8 ha) (Memory.block_access hstack (off := 32) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r2⟩ ⟨c6,r2⟩ := by
    refine Quiet.step_of (by change (0x80003fe0#32).getLsbD 0=false;decide) rh2147500000 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r2 0 [] [] = ⟨.ok c6 r2 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c5.wr 13 (alu .add (0#32) (32#32)) (c5.pc+4#32))) r2 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t6 : Quiet.Step B img ⟨c6,r2⟩ ⟨c7,r3⟩ := by
    refine Quiet.step_of (by change (0x80003fe4#32).getLsbD 0=false;decide) rh2147500004 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r2 0 [] [] = ⟨.ok c7 r3 [],[]⟩
    have v10 : c6.get 10=dst := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    have v13 : c6.get 13=32#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_store,v10,v13]
    rw [Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hdst (off := 12) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r3⟩ ⟨c8,r3⟩ := by
    refine Quiet.step_of (by change (0x80003fe8#32).getLsbD 0=false;decide) rh2147500008 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r3 0 [] [] = ⟨.ok c8 r3 [],[]⟩
    have v12 : c7.get 12=(BitVec.ofNat 32 status) := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_op,Core.get_zero,v12]
    change Observed.interp B img o (.done (c7.wr 13 (alu .add (0#32) ((BitVec.ofNat 32 status))) (c7.pc+2#32))) r3 0 [] [] = _
    rw [(by exact BitVec.zero_add _ : alu .add (0#32) ((BitVec.ofNat 32 status))=(BitVec.ofNat 32 status))]
    first | rfl | (rw [hp]; rfl)
  have t8 : Quiet.Step B img ⟨c8,r3⟩ ⟨c9,r3⟩ := by
    refine Quiet.step_of (by change (0x80003fea#32).getLsbD 0=false;decide) rh2147500010 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r3 0 [] [] = ⟨.ok c9 r3 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c8.wr 12 (alu .add (0#32) (13#32)) (c8.pc+2#32))) r3 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t9 : Quiet.Step B img ⟨c9,r3⟩ ⟨c10,r3⟩ := by
    refine Quiet.step_of (by change (0x80003fec#32).getLsbD 0=false;decide) rh2147500012 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r3 0 [] [] = ⟨.ok c10 r3 [],[]⟩
    have v10 : c9.get 10=dst := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_op,Core.get_zero,v10]
    change Observed.interp B img o (.done (c9.wr 23 (alu .add (0#32) (dst)) (c9.pc+2#32))) r3 0 [] [] = _
    rw [(by exact BitVec.zero_add _ : alu .add (0#32) (dst)=dst)]
    first | rfl | (rw [hp]; rfl)
  have t10 : Quiet.Step B img ⟨c10,r3⟩ ⟨c11,r4⟩ := by
    refine Quiet.step_of (by change (0x80003fee#32).getLsbD 0=false;decide) rh2147500014 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r3 0 [] [] = ⟨.ok c11 r4 [],[]⟩
    have v2 : c10.get 2=(frame+16#32) := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    have v11 : c10.get 11=192#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_store,v2,v11]
    rw [BitVec.add_assoc,show 16#32+24#32=40#32 by decide +kernel]
    rw [Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 10 ha) (Memory.block_access hstack (off := 40) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r4⟩ ⟨c12,r5⟩ := by
    refine Quiet.step_of (by change (0x80003ff0#32).getLsbD 0=false;decide) rh2147500016 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r4 0 [] [] = ⟨.ok c12 r5 [],[]⟩
    have v2 : c11.get 2=(frame+16#32) := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    have v13 : c11.get 13=(BitVec.ofNat 32 status) := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_store,v2,v13]
    rw [BitVec.add_assoc,show 16#32+20#32=36#32 by decide +kernel]
    rw [Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 9 ha) (Memory.block_access hstack (off := 36) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,r5⟩ ⟨c13,r5⟩ := by
    refine Quiet.step_of (by change (0x80003ff2#32).getLsbD 0=false;decide) rh2147500018 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r5 0 [] [] = ⟨.ok c13 r5 [],[]⟩
    rw [exec_auipc,show c12.pc=2147500018#32 by rfl,show 2147500018#32+4294963200#32=2147495922#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r5⟩ ⟨c14,r5⟩ := by
    refine Quiet.step_of (by change (0x80003ff6#32).getLsbD 0=false;decide) rh2147500022 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r5 0 [] [] = ⟨.ok c14 r5 [],[]⟩
    have v1 : c13.get 1=2147495922#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c13.set 1 (0x80003ff6#32+4#32)) ((0x80002ff2#32+1426#32) &&& ~~~1)) r5 0 [] [] = _
    rw [show (0x80002ff2#32+1426#32) &&& ~~~1=0x80003584#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c14,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.single t13))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28]
  · intro reg h27 h26 h13 h12 h23 h1;simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,h16,h17,h28,h27,h26,h13,h12,h23,h1]
end E5R.Thermostat.ResponseHeadPrefixPart2
