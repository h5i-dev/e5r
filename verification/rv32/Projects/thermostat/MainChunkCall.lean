import Projects.thermostat.MainChunkCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainChunkCall
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp rx lim index maxBody : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+4880#32) (ramRead ram (sp+3696#32) .w) .w) (sp+4884#32) (ramRead ram (sp+3700#32) .w) .w) (sp+4888#32) (ramRead ram (sp+3704#32) .w) .w) (sp+4892#32) (ramRead ram (sp+3708#32) .w) .w) (sp+4864#32) (ramRead ram (sp+3680#32) .w) .w) (sp+4868#32) (ramRead ram (sp+3684#32) .w) .w) (sp+4872#32) (ramRead ram (sp+3688#32) .w) .w) (sp+4876#32) (ramRead ram (sp+3692#32) .w) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp rx lim index maxBody : Word) (h2 : c.get 2=sp) (h8 : c.get 8=sp+3204#32) (h23 : c.get 23=sp+3680#32) (h24 : c.get 24=index)
    (hm : Memory.Block B sp 4928) (ha : sp.toNat%4=0)
    (hlim : Memory.Block B lim 8) (hlima : lim.toNat%4=0) (hrx : B.inRam (rx+index) 1=true)
    (hrxPtr : ramRead ram (sp+3312#32) .w=rx) (hlimPtr : ramRead ram (sp+3636#32) .w=lim)
    (hmax : ramRead ram (lim+4#32) .w=maxBody)
    (hp : c.pc=0x80000eaa#32) :
    ∃ d, Quiet.Steps B img 30 ⟨c,ram⟩ ⟨d,memory ram sp rx lim index maxBody⟩ ∧ d.pc=0x80002998#32 ∧
      d.get 10=sp+4824#32 ∧ d.get 11=sp+4864#32 ∧ d.get 12=BitVec.ofNat 32 (ram (rx+index)).toNat ∧ d.get 14=ramRead ram (sp+3700#32) .w ∧ d.get 15=ramRead ram (sp+3704#32) .w ∧ d.get 16=ramRead ram (sp+3708#32) .w ∧ d.get 17=ramRead ram (sp+3680#32) .w ∧ d.get 5=ramRead ram (sp+3684#32) .w ∧ d.get 6=ramRead ram (sp+3688#32) .w ∧ d.get 7=ramRead ram (sp+3692#32) .w ∧ d.get 20=BitVec.ofNat 32 (ram (rx+index)).toNat ∧ d.get 13=maxBody ∧ d.get 1=0x80000f10#32 ∧ (∀ r : Reg, r≠10 → r≠11 → r≠12 → r≠14 → r≠15 → r≠16 → r≠17 → r≠5 → r≠6 → r≠7 → r≠20 → r≠13 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (rx) 0x80000eac#32
  let c2 := c1.wr 11 (lim) 0x80000eb0#32
  let c3 := c2.wr 12 (ramRead ram (sp+3696#32) .w) 0x80000eb4#32
  let c4 := c3.wr 14 (ramRead ram (sp+3700#32) .w) 0x80000eb8#32
  let c5 := c4.wr 15 (ramRead ram (sp+3704#32) .w) 0x80000ebc#32
  let c6 := c5.wr 16 (ramRead ram (sp+3708#32) .w) 0x80000ec0#32
  let c7 := c6.wr 10 (rx+index) 0x80000ec2#32
  let c8 := c7.wr 17 (ramRead ram (sp+3680#32) .w) 0x80000ec6#32
  let c9 := c8.wr 5 (ramRead ram (sp+3684#32) .w) 0x80000eca#32
  let c10 := c9.wr 6 (ramRead ram (sp+3688#32) .w) 0x80000ece#32
  let c11 := c10.wr 7 (ramRead ram (sp+3692#32) .w) 0x80000ed2#32
  let c12 := c11.wr 20 (BitVec.ofNat 32 (ram (rx+index)).toNat) 0x80000ed6#32
  let c13 := c12.wr 13 (maxBody) 0x80000ed8#32
  let r1 := ramWrite ram (sp+4880#32) (ramRead ram (sp+3696#32) .w) .w
  let c14 := c13.goto 0x80000edc#32
  let r2 := ramWrite r1 (sp+4884#32) (ramRead ram (sp+3700#32) .w) .w
  let c15 := c14.goto 0x80000ee0#32
  let r3 := ramWrite r2 (sp+4888#32) (ramRead ram (sp+3704#32) .w) .w
  let c16 := c15.goto 0x80000ee4#32
  let r4 := ramWrite r3 (sp+4892#32) (ramRead ram (sp+3708#32) .w) .w
  let c17 := c16.goto 0x80000ee8#32
  let r5 := ramWrite r4 (sp+4864#32) (ramRead ram (sp+3680#32) .w) .w
  let c18 := c17.goto 0x80000eec#32
  let r6 := ramWrite r5 (sp+4868#32) (ramRead ram (sp+3684#32) .w) .w
  let c19 := c18.goto 0x80000ef0#32
  let r7 := ramWrite r6 (sp+4872#32) (ramRead ram (sp+3688#32) .w) .w
  let c20 := c19.goto 0x80000ef4#32
  let r8 := ramWrite r7 (sp+4876#32) (ramRead ram (sp+3692#32) .w) .w
  let c21 := c20.goto 0x80000ef8#32
  let c22 := c21.wr 10 (4096#32) 0x80000efa#32
  let c23 := c22.wr 10 (4824#32) 0x80000efe#32
  let c24 := c23.wr 10 (sp+4824#32) 0x80000f00#32
  let c25 := c24.wr 11 (19#32) 0x80000f02#32
  let c26 := c25.wr 11 (4864#32) 0x80000f04#32
  let c27 := c26.wr 11 (sp+4864#32) 0x80000f06#32
  let c28 := c27.wr 12 (BitVec.ofNat 32 (ram (rx+index)).toNat) 0x80000f08#32
  let c29 := c28.wr 1 (0x80002f08#32) 0x80000f0c#32
  let c30 := c29.wr 1 (0x80000f10#32) 0x80002998#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact cc2147487402) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=sp+3204#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+108#32=3312#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 828 ha) (Memory.block_access hm (off := 3312) (by decide) (by decide)),hrxPtr];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000eac#32).getLsbD 0=false;decide) cc2147487404 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=sp+3204#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+432#32=3636#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 909 ha) (Memory.block_access hm (off := 3636) (by decide) (by decide)),hlimPtr];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000eb0#32).getLsbD 0=false;decide) cc2147487408 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v23 : c2.get 23=sp+3680#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_load,v23,BitVec.add_assoc,show 3680#32+16#32=3696#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 924 ha) (Memory.block_access hm (off := 3696) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000eb4#32).getLsbD 0=false;decide) cc2147487412 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v23 : c3.get 23=sp+3680#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_load,v23,BitVec.add_assoc,show 3680#32+20#32=3700#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 925 ha) (Memory.block_access hm (off := 3700) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80000eb8#32).getLsbD 0=false;decide) cc2147487416 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v23 : c4.get 23=sp+3680#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_load,v23,BitVec.add_assoc,show 3680#32+24#32=3704#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 926 ha) (Memory.block_access hm (off := 3704) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80000ebc#32).getLsbD 0=false;decide) cc2147487420 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v23 : c5.get 23=sp+3680#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_load,v23,BitVec.add_assoc,show 3680#32+28#32=3708#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 927 ha) (Memory.block_access hm (off := 3708) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80000ec0#32).getLsbD 0=false;decide) cc2147487424 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v10 : c6.get 10=rx := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    have v24 : c6.get 24=index := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_op,v10,v24];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80000ec2#32).getLsbD 0=false;decide) cc2147487426 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v23 : c7.get 23=sp+3680#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_load,v23,BitVec.add_assoc,show 3680#32+0#32=3680#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 920 ha) (Memory.block_access hm (off := 3680) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80000ec6#32).getLsbD 0=false;decide) cc2147487430 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v23 : c8.get 23=sp+3680#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_load,v23,BitVec.add_assoc,show 3680#32+4#32=3684#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 921 ha) (Memory.block_access hm (off := 3684) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80000eca#32).getLsbD 0=false;decide) cc2147487434 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v23 : c9.get 23=sp+3680#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_load,v23,BitVec.add_assoc,show 3680#32+8#32=3688#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 922 ha) (Memory.block_access hm (off := 3688) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80000ece#32).getLsbD 0=false;decide) cc2147487438 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v23 : c10.get 23=sp+3680#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_load,v23,BitVec.add_assoc,show 3680#32+12#32=3692#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 923 ha) (Memory.block_access hm (off := 3692) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x80000ed2#32).getLsbD 0=false;decide) cc2147487442 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v10 : c11.get 10=rx+index := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_load,v10,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hrx,Memory.load_byte];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x80000ed6#32).getLsbD 0=false;decide) cc2147487446 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    have v11 : c12.get 11=lim := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned lim 1 hlima) (Memory.block_access hlim (off := 4) (by decide) (by decide)),hmax];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,r1⟩ := by
    refine Quiet.step_of (by change (0x80000ed8#32).getLsbD 0=false;decide) cc2147487448 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 r1 [],[]⟩
    have v8 : c13.get 8=sp+3204#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    have v12 : c13.get 12=ramRead ram (sp+3696#32) .w := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_store,v8,v12,BitVec.add_assoc,show 3204#32+1676#32=4880#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1220 ha)
        (Memory.block_access hm (off := 4880) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,r1⟩ ⟨c15,r2⟩ := by
    refine Quiet.step_of (by change (0x80000edc#32).getLsbD 0=false;decide) cc2147487452 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) r1 0 [] [] = ⟨.ok c15 r2 [],[]⟩
    have v8 : c14.get 8=sp+3204#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    have v14 : c14.get 14=ramRead ram (sp+3700#32) .w := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_store,v8,v14,BitVec.add_assoc,show 3204#32+1680#32=4884#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1221 ha)
        (Memory.block_access hm (off := 4884) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,r2⟩ ⟨c16,r3⟩ := by
    refine Quiet.step_of (by change (0x80000ee0#32).getLsbD 0=false;decide) cc2147487456 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) r2 0 [] [] = ⟨.ok c16 r3 [],[]⟩
    have v8 : c15.get 8=sp+3204#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    have v15 : c15.get 15=ramRead ram (sp+3704#32) .w := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_store,v8,v15,BitVec.add_assoc,show 3204#32+1684#32=4888#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1222 ha)
        (Memory.block_access hm (off := 4888) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,r3⟩ ⟨c17,r4⟩ := by
    refine Quiet.step_of (by change (0x80000ee4#32).getLsbD 0=false;decide) cc2147487460 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) r3 0 [] [] = ⟨.ok c17 r4 [],[]⟩
    have v8 : c16.get 8=sp+3204#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    have v16 : c16.get 16=ramRead ram (sp+3708#32) .w := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_store,v8,v16,BitVec.add_assoc,show 3204#32+1688#32=4892#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1223 ha)
        (Memory.block_access hm (off := 4892) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,r4⟩ ⟨c18,r5⟩ := by
    refine Quiet.step_of (by change (0x80000ee8#32).getLsbD 0=false;decide) cc2147487464 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) r4 0 [] [] = ⟨.ok c18 r5 [],[]⟩
    have v8 : c17.get 8=sp+3204#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    have v17 : c17.get 17=ramRead ram (sp+3680#32) .w := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_store,v8,v17,BitVec.add_assoc,show 3204#32+1660#32=4864#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1216 ha)
        (Memory.block_access hm (off := 4864) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,r5⟩ ⟨c19,r6⟩ := by
    refine Quiet.step_of (by change (0x80000eec#32).getLsbD 0=false;decide) cc2147487468 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) r5 0 [] [] = ⟨.ok c19 r6 [],[]⟩
    have v8 : c18.get 8=sp+3204#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    have v5 : c18.get 5=ramRead ram (sp+3684#32) .w := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_store,v8,v5,BitVec.add_assoc,show 3204#32+1664#32=4868#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1217 ha)
        (Memory.block_access hm (off := 4868) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,r6⟩ ⟨c20,r7⟩ := by
    refine Quiet.step_of (by change (0x80000ef0#32).getLsbD 0=false;decide) cc2147487472 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) r6 0 [] [] = ⟨.ok c20 r7 [],[]⟩
    have v8 : c19.get 8=sp+3204#32 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    have v6 : c19.get 6=ramRead ram (sp+3688#32) .w := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_store,v8,v6,BitVec.add_assoc,show 3204#32+1668#32=4872#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1218 ha)
        (Memory.block_access hm (off := 4872) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,r7⟩ ⟨c21,r8⟩ := by
    refine Quiet.step_of (by change (0x80000ef4#32).getLsbD 0=false;decide) cc2147487476 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) r7 0 [] [] = ⟨.ok c21 r8 [],[]⟩
    have v8 : c20.get 8=sp+3204#32 := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    have v7 : c20.get 7=ramRead ram (sp+3692#32) .w := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_store,v8,v7,BitVec.add_assoc,show 3204#32+1672#32=4876#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1219 ha)
        (Memory.block_access hm (off := 4876) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,r8⟩ ⟨c22,r8⟩ := by
    refine Quiet.step_of (by change (0x80000ef8#32).getLsbD 0=false;decide) cc2147487480 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) r8 0 [] [] = ⟨.ok c22 r8 [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,r8⟩ ⟨c23,r8⟩ := by
    refine Quiet.step_of (by change (0x80000efa#32).getLsbD 0=false;decide) cc2147487482 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) r8 0 [] [] = ⟨.ok c23 r8 [],[]⟩
    have v10 : c22.get 10=4096#32 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  have t23 : Quiet.Step B img ⟨c23,r8⟩ ⟨c24,r8⟩ := by
    refine Quiet.step_of (by change (0x80000efe#32).getLsbD 0=false;decide) cc2147487486 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) r8 0 [] [] = ⟨.ok c24 r8 [],[]⟩
    have v10 : c23.get 10=4824#32 := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    have v2 : c23.get 2=sp := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_op,v10,v2,(show alu .add 4824#32 sp=sp+4824#32 from BitVec.add_comm _ _)];first | rfl | (rw [hp];rfl)
  have t24 : Quiet.Step B img ⟨c24,r8⟩ ⟨c25,r8⟩ := by
    refine Quiet.step_of (by change (0x80000f00#32).getLsbD 0=false;decide) cc2147487488 fun o => ?_
    change Observed.interp B img o (exec c24 _ _) r8 0 [] [] = ⟨.ok c25 r8 [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t25 : Quiet.Step B img ⟨c25,r8⟩ ⟨c26,r8⟩ := by
    refine Quiet.step_of (by change (0x80000f02#32).getLsbD 0=false;decide) cc2147487490 fun o => ?_
    change Observed.interp B img o (exec c25 _ _) r8 0 [] [] = ⟨.ok c26 r8 [],[]⟩
    have v11 : c25.get 11=19#32 := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_opimm,v11];first | rfl | (rw [hp];rfl)
  have t26 : Quiet.Step B img ⟨c26,r8⟩ ⟨c27,r8⟩ := by
    refine Quiet.step_of (by change (0x80000f04#32).getLsbD 0=false;decide) cc2147487492 fun o => ?_
    change Observed.interp B img o (exec c26 _ _) r8 0 [] [] = ⟨.ok c27 r8 [],[]⟩
    have v11 : c26.get 11=4864#32 := by simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    have v2 : c26.get 2=sp := by simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_op,v11,v2,(show alu .add 4864#32 sp=sp+4864#32 from BitVec.add_comm _ _)];first | rfl | (rw [hp];rfl)
  have t27 : Quiet.Step B img ⟨c27,r8⟩ ⟨c28,r8⟩ := by
    refine Quiet.step_of (by change (0x80000f06#32).getLsbD 0=false;decide) cc2147487494 fun o => ?_
    change Observed.interp B img o (exec c27 _ _) r8 0 [] [] = ⟨.ok c28 r8 [],[]⟩
    have v20 : c27.get 20=BitVec.ofNat 32 (ram (rx+index)).toNat := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_op,Core.get_zero,v20,(show alu .add (0 : Word) (BitVec.ofNat 32 (ram (rx+index)).toNat)=BitVec.ofNat 32 (ram (rx+index)).toNat from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  have t28 : Quiet.Step B img ⟨c28,r8⟩ ⟨c29,r8⟩ := by
    refine Quiet.step_of (by change (0x80000f08#32).getLsbD 0=false;decide) cc2147487496 fun o => ?_
    change Observed.interp B img o (exec c28 _ _) r8 0 [] [] = ⟨.ok c29 r8 [],[]⟩
    rw [exec_auipc,show c28.pc=0x80000f08#32 by rfl,show 0x80000f08#32+8192#32=0x80002f08#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t29 : Quiet.Step B img ⟨c29,r8⟩ ⟨c30,r8⟩ := by
    refine Quiet.step_of (by change (0x80000f0c#32).getLsbD 0=false;decide) cc2147487500 fun o => ?_
    change Observed.interp B img o (exec c29 _ _) r8 0 [] [] = ⟨.ok c30 r8 [],[]⟩
    have v1 : c29.get 1=0x80002f08#32 := by simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c29.set 1 (0x80000f0c#32+4#32)) ((0x80002f08#32+0xfffffa90#32) &&& ~~~1)) r8 0 [] [] = _
    rw [show (0x80002f08#32+0xfffffa90#32) &&& ~~~1=0x80002998#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c30,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.step t23 (.step t24 (.step t25 (.step t26 (.step t27 (.step t28 (.single t29))))))))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24]
  · intro reg h10 h11 h12 h14 h15 h16 h17 h5 h6 h7 h20 h13 h1;simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h23,h24,h10,h11,h12,h14,h15,h16,h17,h5,h6,h7,h20,h13,h1]
end E5R.Thermostat.MainChunkCall
