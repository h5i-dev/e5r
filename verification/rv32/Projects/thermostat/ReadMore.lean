import Projects.thermostat.ReadMoreCode
import Projects.thermostat.Init
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ReadMore
open E5R E5R.Thermostat

def execute (c : Core) (ram : Word → BitVec 8) : Machine :=
  let c1 := c.wr 10 (3#32) 2147486250#32
  let c2 := c1.wr 11 (0#32) 2147486254#32
  let c3 := c2.wr 11 1#32 2147486258#32
  let c4 := c3.wr 12 0#32 2147486262#32
  let c5 := c4.wr 11 0#32 2147486264#32
  let c6 := c5.goto 2147486284#32
  let c7 := c6.wr 10 0#32 2147486286#32
  let c8 := c7.goto 2147486288#32
  let c9 := c8.wr 10 (2164258920#32) 2147486292#32
  let c10 := c9.wr 11 (2048#32) 2147486294#32
  let c11 := c10.wr 10 (0#32) 2147486296#32
  let c12 := c11.goto 2147486304#32
  let c13 := c12.wr 12 (2164255764#32) 2147486306#32
  let c14 := c13.wr 13 (2164260807#32) 2147486310#32
  let c15 := c14.wr 14 2048#32 2147486314#32
  let c16 := c15.wr 12 2164255764#32 2147486316#32
  let r1 := ramWrite ram 2164259288#32 (2164260807#32) .w
  let c17 := c16.goto 2147486320#32
  let r2 := ramWrite r1 2164259292#32 (2164255764#32) .w
  let c18 := c17.goto 2147486324#32
  let r3 := ramWrite r2 2164259296#32 (2048#32) .w
  let c19 := c18.goto 2147486328#32
  let r4 := ramWrite r3 2164259300#32 (0#32) .b
  let c20 := c19.goto 2147486332#32
  let c21 := c20.goto 2147486626#32
  ⟨c21,r4⟩

def memory (ram : Word → BitVec 8) : Word → BitVec 8 :=
  let r1 := ramWrite ram 2164259288#32 (2164260807#32) .w
  let r2 := ramWrite r1 2164259292#32 (2164255764#32) .w
  let r3 := ramWrite r2 2164259296#32 (2048#32) .w
  let r4 := ramWrite r3 2164259300#32 (0#32) .b
  r4

theorem execute_ram (c : Core) (ram : Word → BitVec 8) : (execute c ram).ram = memory ram := rfl

theorem execute_contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000a26#32) (hfp : c.get 8 = 0x80fff814#32)
    (htag : ramRead ram 0x80fffd38#32 .w = 3#32) (haux : ramRead ram 0x80fffd3c#32 .w = 0#32)
    (hfilledPtr : ramRead ram 0x80fff9c8#32 .w = 0x80fff868#32)
    (hcapacity : ramRead ram 0x80fff884#32 .w = 2048#32) (hfilled : ramRead ram 0x80fff868#32 .w = 0#32)
    (hrx : ramRead ram 0x80fff880#32 .w = 0x80ffec14#32) (huartPtr : ramRead ram 0x80fff9cc#32 .w = 0x80ffffc7#32)
    (hm : Memory.Block B 0x80ff0000#32 65536) :
    DetSteps B img 21 ⟨c,ram⟩ (execute c ram) := by
  let c1 := c.wr 10 (3#32) 2147486250#32
  let c2 := c1.wr 11 (0#32) 2147486254#32
  let c3 := c2.wr 11 1#32 2147486258#32
  let c4 := c3.wr 12 0#32 2147486262#32
  let c5 := c4.wr 11 0#32 2147486264#32
  let c6 := c5.goto 2147486284#32
  let c7 := c6.wr 10 0#32 2147486286#32
  let c8 := c7.goto 2147486288#32
  let c9 := c8.wr 10 (2164258920#32) 2147486292#32
  let c10 := c9.wr 11 (2048#32) 2147486294#32
  let c11 := c10.wr 10 (0#32) 2147486296#32
  let c12 := c11.goto 2147486304#32
  let c13 := c12.wr 12 (2164255764#32) 2147486306#32
  let c14 := c13.wr 13 (2164260807#32) 2147486310#32
  let c15 := c14.wr 14 2048#32 2147486314#32
  let c16 := c15.wr 12 2164255764#32 2147486316#32
  let r1 := ramWrite ram 2164259288#32 (2164260807#32) .w
  let c17 := c16.goto 2147486320#32
  let r2 := ramWrite r1 2164259292#32 (2164255764#32) .w
  let c18 := c17.goto 2147486324#32
  let r3 := ramWrite r2 2164259296#32 (2048#32) .w
  let c19 := c18.goto 2147486328#32
  let r4 := ramWrite r3 2164259300#32 (0#32) .b
  let c20 := c19.goto 2147486332#32
  let c21 := c20.goto 2147486626#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact mo2147486246) fun o => ?_
    have haddr : c.get 8+0x00000524#32 = 2164260152#32 := by simp [Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    have hmem : B.inRam (2164260152#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 64824) (width := 4) hm (by decide) (by decide)
    have hread : ramRead ram 2164260152#32 .w = 3#32 := by
      calc
        _ = ramRead ram 2164260152#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,ramWrite,ramPut]
        _ = _ := htag
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164260152#32) o (by decide) hmem,hread,hp]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (2147486250#32).getLsbD 0 = false;decide) mo2147486250 fun o => ?_
    have haddr : c1.get 8+0x00000528#32 = 2164260156#32 := by simp [c1,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    have hmem : B.inRam (2164260156#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 64828) (width := 4) hm (by decide) (by decide)
    have hread : ramRead ram 2164260156#32 .w = 0#32 := by
      calc
        _ = ramRead ram 2164260156#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,ramWrite,ramPut]
        _ = _ := haux
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164260156#32) o (by decide) hmem,hread]
    rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (2147486254#32).getLsbD 0 = false;decide) mo2147486254 fun o => ?_
    have ha : c2.get 11 = 0#32 := by simp [c1,c2,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    rw [exec_opimm,ha]
    rw [show alu .sltu (0#32) (0x00000001#32) = 1#32 by decide +kernel]
    rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (2147486258#32).getLsbD 0 = false;decide) mo2147486258 fun o => ?_
    have ha : c3.get 10 = 3#32 := by simp [c1,c2,c3,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    rw [exec_opimm,ha]
    rw [show alu .sltu (3#32) (0x00000003#32) = 0#32 by decide +kernel]
    rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (2147486262#32).getLsbD 0 = false;decide) mo2147486262 fun o => ?_
    have ha : c4.get 11 = 1#32 := by simp [c1,c2,c3,c4,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    have hb : c4.get 12 = 0#32 := by simp [c1,c2,c3,c4,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    rw [exec_op,ha,hb]
    rw [show alu .and (1#32) (0#32) = 0#32 by decide +kernel]
    rfl
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (2147486264#32).getLsbD 0 = false;decide) mo2147486264 fun o => ?_
    have ha : c5.get 11 = 0#32 := by simp [c1,c2,c3,c4,c5,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    have hb : c5.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    rw [exec_branch,ha,hb]
    have ht : taken .eq (0#32) (0#32) = true := by decide +kernel
    rw [ht]
    simp only [ite_true]
    change interp B img o (jump c5 (2147486264#32+0x00000014#32)) ram 0 [] = _
    rw [show 2147486264#32+0x00000014#32 = 2147486284#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine detStep_of (by change (2147486284#32).getLsbD 0 = false;decide) mo2147486284 fun o => ?_
    have ha : c6.get 10 = 3#32 := by simp [c1,c2,c3,c4,c5,c6,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    rw [exec_opimm,ha]
    rw [show alu .add (3#32) (0xfffffffd#32) = 0#32 by decide +kernel]
    rfl
  have s7 : DetStep B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine detStep_of (by change (2147486286#32).getLsbD 0 = false;decide) mo2147486286 fun o => ?_
    have ha : c7.get 10 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    have hb : c7.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    rw [exec_branch,ha,hb]
    have ht : taken .ne (0#32) (0#32) = false := by decide +kernel
    rw [ht]
    rfl
  have s8 : DetStep B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine detStep_of (by change (2147486288#32).getLsbD 0 = false;decide) mo2147486288 fun o => ?_
    have haddr : c8.get 8+0x000001b4#32 = 2164259272#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    have hmem : B.inRam (2164259272#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 63944) (width := 4) hm (by decide) (by decide)
    have hread : ramRead ram 2164259272#32 .w = 2164258920#32 := by
      calc
        _ = ramRead ram 2164259272#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,ramWrite,ramPut]
        _ = _ := hfilledPtr
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164259272#32) o (by decide) hmem,hread]
    rfl
  have s9 : DetStep B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine detStep_of (by change (2147486292#32).getLsbD 0 = false;decide) mo2147486292 fun o => ?_
    have haddr : c9.get 8+0x00000070#32 = 2164258948#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    have hmem : B.inRam (2164258948#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 63620) (width := 4) hm (by decide) (by decide)
    have hread : ramRead ram 2164258948#32 .w = 2048#32 := by
      calc
        _ = ramRead ram 2164258948#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,ramWrite,ramPut]
        _ = _ := hcapacity
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164258948#32) o (by decide) hmem,hread]
    rfl
  have s10 : DetStep B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine detStep_of (by change (2147486294#32).getLsbD 0 = false;decide) mo2147486294 fun o => ?_
    have haddr : c10.get 10+0x00000000#32 = 2164258920#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    have hmem : B.inRam (2164258920#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 63592) (width := 4) hm (by decide) (by decide)
    have hread : ramRead ram 2164258920#32 .w = 0#32 := by
      calc
        _ = ramRead ram 2164258920#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,ramWrite,ramPut]
        _ = _ := hfilled
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164258920#32) o (by decide) hmem,hread]
    rfl
  have s11 : DetStep B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine detStep_of (by change (2147486296#32).getLsbD 0 = false;decide) mo2147486296 fun o => ?_
    have ha : c11.get 11 = 2048#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    have hb : c11.get 10 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    rw [exec_branch,ha,hb]
    have ht : taken .geu (2048#32) (0#32) = true := by decide +kernel
    rw [ht]
    simp only [ite_true]
    change interp B img o (jump c11 (2147486296#32+0x00000008#32)) ram 0 [] = _
    rw [show 2147486296#32+0x00000008#32 = 2147486304#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  have s12 : DetStep B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine detStep_of (by change (2147486304#32).getLsbD 0 = false;decide) mo2147486304 fun o => ?_
    have haddr : c12.get 8+0x0000006c#32 = 2164258944#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    have hmem : B.inRam (2164258944#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 63616) (width := 4) hm (by decide) (by decide)
    have hread : ramRead ram 2164258944#32 .w = 2164255764#32 := by
      calc
        _ = ramRead ram 2164258944#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,ramWrite,ramPut]
        _ = _ := hrx
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164258944#32) o (by decide) hmem,hread]
    rfl
  have s13 : DetStep B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine detStep_of (by change (2147486306#32).getLsbD 0 = false;decide) mo2147486306 fun o => ?_
    have haddr : c13.get 8+0x000001b8#32 = 2164259276#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    have hmem : B.inRam (2164259276#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 63948) (width := 4) hm (by decide) (by decide)
    have hread : ramRead ram 2164259276#32 .w = 2164260807#32 := by
      calc
        _ = ramRead ram 2164259276#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,ramWrite,ramPut]
        _ = _ := huartPtr
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164259276#32) o (by decide) hmem,hread]
    rfl
  have s14 : DetStep B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine detStep_of (by change (2147486310#32).getLsbD 0 = false;decide) mo2147486310 fun o => ?_
    have ha : c14.get 11 = 2048#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    have hb : c14.get 10 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    rw [exec_op,ha,hb]
    rw [show alu .sub (2048#32) (0#32) = 2048#32 by decide +kernel]
    rfl
  have s15 : DetStep B img ⟨c15,ram⟩ ⟨c16,ram⟩ := by
    refine detStep_of (by change (2147486314#32).getLsbD 0 = false;decide) mo2147486314 fun o => ?_
    have ha : c15.get 12 = 2164255764#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    have hb : c15.get 10 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    rw [exec_op,ha,hb]
    rw [show alu .add (2164255764#32) (0#32) = 2164255764#32 by decide +kernel]
    rfl
  have s16 : DetStep B img ⟨c16,ram⟩ ⟨c17,r1⟩ := by
    refine detStep_of (by change (2147486316#32).getLsbD 0 = false;decide) mo2147486316 fun o => ?_
    have haddr : c16.get 8+0x000001c4#32 = 2164259288#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    have hmem : B.inRam (2164259288#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 63960) (width := 4) hm (by decide) (by decide)
    have hval : c16.get 13 = 2164260807#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164259288#32) o (by decide) hmem]
    rfl
  have s17 : DetStep B img ⟨c17,r1⟩ ⟨c18,r2⟩ := by
    refine detStep_of (by change (2147486320#32).getLsbD 0 = false;decide) mo2147486320 fun o => ?_
    have haddr : c17.get 8+0x000001c8#32 = 2164259292#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    have hmem : B.inRam (2164259292#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 63964) (width := 4) hm (by decide) (by decide)
    have hval : c17.get 12 = 2164255764#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164259292#32) o (by decide) hmem]
    rfl
  have s18 : DetStep B img ⟨c18,r2⟩ ⟨c19,r3⟩ := by
    refine detStep_of (by change (2147486324#32).getLsbD 0 = false;decide) mo2147486324 fun o => ?_
    have haddr : c18.get 8+0x000001cc#32 = 2164259296#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    have hmem : B.inRam (2164259296#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 63968) (width := 4) hm (by decide) (by decide)
    have hval : c18.get 14 = 2048#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164259296#32) o (by decide) hmem]
    rfl
  have s19 : DetStep B img ⟨c19,r3⟩ ⟨c20,r4⟩ := by
    refine detStep_of (by change (2147486328#32).getLsbD 0 = false;decide) mo2147486328 fun o => ?_
    have haddr : c19.get 8+0x000001d0#32 = 2164259300#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    have hmem : B.inRam (2164259300#32) 1 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 63972) (width := 1) hm (by decide) (by decide)
    have hval : c19.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164259300#32) o (by decide) hmem]
    rfl
  have s20 : DetStep B img ⟨c20,r4⟩ ⟨c21,r4⟩ := by
    refine detStep_of (by change (2147486332#32).getLsbD 0 = false;decide) mo2147486332 fun o => ?_
    have ha : c20.get 11 = 2048#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    have hb : c20.get 10 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,Core.wr_get,Core.wr_get_ne,Core.get_zero,hfp]
    rw [exec_branch,ha,hb]
    have ht : taken .ne (2048#32) (0#32) = true := by decide +kernel
    rw [ht]
    simp only [ite_true]
    change interp B img o (jump c20 (2147486332#32+0x00000126#32)) r4 0 [] = _
    rw [show 2147486332#32+0x00000126#32 = 2147486626#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  exact .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.step s13 (.step s14 (.step s15 (.step s16 (.step s17 (.step s18 (.step s19 (.single s20))))))))))))))))))))

theorem fields (c : Core) (ram : Word → BitVec 8) :
    (execute c ram).core.pc = 0x80000ba2#32 ∧ (execute c ram).core.get 10 = 0#32 ∧
    (execute c ram).core.get 12 = 0x80ffec14#32 ∧
    (∀ rr : Reg, rr ≠ 10 → rr ≠ 11 → rr ≠ 12 → rr ≠ 13 → rr ≠ 14 → (execute c ram).core.get rr = c.get rr) ∧
    (execute c ram).core.sameCsr c := by
  refine ⟨rfl,rfl,rfl,?_,by rfl⟩
  intro rr h10 h11 h12 h13 h14
  simp [execute,Core.wr_get_ne,h10,h11,h12,h13,h14]

theorem frame (ram : Word → BitVec 8) (x : Word)
    (hf : ∀ i : Fin 13, x ≠ 0x80fff9d8#32+BitVec.ofNat 32 i.val) : memory ram x = ram x := by
  have h0 : x ≠ 2164259288#32 := hf ⟨0,by decide⟩
  have h1 : x ≠ 2164259289#32 := hf ⟨1,by decide⟩
  have h2 : x ≠ 2164259290#32 := hf ⟨2,by decide⟩
  have h3 : x ≠ 2164259291#32 := hf ⟨3,by decide⟩
  have h4 : x ≠ 2164259292#32 := hf ⟨4,by decide⟩
  have h5 : x ≠ 2164259293#32 := hf ⟨5,by decide⟩
  have h6 : x ≠ 2164259294#32 := hf ⟨6,by decide⟩
  have h7 : x ≠ 2164259295#32 := hf ⟨7,by decide⟩
  have h8 : x ≠ 2164259296#32 := hf ⟨8,by decide⟩
  have h9 : x ≠ 2164259297#32 := hf ⟨9,by decide⟩
  have h10 : x ≠ 2164259298#32 := hf ⟨10,by decide⟩
  have h11 : x ≠ 2164259299#32 := hf ⟨11,by decide⟩
  have h12 : x ≠ 2164259300#32 := hf ⟨12,by decide⟩
  simp [memory,ramWrite,ramPut,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12]

end E5R.Thermostat.ReadMore
