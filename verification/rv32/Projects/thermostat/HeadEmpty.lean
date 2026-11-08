import Projects.thermostat.HeadEmptyCode
import Projects.thermostat.Init
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadEmpty
open E5R E5R.Thermostat

def execute (c : Core) (ram : Word → BitVec 8) : Machine :=
  let c1 := c.wr 2 2164255248#32 2147494984#32
  let r1 := ramWrite ram 2164255628#32 (2147486246#32) .w
  let c2 := c1.goto 2147494988#32
  let r2 := ramWrite r1 2164255624#32 (c.get 8) .w
  let c3 := c2.goto 2147494992#32
  let r3 := ramWrite r2 2164255620#32 (c.get 9) .w
  let c4 := c3.goto 2147494996#32
  let r4 := ramWrite r3 2164255616#32 (c.get 18) .w
  let c5 := c4.goto 2147495000#32
  let r5 := ramWrite r4 2164255612#32 (c.get 19) .w
  let c6 := c5.goto 2147495004#32
  let r6 := ramWrite r5 2164255608#32 (c.get 20) .w
  let c7 := c6.goto 2147495008#32
  let r7 := ramWrite r6 2164255604#32 (c.get 21) .w
  let c8 := c7.goto 2147495012#32
  let r8 := ramWrite r7 2164255600#32 (c.get 22) .w
  let c9 := c8.goto 2147495016#32
  let r9 := ramWrite r8 2164255596#32 (c.get 23) .w
  let c10 := c9.goto 2147495020#32
  let r10 := ramWrite r9 2164255592#32 (c.get 24) .w
  let c11 := c10.goto 2147495024#32
  let r11 := ramWrite r10 2164255588#32 (c.get 25) .w
  let c12 := c11.goto 2147495028#32
  let r12 := ramWrite r11 2164255584#32 (c.get 26) .w
  let c13 := c12.goto 2147495032#32
  let r13 := ramWrite r12 2164255580#32 (c.get 27) .w
  let c14 := c13.goto 2147495036#32
  let c15 := c14.wr 16 (1024#32) 2147495040#32
  let c16 := c15.wr 14 0#32 2147495042#32
  let c17 := c16.goto 2147495048#32
  let c18 := c17.goto 2147495142#32
  let c19 := c18.goto 2147495146#32
  let c20 := c19.wr 11 3#32 2147495148#32
  let r14 := ramWrite r13 2164260152#32 (3#32) .w
  let c21 := c20.goto 2147495150#32
  let r15 := ramWrite r14 2164260156#32 (0#32) .w
  let c22 := c21.goto 2147495154#32
  let c23 := c22.goto 2147495274#32
  let c24 := c23.wr 1 (2147486246#32) 2147495278#32
  let c25 := c24.wr 8 (c.get 8) 2147495282#32
  let c26 := c25.wr 9 (c.get 9) 2147495286#32
  let c27 := c26.wr 18 (c.get 18) 2147495290#32
  let c28 := c27.wr 19 (c.get 19) 2147495294#32
  let c29 := c28.wr 20 (c.get 20) 2147495298#32
  let c30 := c29.wr 21 (c.get 21) 2147495302#32
  let c31 := c30.wr 22 (c.get 22) 2147495306#32
  let c32 := c31.wr 23 (c.get 23) 2147495310#32
  let c33 := c32.wr 24 (c.get 24) 2147495314#32
  let c34 := c33.wr 25 (c.get 25) 2147495318#32
  let c35 := c34.wr 26 (c.get 26) 2147495322#32
  let c36 := c35.wr 27 (c.get 27) 2147495326#32
  let c37 := c36.wr 2 2164255632#32 2147495328#32
  let c38 := c37.goto 2147486246#32
  ⟨c38,r15⟩

def memory (c : Core) (ram : Word → BitVec 8) : Word → BitVec 8 :=
  let r1 := ramWrite ram 2164255628#32 (2147486246#32) .w
  let r2 := ramWrite r1 2164255624#32 (c.get 8) .w
  let r3 := ramWrite r2 2164255620#32 (c.get 9) .w
  let r4 := ramWrite r3 2164255616#32 (c.get 18) .w
  let r5 := ramWrite r4 2164255612#32 (c.get 19) .w
  let r6 := ramWrite r5 2164255608#32 (c.get 20) .w
  let r7 := ramWrite r6 2164255604#32 (c.get 21) .w
  let r8 := ramWrite r7 2164255600#32 (c.get 22) .w
  let r9 := ramWrite r8 2164255596#32 (c.get 23) .w
  let r10 := ramWrite r9 2164255592#32 (c.get 24) .w
  let r11 := ramWrite r10 2164255588#32 (c.get 25) .w
  let r12 := ramWrite r11 2164255584#32 (c.get 26) .w
  let r13 := ramWrite r12 2164255580#32 (c.get 27) .w
  let r14 := ramWrite r13 2164260152#32 (3#32) .w
  let r15 := ramWrite r14 2164260156#32 (0#32) .w
  r15

theorem execute_ram (c : Core) (ram : Word → BitVec 8) : (execute c ram).ram = memory c ram := rfl

theorem execute_contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80002c46#32) (hsp : c.get 2 = 0x80ffeb90#32)
    (hret : c.get 1 = 0x80000a26#32) (hout : c.get 10 = 0x80fffd38#32)
    (hlen : c.get 12 = 0#32) (hmaxptr : c.get 13 = 0x80fff860#32)
    (hmax : ramRead ram 0x80fff860#32 .w = 1024#32) (hm : Memory.Block B 0x80ff0000#32 65536) :
    DetSteps B img 38 ⟨c,ram⟩ (execute c ram) := by
  let c1 := c.wr 2 2164255248#32 2147494984#32
  let r1 := ramWrite ram 2164255628#32 (2147486246#32) .w
  let c2 := c1.goto 2147494988#32
  let r2 := ramWrite r1 2164255624#32 (c.get 8) .w
  let c3 := c2.goto 2147494992#32
  let r3 := ramWrite r2 2164255620#32 (c.get 9) .w
  let c4 := c3.goto 2147494996#32
  let r4 := ramWrite r3 2164255616#32 (c.get 18) .w
  let c5 := c4.goto 2147495000#32
  let r5 := ramWrite r4 2164255612#32 (c.get 19) .w
  let c6 := c5.goto 2147495004#32
  let r6 := ramWrite r5 2164255608#32 (c.get 20) .w
  let c7 := c6.goto 2147495008#32
  let r7 := ramWrite r6 2164255604#32 (c.get 21) .w
  let c8 := c7.goto 2147495012#32
  let r8 := ramWrite r7 2164255600#32 (c.get 22) .w
  let c9 := c8.goto 2147495016#32
  let r9 := ramWrite r8 2164255596#32 (c.get 23) .w
  let c10 := c9.goto 2147495020#32
  let r10 := ramWrite r9 2164255592#32 (c.get 24) .w
  let c11 := c10.goto 2147495024#32
  let r11 := ramWrite r10 2164255588#32 (c.get 25) .w
  let c12 := c11.goto 2147495028#32
  let r12 := ramWrite r11 2164255584#32 (c.get 26) .w
  let c13 := c12.goto 2147495032#32
  let r13 := ramWrite r12 2164255580#32 (c.get 27) .w
  let c14 := c13.goto 2147495036#32
  let c15 := c14.wr 16 (1024#32) 2147495040#32
  let c16 := c15.wr 14 0#32 2147495042#32
  let c17 := c16.goto 2147495048#32
  let c18 := c17.goto 2147495142#32
  let c19 := c18.goto 2147495146#32
  let c20 := c19.wr 11 3#32 2147495148#32
  let r14 := ramWrite r13 2164260152#32 (3#32) .w
  let c21 := c20.goto 2147495150#32
  let r15 := ramWrite r14 2164260156#32 (0#32) .w
  let c22 := c21.goto 2147495154#32
  let c23 := c22.goto 2147495274#32
  let c24 := c23.wr 1 (2147486246#32) 2147495278#32
  let c25 := c24.wr 8 (c.get 8) 2147495282#32
  let c26 := c25.wr 9 (c.get 9) 2147495286#32
  let c27 := c26.wr 18 (c.get 18) 2147495290#32
  let c28 := c27.wr 19 (c.get 19) 2147495294#32
  let c29 := c28.wr 20 (c.get 20) 2147495298#32
  let c30 := c29.wr 21 (c.get 21) 2147495302#32
  let c31 := c30.wr 22 (c.get 22) 2147495306#32
  let c32 := c31.wr 23 (c.get 23) 2147495310#32
  let c33 := c32.wr 24 (c.get 24) 2147495314#32
  let c34 := c33.wr 25 (c.get 25) 2147495318#32
  let c35 := c34.wr 26 (c.get 26) 2147495322#32
  let c36 := c35.wr 27 (c.get 27) 2147495326#32
  let c37 := c36.wr 2 2164255632#32 2147495328#32
  let c38 := c37.goto 2147486246#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact he2147494982) fun o => ?_
    have ha : c.get 2 = 2164255632#32 := by simp [Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_opimm,ha,hp]
    simp only [alu]
    rw [show (2164255632#32)+(0xfffffe80#32) = 2164255248#32 by decide +kernel]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine detStep_of (by change (2147494984#32).getLsbD 0 = false;decide) he2147494984 fun o => ?_
    have haddr : c1.get 2+0x0000017c#32 = 2164255628#32 := by simp [c1,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255628#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60300) (width := 4) hm (by decide) (by decide)
    have hval : c1.get 1 = 2147486246#32 := by simp [c1,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255628#32) o (by decide) hmem]
    rfl
  have s2 : DetStep B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine detStep_of (by change (2147494988#32).getLsbD 0 = false;decide) he2147494988 fun o => ?_
    have haddr : c2.get 2+0x00000178#32 = 2164255624#32 := by simp [c1,c2,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255624#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60296) (width := 4) hm (by decide) (by decide)
    have hval : c2.get 8 = c.get 8 := by simp [c1,c2,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255624#32) o (by decide) hmem]
    rfl
  have s3 : DetStep B img ⟨c3,r2⟩ ⟨c4,r3⟩ := by
    refine detStep_of (by change (2147494992#32).getLsbD 0 = false;decide) he2147494992 fun o => ?_
    have haddr : c3.get 2+0x00000174#32 = 2164255620#32 := by simp [c1,c2,c3,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255620#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60292) (width := 4) hm (by decide) (by decide)
    have hval : c3.get 9 = c.get 9 := by simp [c1,c2,c3,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255620#32) o (by decide) hmem]
    rfl
  have s4 : DetStep B img ⟨c4,r3⟩ ⟨c5,r4⟩ := by
    refine detStep_of (by change (2147494996#32).getLsbD 0 = false;decide) he2147494996 fun o => ?_
    have haddr : c4.get 2+0x00000170#32 = 2164255616#32 := by simp [c1,c2,c3,c4,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255616#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60288) (width := 4) hm (by decide) (by decide)
    have hval : c4.get 18 = c.get 18 := by simp [c1,c2,c3,c4,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255616#32) o (by decide) hmem]
    rfl
  have s5 : DetStep B img ⟨c5,r4⟩ ⟨c6,r5⟩ := by
    refine detStep_of (by change (2147495000#32).getLsbD 0 = false;decide) he2147495000 fun o => ?_
    have haddr : c5.get 2+0x0000016c#32 = 2164255612#32 := by simp [c1,c2,c3,c4,c5,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255612#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60284) (width := 4) hm (by decide) (by decide)
    have hval : c5.get 19 = c.get 19 := by simp [c1,c2,c3,c4,c5,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255612#32) o (by decide) hmem]
    rfl
  have s6 : DetStep B img ⟨c6,r5⟩ ⟨c7,r6⟩ := by
    refine detStep_of (by change (2147495004#32).getLsbD 0 = false;decide) he2147495004 fun o => ?_
    have haddr : c6.get 2+0x00000168#32 = 2164255608#32 := by simp [c1,c2,c3,c4,c5,c6,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255608#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60280) (width := 4) hm (by decide) (by decide)
    have hval : c6.get 20 = c.get 20 := by simp [c1,c2,c3,c4,c5,c6,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255608#32) o (by decide) hmem]
    rfl
  have s7 : DetStep B img ⟨c7,r6⟩ ⟨c8,r7⟩ := by
    refine detStep_of (by change (2147495008#32).getLsbD 0 = false;decide) he2147495008 fun o => ?_
    have haddr : c7.get 2+0x00000164#32 = 2164255604#32 := by simp [c1,c2,c3,c4,c5,c6,c7,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255604#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60276) (width := 4) hm (by decide) (by decide)
    have hval : c7.get 21 = c.get 21 := by simp [c1,c2,c3,c4,c5,c6,c7,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255604#32) o (by decide) hmem]
    rfl
  have s8 : DetStep B img ⟨c8,r7⟩ ⟨c9,r8⟩ := by
    refine detStep_of (by change (2147495012#32).getLsbD 0 = false;decide) he2147495012 fun o => ?_
    have haddr : c8.get 2+0x00000160#32 = 2164255600#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255600#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60272) (width := 4) hm (by decide) (by decide)
    have hval : c8.get 22 = c.get 22 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255600#32) o (by decide) hmem]
    rfl
  have s9 : DetStep B img ⟨c9,r8⟩ ⟨c10,r9⟩ := by
    refine detStep_of (by change (2147495016#32).getLsbD 0 = false;decide) he2147495016 fun o => ?_
    have haddr : c9.get 2+0x0000015c#32 = 2164255596#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255596#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60268) (width := 4) hm (by decide) (by decide)
    have hval : c9.get 23 = c.get 23 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255596#32) o (by decide) hmem]
    rfl
  have s10 : DetStep B img ⟨c10,r9⟩ ⟨c11,r10⟩ := by
    refine detStep_of (by change (2147495020#32).getLsbD 0 = false;decide) he2147495020 fun o => ?_
    have haddr : c10.get 2+0x00000158#32 = 2164255592#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255592#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60264) (width := 4) hm (by decide) (by decide)
    have hval : c10.get 24 = c.get 24 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255592#32) o (by decide) hmem]
    rfl
  have s11 : DetStep B img ⟨c11,r10⟩ ⟨c12,r11⟩ := by
    refine detStep_of (by change (2147495024#32).getLsbD 0 = false;decide) he2147495024 fun o => ?_
    have haddr : c11.get 2+0x00000154#32 = 2164255588#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255588#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60260) (width := 4) hm (by decide) (by decide)
    have hval : c11.get 25 = c.get 25 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255588#32) o (by decide) hmem]
    rfl
  have s12 : DetStep B img ⟨c12,r11⟩ ⟨c13,r12⟩ := by
    refine detStep_of (by change (2147495028#32).getLsbD 0 = false;decide) he2147495028 fun o => ?_
    have haddr : c12.get 2+0x00000150#32 = 2164255584#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255584#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60256) (width := 4) hm (by decide) (by decide)
    have hval : c12.get 26 = c.get 26 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255584#32) o (by decide) hmem]
    rfl
  have s13 : DetStep B img ⟨c13,r12⟩ ⟨c14,r13⟩ := by
    refine detStep_of (by change (2147495032#32).getLsbD 0 = false;decide) he2147495032 fun o => ?_
    have haddr : c13.get 2+0x0000014c#32 = 2164255580#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255580#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60252) (width := 4) hm (by decide) (by decide)
    have hval : c13.get 27 = c.get 27 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255580#32) o (by decide) hmem]
    rfl
  have s14 : DetStep B img ⟨c14,r13⟩ ⟨c15,r13⟩ := by
    refine detStep_of (by change (2147495036#32).getLsbD 0 = false;decide) he2147495036 fun o => ?_
    have haddr : c14.get 13+0x00000000#32 = 2164258912#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164258912#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 63584) (width := 4) hm (by decide) (by decide)
    have hread : ramRead r13 2164258912#32 .w = 1024#32 := by
      calc
        _ = ramRead ram 2164258912#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,ramWrite,ramPut]
        _ = _ := hmax
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164258912#32) o (by decide) hmem,hread]
    rfl
  have s15 : DetStep B img ⟨c15,r13⟩ ⟨c16,r13⟩ := by
    refine detStep_of (by change (2147495040#32).getLsbD 0 = false;decide) he2147495040 fun o => ?_
    have ha : c15.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hb : c15.get 12 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_op,ha,hb]
    simp only [alu]
    rw [show (0#32)+(0#32) = 0#32 by decide +kernel]
    rfl
  have s16 : DetStep B img ⟨c16,r13⟩ ⟨c17,r13⟩ := by
    refine detStep_of (by change (2147495042#32).getLsbD 0 = false;decide) he2147495042 fun o => ?_
    have ha : c16.get 12 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hb : c16.get 16 = 1024#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_branch,ha,hb]
    have ht : taken .ltu (0#32) (1024#32) = true := by decide +kernel
    rw [ht]
    simp only [ite_true]
    change interp B img o (jump c16 (2147495042#32+0x00000006#32)) r13 0 [] = _
    rw [show 2147495042#32+0x00000006#32 = 2147495048#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  have s17 : DetStep B img ⟨c17,r13⟩ ⟨c18,r13⟩ := by
    refine detStep_of (by change (2147495048#32).getLsbD 0 = false;decide) he2147495048 fun o => ?_
    have ha : c17.get 14 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hb : c17.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_branch,ha,hb]
    have ht : taken .eq (0#32) (0#32) = true := by decide +kernel
    rw [ht]
    simp only [ite_true]
    change interp B img o (jump c17 (2147495048#32+0x0000005e#32)) r13 0 [] = _
    rw [show 2147495048#32+0x0000005e#32 = 2147495142#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  have s18 : DetStep B img ⟨c18,r13⟩ ⟨c19,r13⟩ := by
    refine detStep_of (by change (2147495142#32).getLsbD 0 = false;decide) he2147495142 fun o => ?_
    have ha : c18.get 12 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hb : c18.get 16 = 1024#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_branch,ha,hb]
    have ht : taken .geu (0#32) (1024#32) = false := by decide +kernel
    rw [ht]
    rfl
  have s19 : DetStep B img ⟨c19,r13⟩ ⟨c20,r13⟩ := by
    refine detStep_of (by change (2147495146#32).getLsbD 0 = false;decide) he2147495146 fun o => ?_
    have ha : c19.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0#32)+(0x00000003#32) = 3#32 by decide +kernel]
    rfl
  have s20 : DetStep B img ⟨c20,r13⟩ ⟨c21,r14⟩ := by
    refine detStep_of (by change (2147495148#32).getLsbD 0 = false;decide) he2147495148 fun o => ?_
    have haddr : c20.get 10+0x00000000#32 = 2164260152#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164260152#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 64824) (width := 4) hm (by decide) (by decide)
    have hval : c20.get 11 = 3#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164260152#32) o (by decide) hmem]
    rfl
  have s21 : DetStep B img ⟨c21,r14⟩ ⟨c22,r15⟩ := by
    refine detStep_of (by change (2147495150#32).getLsbD 0 = false;decide) he2147495150 fun o => ?_
    have haddr : c21.get 10+0x00000004#32 = 2164260156#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164260156#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 64828) (width := 4) hm (by decide) (by decide)
    have hval : c21.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164260156#32) o (by decide) hmem]
    rfl
  have s22 : DetStep B img ⟨c22,r15⟩ ⟨c23,r15⟩ := by
    refine detStep_of (by change (2147495154#32).getLsbD 0 = false;decide) he2147495154 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c22 (2147495154#32+0x00000078#32)) r15 0 [] = _
    rw [show 2147495154#32+0x00000078#32 = 2147495274#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  have s23 : DetStep B img ⟨c23,r15⟩ ⟨c24,r15⟩ := by
    refine detStep_of (by change (2147495274#32).getLsbD 0 = false;decide) he2147495274 fun o => ?_
    have haddr : c23.get 2+0x0000017c#32 = 2164255628#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255628#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60300) (width := 4) hm (by decide) (by decide)
    have hread : ramRead r15 2164255628#32 .w = 2147486246#32 := by
      calc
        _ = ramRead (ramWrite ram 2164255628#32 (2147486246#32) .w) 2164255628#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,ramWrite,ramPut]
        _ = _ := ramRead_ramWrite_w _ _ _
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164255628#32) o (by decide) hmem,hread]
    rfl
  have s24 : DetStep B img ⟨c24,r15⟩ ⟨c25,r15⟩ := by
    refine detStep_of (by change (2147495278#32).getLsbD 0 = false;decide) he2147495278 fun o => ?_
    have haddr : c24.get 2+0x00000178#32 = 2164255624#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255624#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60296) (width := 4) hm (by decide) (by decide)
    have hread : ramRead r15 2164255624#32 .w = c.get 8 := by
      calc
        _ = ramRead (ramWrite ram 2164255624#32 (c.get 8) .w) 2164255624#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,ramWrite,ramPut]
        _ = _ := ramRead_ramWrite_w _ _ _
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164255624#32) o (by decide) hmem,hread]
    rfl
  have s25 : DetStep B img ⟨c25,r15⟩ ⟨c26,r15⟩ := by
    refine detStep_of (by change (2147495282#32).getLsbD 0 = false;decide) he2147495282 fun o => ?_
    have haddr : c25.get 2+0x00000174#32 = 2164255620#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255620#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60292) (width := 4) hm (by decide) (by decide)
    have hread : ramRead r15 2164255620#32 .w = c.get 9 := by
      calc
        _ = ramRead (ramWrite ram 2164255620#32 (c.get 9) .w) 2164255620#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,ramWrite,ramPut]
        _ = _ := ramRead_ramWrite_w _ _ _
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164255620#32) o (by decide) hmem,hread]
    rfl
  have s26 : DetStep B img ⟨c26,r15⟩ ⟨c27,r15⟩ := by
    refine detStep_of (by change (2147495286#32).getLsbD 0 = false;decide) he2147495286 fun o => ?_
    have haddr : c26.get 2+0x00000170#32 = 2164255616#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255616#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60288) (width := 4) hm (by decide) (by decide)
    have hread : ramRead r15 2164255616#32 .w = c.get 18 := by
      calc
        _ = ramRead (ramWrite ram 2164255616#32 (c.get 18) .w) 2164255616#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,ramWrite,ramPut]
        _ = _ := ramRead_ramWrite_w _ _ _
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164255616#32) o (by decide) hmem,hread]
    rfl
  have s27 : DetStep B img ⟨c27,r15⟩ ⟨c28,r15⟩ := by
    refine detStep_of (by change (2147495290#32).getLsbD 0 = false;decide) he2147495290 fun o => ?_
    have haddr : c27.get 2+0x0000016c#32 = 2164255612#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255612#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60284) (width := 4) hm (by decide) (by decide)
    have hread : ramRead r15 2164255612#32 .w = c.get 19 := by
      calc
        _ = ramRead (ramWrite ram 2164255612#32 (c.get 19) .w) 2164255612#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,ramWrite,ramPut]
        _ = _ := ramRead_ramWrite_w _ _ _
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164255612#32) o (by decide) hmem,hread]
    rfl
  have s28 : DetStep B img ⟨c28,r15⟩ ⟨c29,r15⟩ := by
    refine detStep_of (by change (2147495294#32).getLsbD 0 = false;decide) he2147495294 fun o => ?_
    have haddr : c28.get 2+0x00000168#32 = 2164255608#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255608#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60280) (width := 4) hm (by decide) (by decide)
    have hread : ramRead r15 2164255608#32 .w = c.get 20 := by
      calc
        _ = ramRead (ramWrite ram 2164255608#32 (c.get 20) .w) 2164255608#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,ramWrite,ramPut]
        _ = _ := ramRead_ramWrite_w _ _ _
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164255608#32) o (by decide) hmem,hread]
    rfl
  have s29 : DetStep B img ⟨c29,r15⟩ ⟨c30,r15⟩ := by
    refine detStep_of (by change (2147495298#32).getLsbD 0 = false;decide) he2147495298 fun o => ?_
    have haddr : c29.get 2+0x00000164#32 = 2164255604#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255604#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60276) (width := 4) hm (by decide) (by decide)
    have hread : ramRead r15 2164255604#32 .w = c.get 21 := by
      calc
        _ = ramRead (ramWrite ram 2164255604#32 (c.get 21) .w) 2164255604#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,ramWrite,ramPut]
        _ = _ := ramRead_ramWrite_w _ _ _
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164255604#32) o (by decide) hmem,hread]
    rfl
  have s30 : DetStep B img ⟨c30,r15⟩ ⟨c31,r15⟩ := by
    refine detStep_of (by change (2147495302#32).getLsbD 0 = false;decide) he2147495302 fun o => ?_
    have haddr : c30.get 2+0x00000160#32 = 2164255600#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255600#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60272) (width := 4) hm (by decide) (by decide)
    have hread : ramRead r15 2164255600#32 .w = c.get 22 := by
      calc
        _ = ramRead (ramWrite ram 2164255600#32 (c.get 22) .w) 2164255600#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,ramWrite,ramPut]
        _ = _ := ramRead_ramWrite_w _ _ _
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164255600#32) o (by decide) hmem,hread]
    rfl
  have s31 : DetStep B img ⟨c31,r15⟩ ⟨c32,r15⟩ := by
    refine detStep_of (by change (2147495306#32).getLsbD 0 = false;decide) he2147495306 fun o => ?_
    have haddr : c31.get 2+0x0000015c#32 = 2164255596#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255596#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60268) (width := 4) hm (by decide) (by decide)
    have hread : ramRead r15 2164255596#32 .w = c.get 23 := by
      calc
        _ = ramRead (ramWrite ram 2164255596#32 (c.get 23) .w) 2164255596#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,ramWrite,ramPut]
        _ = _ := ramRead_ramWrite_w _ _ _
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164255596#32) o (by decide) hmem,hread]
    rfl
  have s32 : DetStep B img ⟨c32,r15⟩ ⟨c33,r15⟩ := by
    refine detStep_of (by change (2147495310#32).getLsbD 0 = false;decide) he2147495310 fun o => ?_
    have haddr : c32.get 2+0x00000158#32 = 2164255592#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255592#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60264) (width := 4) hm (by decide) (by decide)
    have hread : ramRead r15 2164255592#32 .w = c.get 24 := by
      calc
        _ = ramRead (ramWrite ram 2164255592#32 (c.get 24) .w) 2164255592#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,ramWrite,ramPut]
        _ = _ := ramRead_ramWrite_w _ _ _
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164255592#32) o (by decide) hmem,hread]
    rfl
  have s33 : DetStep B img ⟨c33,r15⟩ ⟨c34,r15⟩ := by
    refine detStep_of (by change (2147495314#32).getLsbD 0 = false;decide) he2147495314 fun o => ?_
    have haddr : c33.get 2+0x00000154#32 = 2164255588#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255588#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60260) (width := 4) hm (by decide) (by decide)
    have hread : ramRead r15 2164255588#32 .w = c.get 25 := by
      calc
        _ = ramRead (ramWrite ram 2164255588#32 (c.get 25) .w) 2164255588#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,ramWrite,ramPut]
        _ = _ := ramRead_ramWrite_w _ _ _
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164255588#32) o (by decide) hmem,hread]
    rfl
  have s34 : DetStep B img ⟨c34,r15⟩ ⟨c35,r15⟩ := by
    refine detStep_of (by change (2147495318#32).getLsbD 0 = false;decide) he2147495318 fun o => ?_
    have haddr : c34.get 2+0x00000150#32 = 2164255584#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255584#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60256) (width := 4) hm (by decide) (by decide)
    have hread : ramRead r15 2164255584#32 .w = c.get 26 := by
      calc
        _ = ramRead (ramWrite ram 2164255584#32 (c.get 26) .w) 2164255584#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,ramWrite,ramPut]
        _ = _ := ramRead_ramWrite_w _ _ _
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164255584#32) o (by decide) hmem,hread]
    rfl
  have s35 : DetStep B img ⟨c35,r15⟩ ⟨c36,r15⟩ := by
    refine detStep_of (by change (2147495322#32).getLsbD 0 = false;decide) he2147495322 fun o => ?_
    have haddr : c35.get 2+0x0000014c#32 = 2164255580#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    have hmem : B.inRam (2164255580#32) 4 = true := Memory.block_access (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60252) (width := 4) hm (by decide) (by decide)
    have hread : ramRead r15 2164255580#32 .w = c.get 27 := by
      calc
        _ = ramRead (ramWrite ram 2164255580#32 (c.get 27) .w) 2164255580#32 .w := by
          apply ramRead_w_congr
          intro k hk
          have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          rcases hc with h|h|h|h
          all_goals simp [h,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,ramWrite,ramPut]
        _ = _ := ramRead_ramWrite_w _ _ _
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164255580#32) o (by decide) hmem,hread]
    rfl
  have s36 : DetStep B img ⟨c36,r15⟩ ⟨c37,r15⟩ := by
    refine detStep_of (by change (2147495326#32).getLsbD 0 = false;decide) he2147495326 fun o => ?_
    have ha : c36.get 2 = 2164255248#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (2164255248#32)+(0x00000180#32) = 2164255632#32 by decide +kernel]
    rfl
  have s37 : DetStep B img ⟨c37,r15⟩ ⟨c38,r15⟩ := by
    refine detStep_of (by change (2147495328#32).getLsbD 0 = false;decide) he2147495328 fun o => ?_
    have hv : c37.get 1 = 2147486246#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hret,hout,hlen,hmaxptr]
    rw [exec_jalr,hv,BitVec.add_zero]
    rw [show (2147486246#32) &&& ~~~(1 : Word) = 2147486246#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  exact .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.step s13 (.step s14 (.step s15 (.step s16 (.step s17 (.step s18 (.step s19 (.step s20 (.step s21 (.step s22 (.step s23 (.step s24 (.step s25 (.step s26 (.step s27 (.step s28 (.step s29 (.step s30 (.step s31 (.step s32 (.step s33 (.step s34 (.step s35 (.step s36 (.single s37)))))))))))))))))))))))))))))))))))))

def reg (i : Fin 12) : Reg := match i.val with
 | 0 => 8 | 1 => 9 | 2 => 18 | 3 => 19 | 4 => 20 | 5 => 21
 | 6 => 22 | 7 => 23 | 8 => 24 | 9 => 25 | 10 => 26 | _ => 27

theorem saved (c : Core) (ram : Word → BitVec 8) :
    ∀ i : Fin 12, (execute c ram).core.get (reg i) = c.get (reg i) := by
  intro i
  have hi := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨
    i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 := by omega
  rcases hc with h|h|h|h|h|h|h|h|h|h|h|h
  all_goals simp [h,reg,execute,Core.wr_get,Core.wr_get_ne]

theorem fields (c : Core) (ram : Word → BitVec 8) :
    (execute c ram).core.pc = 0x80000a26#32 ∧ (execute c ram).core.get 2 = 0x80ffeb90#32 ∧
    (execute c ram).core.get 12 = c.get 12 ∧ (execute c ram).core.sameCsr c :=
  ⟨rfl,rfl,rfl,by rfl⟩

/-- Actual Rust parse-head ABI for zero input and the default1024 limit:
    the Incomplete tag is3 and its consumed/auxiliary word is0. -/
theorem incomplete (c : Core) (ram : Word → BitVec 8) :
    ramRead (memory c ram) 0x80fffd38#32 .w = 3#32 ∧ ramRead (memory c ram) 0x80fffd3c#32 .w = 0#32 := by
  constructor <;> simp [memory,ramRead,ramWrite,ramPut,byteOf]

theorem frame (c : Core) (ram : Word → BitVec 8) (x : Word)
    (hs : ∀ i : Fin 384, x ≠ 0x80ffea10#32+BitVec.ofNat 32 i.val)
    (ho : ∀ i : Fin 8, x ≠ 0x80fffd38#32+BitVec.ofNat 32 i.val) : memory c ram x = ram x := by
  unfold memory
  rw [Init.write_frame _ 2164260156#32 _ x .w (by
    intro j
    have hj := j.isLt
    simp only [Width.bytes] at hj
    have ha : 2164260156#32+BitVec.ofNat 32 j.val = 2164260152#32+BitVec.ofNat 32 (4+j.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [ha]
    exact ho ⟨4+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164260152#32 _ x .w (by
    intro j
    have hj := j.isLt
    simp only [Width.bytes] at hj
    have ha : 2164260152#32+BitVec.ofNat 32 j.val = 2164260152#32+BitVec.ofNat 32 (0+j.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [ha]
    exact ho ⟨0+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164255580#32 _ x .w (by
    intro j
    have hj := j.isLt
    simp only [Width.bytes] at hj
    have ha : 2164255580#32+BitVec.ofNat 32 j.val = 2164255248#32+BitVec.ofNat 32 (332+j.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [ha]
    exact hs ⟨332+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164255584#32 _ x .w (by
    intro j
    have hj := j.isLt
    simp only [Width.bytes] at hj
    have ha : 2164255584#32+BitVec.ofNat 32 j.val = 2164255248#32+BitVec.ofNat 32 (336+j.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [ha]
    exact hs ⟨336+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164255588#32 _ x .w (by
    intro j
    have hj := j.isLt
    simp only [Width.bytes] at hj
    have ha : 2164255588#32+BitVec.ofNat 32 j.val = 2164255248#32+BitVec.ofNat 32 (340+j.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [ha]
    exact hs ⟨340+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164255592#32 _ x .w (by
    intro j
    have hj := j.isLt
    simp only [Width.bytes] at hj
    have ha : 2164255592#32+BitVec.ofNat 32 j.val = 2164255248#32+BitVec.ofNat 32 (344+j.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [ha]
    exact hs ⟨344+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164255596#32 _ x .w (by
    intro j
    have hj := j.isLt
    simp only [Width.bytes] at hj
    have ha : 2164255596#32+BitVec.ofNat 32 j.val = 2164255248#32+BitVec.ofNat 32 (348+j.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [ha]
    exact hs ⟨348+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164255600#32 _ x .w (by
    intro j
    have hj := j.isLt
    simp only [Width.bytes] at hj
    have ha : 2164255600#32+BitVec.ofNat 32 j.val = 2164255248#32+BitVec.ofNat 32 (352+j.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [ha]
    exact hs ⟨352+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164255604#32 _ x .w (by
    intro j
    have hj := j.isLt
    simp only [Width.bytes] at hj
    have ha : 2164255604#32+BitVec.ofNat 32 j.val = 2164255248#32+BitVec.ofNat 32 (356+j.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [ha]
    exact hs ⟨356+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164255608#32 _ x .w (by
    intro j
    have hj := j.isLt
    simp only [Width.bytes] at hj
    have ha : 2164255608#32+BitVec.ofNat 32 j.val = 2164255248#32+BitVec.ofNat 32 (360+j.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [ha]
    exact hs ⟨360+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164255612#32 _ x .w (by
    intro j
    have hj := j.isLt
    simp only [Width.bytes] at hj
    have ha : 2164255612#32+BitVec.ofNat 32 j.val = 2164255248#32+BitVec.ofNat 32 (364+j.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [ha]
    exact hs ⟨364+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164255616#32 _ x .w (by
    intro j
    have hj := j.isLt
    simp only [Width.bytes] at hj
    have ha : 2164255616#32+BitVec.ofNat 32 j.val = 2164255248#32+BitVec.ofNat 32 (368+j.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [ha]
    exact hs ⟨368+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164255620#32 _ x .w (by
    intro j
    have hj := j.isLt
    simp only [Width.bytes] at hj
    have ha : 2164255620#32+BitVec.ofNat 32 j.val = 2164255248#32+BitVec.ofNat 32 (372+j.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [ha]
    exact hs ⟨372+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164255624#32 _ x .w (by
    intro j
    have hj := j.isLt
    simp only [Width.bytes] at hj
    have ha : 2164255624#32+BitVec.ofNat 32 j.val = 2164255248#32+BitVec.ofNat 32 (376+j.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [ha]
    exact hs ⟨376+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164255628#32 _ x .w (by
    intro j
    have hj := j.isLt
    simp only [Width.bytes] at hj
    have ha : 2164255628#32+BitVec.ofNat 32 j.val = 2164255248#32+BitVec.ofNat 32 (380+j.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [ha]
    exact hs ⟨380+j.val,by omega⟩)]

end E5R.Thermostat.HeadEmpty
