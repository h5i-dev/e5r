import Projects.thermostat.LoopInitCode
import Projects.thermostat.Memory
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.InitRoutes
open E5R E5R.Thermostat

def execute (c : Core) (ram : Word → BitVec 8) : Machine :=
  let c1 := c.wr 10 2147508224#32 2147485916#32
  let c2 := c1.wr 10 2147507100#32 2147485920#32
  let c3 := c2.wr 11 10#32 2147485922#32
  let c4 := c3.wr 13 2147508224#32 2147485926#32
  let c5 := c4.wr 13 2147507095#32 2147485930#32
  let c6 := c5.wr 14 5#32 2147485932#32
  let r1 := ramWrite ram 2164255704#32 (2147507100#32) .w
  let c7 := c6.goto 2147485934#32
  let r2 := ramWrite r1 2164255708#32 (10#32) .w
  let c8 := c7.goto 2147485936#32
  let r3 := ramWrite r2 2164255712#32 (2147507095#32) .w
  let c9 := c8.goto 2147485938#32
  let r4 := ramWrite r3 2164255716#32 (5#32) .w
  let c10 := c9.goto 2147485940#32
  let c11 := c10.wr 10 2147508224#32 2147485944#32
  let c12 := c11.wr 10 2147507090#32 2147485948#32
  let c13 := c12.wr 11 2147508224#32 2147485952#32
  let c14 := c13.wr 11 2147507081#32 2147485956#32
  let c15 := c14.wr 13 9#32 2147485958#32
  let r5 := ramWrite r4 2164255720#32 (2147507090#32) .w
  let c16 := c15.goto 2147485960#32
  let r6 := ramWrite r5 2164255724#32 (5#32) .w
  let c17 := c16.goto 2147485962#32
  let r7 := ramWrite r6 2164255728#32 (2147507081#32) .w
  let c18 := c17.goto 2147485964#32
  let r8 := ramWrite r7 2164255732#32 (9#32) .w
  let c19 := c18.goto 2147485966#32
  let c20 := c19.wr 10 2147508224#32 2147485970#32
  let c21 := c20.wr 10 2147507075#32 2147485974#32
  let c22 := c21.wr 11 6#32 2147485976#32
  let c23 := c22.wr 26 3#32 2147485978#32
  let c24 := c23.wr 18 2#32 2147485980#32
  let r9 := ramWrite r8 2164255736#32 (2147507075#32) .w
  let c25 := c24.goto 2147485982#32
  let r10 := ramWrite r9 2164255740#32 (6#32) .w
  let c26 := c25.goto 2147485984#32
  let r11 := ramWrite r10 2164255744#32 (0#32) .b
  let c27 := c26.goto 2147485988#32
  let r12 := ramWrite r11 2164255748#32 (3#32) .b
  let c28 := c27.goto 2147485992#32
  let r13 := ramWrite r12 2164255752#32 (2#32) .b
  let c29 := c28.goto 2147485996#32
  let r14 := ramWrite r13 2164255756#32 (3#32) .b
  let c30 := c29.goto 2147486000#32
  let r15 := ramWrite r14 2164255760#32 (3#32) .b
  let c31 := c30.goto 2147486004#32
  let c32 := c31.wr 10 2164255764#32 2147486006#32
  let c33 := c32.wr 11 0#32 2147486008#32
  let r16 := ramWrite r15 2164255648#32 (2048#32) .w
  let c34 := c33.goto 2147486010#32
  let c35 := c34.wr 1 2147506490#32 2147486014#32
  let c36 := c35.wr 1 2147486018#32 2147505720#32
  ⟨c36,r16⟩

def memory (ram : Word → BitVec 8) : Word → BitVec 8 :=
  let r1 := ramWrite ram 2164255704#32 (2147507100#32) .w
  let r2 := ramWrite r1 2164255708#32 (10#32) .w
  let r3 := ramWrite r2 2164255712#32 (2147507095#32) .w
  let r4 := ramWrite r3 2164255716#32 (5#32) .w
  let r5 := ramWrite r4 2164255720#32 (2147507090#32) .w
  let r6 := ramWrite r5 2164255724#32 (5#32) .w
  let r7 := ramWrite r6 2164255728#32 (2147507081#32) .w
  let r8 := ramWrite r7 2164255732#32 (9#32) .w
  let r9 := ramWrite r8 2164255736#32 (2147507075#32) .w
  let r10 := ramWrite r9 2164255740#32 (6#32) .w
  let r11 := ramWrite r10 2164255744#32 (0#32) .b
  let r12 := ramWrite r11 2164255748#32 (3#32) .b
  let r13 := ramWrite r12 2164255752#32 (2#32) .b
  let r14 := ramWrite r13 2164255756#32 (3#32) .b
  let r15 := ramWrite r14 2164255760#32 (3#32) .b
  let r16 := ramWrite r15 2164255648#32 (2048#32) .w
  r16

theorem execute_ram (c : Core) (ram : Word → BitVec 8) : (execute c ram).ram = memory ram := rfl

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 2147485912#32) (hsp : c.get 2 = 0x80ffeb90#32)
    (h12 : c.get 12 = 2048#32) (hm : Memory.Block B 0x80ffeb90#32 5232) :
    DetSteps B img 36 ⟨c,ram⟩ (execute c ram) := by
  let c1 := c.wr 10 2147508224#32 2147485916#32
  let c2 := c1.wr 10 2147507100#32 2147485920#32
  let c3 := c2.wr 11 10#32 2147485922#32
  let c4 := c3.wr 13 2147508224#32 2147485926#32
  let c5 := c4.wr 13 2147507095#32 2147485930#32
  let c6 := c5.wr 14 5#32 2147485932#32
  let r1 := ramWrite ram 2164255704#32 (2147507100#32) .w
  let c7 := c6.goto 2147485934#32
  let r2 := ramWrite r1 2164255708#32 (10#32) .w
  let c8 := c7.goto 2147485936#32
  let r3 := ramWrite r2 2164255712#32 (2147507095#32) .w
  let c9 := c8.goto 2147485938#32
  let r4 := ramWrite r3 2164255716#32 (5#32) .w
  let c10 := c9.goto 2147485940#32
  let c11 := c10.wr 10 2147508224#32 2147485944#32
  let c12 := c11.wr 10 2147507090#32 2147485948#32
  let c13 := c12.wr 11 2147508224#32 2147485952#32
  let c14 := c13.wr 11 2147507081#32 2147485956#32
  let c15 := c14.wr 13 9#32 2147485958#32
  let r5 := ramWrite r4 2164255720#32 (2147507090#32) .w
  let c16 := c15.goto 2147485960#32
  let r6 := ramWrite r5 2164255724#32 (5#32) .w
  let c17 := c16.goto 2147485962#32
  let r7 := ramWrite r6 2164255728#32 (2147507081#32) .w
  let c18 := c17.goto 2147485964#32
  let r8 := ramWrite r7 2164255732#32 (9#32) .w
  let c19 := c18.goto 2147485966#32
  let c20 := c19.wr 10 2147508224#32 2147485970#32
  let c21 := c20.wr 10 2147507075#32 2147485974#32
  let c22 := c21.wr 11 6#32 2147485976#32
  let c23 := c22.wr 26 3#32 2147485978#32
  let c24 := c23.wr 18 2#32 2147485980#32
  let r9 := ramWrite r8 2164255736#32 (2147507075#32) .w
  let c25 := c24.goto 2147485982#32
  let r10 := ramWrite r9 2164255740#32 (6#32) .w
  let c26 := c25.goto 2147485984#32
  let r11 := ramWrite r10 2164255744#32 (0#32) .b
  let c27 := c26.goto 2147485988#32
  let r12 := ramWrite r11 2164255748#32 (3#32) .b
  let c28 := c27.goto 2147485992#32
  let r13 := ramWrite r12 2164255752#32 (2#32) .b
  let c29 := c28.goto 2147485996#32
  let r14 := ramWrite r13 2164255756#32 (3#32) .b
  let c30 := c29.goto 2147486000#32
  let r15 := ramWrite r14 2164255760#32 (3#32) .b
  let c31 := c30.goto 2147486004#32
  let c32 := c31.wr 10 2164255764#32 2147486006#32
  let c33 := c32.wr 11 0#32 2147486008#32
  let r16 := ramWrite r15 2164255648#32 (2048#32) .w
  let c34 := c33.goto 2147486010#32
  let c35 := c34.wr 1 2147506490#32 2147486014#32
  let c36 := c35.wr 1 2147486018#32 2147505720#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact li2147485912) fun o => ?_
    rw [exec_lui,hp]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (2147485916#32).getLsbD 0 = false;decide) li2147485916 fun o => ?_
    have ha : c1.get 10 = 2147508224#32 := by simp [c1,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (2147508224#32)+(0xfffffb9c#32) = 2147507100#32 by decide +kernel]
    rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (2147485920#32).getLsbD 0 = false;decide) li2147485920 fun o => ?_
    have ha : c2.get 0 = 0#32 := by simp [c1,c2,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0#32)+(0x0000000a#32) = 10#32 by decide +kernel]
    rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (2147485922#32).getLsbD 0 = false;decide) li2147485922 fun o => ?_
    rw [exec_lui]
    rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (2147485926#32).getLsbD 0 = false;decide) li2147485926 fun o => ?_
    have ha : c4.get 13 = 2147508224#32 := by simp [c1,c2,c3,c4,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (2147508224#32)+(0xfffffb97#32) = 2147507095#32 by decide +kernel]
    rfl
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (2147485930#32).getLsbD 0 = false;decide) li2147485930 fun o => ?_
    have ha : c5.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0#32)+(0x00000005#32) = 5#32 by decide +kernel]
    rfl
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,r1⟩ := by
    refine detStep_of (by change (2147485932#32).getLsbD 0 = false;decide) li2147485932 fun o => ?_
    have haddr : c6.get 2+0x00000048#32 = 2164255704#32 := by simp [c1,c2,c3,c4,c5,c6,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255704#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 72) (width := 4) hm (by decide) (by decide)
    have hval : c6.get 10 = 2147507100#32 := by simp [c1,c2,c3,c4,c5,c6,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255704#32) o (by decide) hmem]
    rfl
  have s7 : DetStep B img ⟨c7,r1⟩ ⟨c8,r2⟩ := by
    refine detStep_of (by change (2147485934#32).getLsbD 0 = false;decide) li2147485934 fun o => ?_
    have haddr : c7.get 2+0x0000004c#32 = 2164255708#32 := by simp [c1,c2,c3,c4,c5,c6,c7,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255708#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 76) (width := 4) hm (by decide) (by decide)
    have hval : c7.get 11 = 10#32 := by simp [c1,c2,c3,c4,c5,c6,c7,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255708#32) o (by decide) hmem]
    rfl
  have s8 : DetStep B img ⟨c8,r2⟩ ⟨c9,r3⟩ := by
    refine detStep_of (by change (2147485936#32).getLsbD 0 = false;decide) li2147485936 fun o => ?_
    have haddr : c8.get 2+0x00000050#32 = 2164255712#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255712#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 80) (width := 4) hm (by decide) (by decide)
    have hval : c8.get 13 = 2147507095#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255712#32) o (by decide) hmem]
    rfl
  have s9 : DetStep B img ⟨c9,r3⟩ ⟨c10,r4⟩ := by
    refine detStep_of (by change (2147485938#32).getLsbD 0 = false;decide) li2147485938 fun o => ?_
    have haddr : c9.get 2+0x00000054#32 = 2164255716#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255716#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 84) (width := 4) hm (by decide) (by decide)
    have hval : c9.get 14 = 5#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255716#32) o (by decide) hmem]
    rfl
  have s10 : DetStep B img ⟨c10,r4⟩ ⟨c11,r4⟩ := by
    refine detStep_of (by change (2147485940#32).getLsbD 0 = false;decide) li2147485940 fun o => ?_
    rw [exec_lui]
    rfl
  have s11 : DetStep B img ⟨c11,r4⟩ ⟨c12,r4⟩ := by
    refine detStep_of (by change (2147485944#32).getLsbD 0 = false;decide) li2147485944 fun o => ?_
    have ha : c11.get 10 = 2147508224#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (2147508224#32)+(0xfffffb92#32) = 2147507090#32 by decide +kernel]
    rfl
  have s12 : DetStep B img ⟨c12,r4⟩ ⟨c13,r4⟩ := by
    refine detStep_of (by change (2147485948#32).getLsbD 0 = false;decide) li2147485948 fun o => ?_
    rw [exec_lui]
    rfl
  have s13 : DetStep B img ⟨c13,r4⟩ ⟨c14,r4⟩ := by
    refine detStep_of (by change (2147485952#32).getLsbD 0 = false;decide) li2147485952 fun o => ?_
    have ha : c13.get 11 = 2147508224#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (2147508224#32)+(0xfffffb89#32) = 2147507081#32 by decide +kernel]
    rfl
  have s14 : DetStep B img ⟨c14,r4⟩ ⟨c15,r4⟩ := by
    refine detStep_of (by change (2147485956#32).getLsbD 0 = false;decide) li2147485956 fun o => ?_
    have ha : c14.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0#32)+(0x00000009#32) = 9#32 by decide +kernel]
    rfl
  have s15 : DetStep B img ⟨c15,r4⟩ ⟨c16,r5⟩ := by
    refine detStep_of (by change (2147485958#32).getLsbD 0 = false;decide) li2147485958 fun o => ?_
    have haddr : c15.get 2+0x00000058#32 = 2164255720#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255720#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 88) (width := 4) hm (by decide) (by decide)
    have hval : c15.get 10 = 2147507090#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255720#32) o (by decide) hmem]
    rfl
  have s16 : DetStep B img ⟨c16,r5⟩ ⟨c17,r6⟩ := by
    refine detStep_of (by change (2147485960#32).getLsbD 0 = false;decide) li2147485960 fun o => ?_
    have haddr : c16.get 2+0x0000005c#32 = 2164255724#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255724#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 92) (width := 4) hm (by decide) (by decide)
    have hval : c16.get 14 = 5#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255724#32) o (by decide) hmem]
    rfl
  have s17 : DetStep B img ⟨c17,r6⟩ ⟨c18,r7⟩ := by
    refine detStep_of (by change (2147485962#32).getLsbD 0 = false;decide) li2147485962 fun o => ?_
    have haddr : c17.get 2+0x00000060#32 = 2164255728#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255728#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 96) (width := 4) hm (by decide) (by decide)
    have hval : c17.get 11 = 2147507081#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255728#32) o (by decide) hmem]
    rfl
  have s18 : DetStep B img ⟨c18,r7⟩ ⟨c19,r8⟩ := by
    refine detStep_of (by change (2147485964#32).getLsbD 0 = false;decide) li2147485964 fun o => ?_
    have haddr : c18.get 2+0x00000064#32 = 2164255732#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255732#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 100) (width := 4) hm (by decide) (by decide)
    have hval : c18.get 13 = 9#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255732#32) o (by decide) hmem]
    rfl
  have s19 : DetStep B img ⟨c19,r8⟩ ⟨c20,r8⟩ := by
    refine detStep_of (by change (2147485966#32).getLsbD 0 = false;decide) li2147485966 fun o => ?_
    rw [exec_lui]
    rfl
  have s20 : DetStep B img ⟨c20,r8⟩ ⟨c21,r8⟩ := by
    refine detStep_of (by change (2147485970#32).getLsbD 0 = false;decide) li2147485970 fun o => ?_
    have ha : c20.get 10 = 2147508224#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (2147508224#32)+(0xfffffb83#32) = 2147507075#32 by decide +kernel]
    rfl
  have s21 : DetStep B img ⟨c21,r8⟩ ⟨c22,r8⟩ := by
    refine detStep_of (by change (2147485974#32).getLsbD 0 = false;decide) li2147485974 fun o => ?_
    have ha : c21.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0#32)+(0x00000006#32) = 6#32 by decide +kernel]
    rfl
  have s22 : DetStep B img ⟨c22,r8⟩ ⟨c23,r8⟩ := by
    refine detStep_of (by change (2147485976#32).getLsbD 0 = false;decide) li2147485976 fun o => ?_
    have ha : c22.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0#32)+(0x00000003#32) = 3#32 by decide +kernel]
    rfl
  have s23 : DetStep B img ⟨c23,r8⟩ ⟨c24,r8⟩ := by
    refine detStep_of (by change (2147485978#32).getLsbD 0 = false;decide) li2147485978 fun o => ?_
    have ha : c23.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0#32)+(0x00000002#32) = 2#32 by decide +kernel]
    rfl
  have s24 : DetStep B img ⟨c24,r8⟩ ⟨c25,r9⟩ := by
    refine detStep_of (by change (2147485980#32).getLsbD 0 = false;decide) li2147485980 fun o => ?_
    have haddr : c24.get 2+0x00000068#32 = 2164255736#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255736#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 104) (width := 4) hm (by decide) (by decide)
    have hval : c24.get 10 = 2147507075#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255736#32) o (by decide) hmem]
    rfl
  have s25 : DetStep B img ⟨c25,r9⟩ ⟨c26,r10⟩ := by
    refine detStep_of (by change (2147485982#32).getLsbD 0 = false;decide) li2147485982 fun o => ?_
    have haddr : c25.get 2+0x0000006c#32 = 2164255740#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255740#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 108) (width := 4) hm (by decide) (by decide)
    have hval : c25.get 11 = 6#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255740#32) o (by decide) hmem]
    rfl
  have s26 : DetStep B img ⟨c26,r10⟩ ⟨c27,r11⟩ := by
    refine detStep_of (by change (2147485984#32).getLsbD 0 = false;decide) li2147485984 fun o => ?_
    have haddr : c26.get 2+0x00000070#32 = 2164255744#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255744#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 112) (width := 1) hm (by decide) (by decide)
    have hval : c26.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164255744#32) o (by decide) hmem]
    rfl
  have s27 : DetStep B img ⟨c27,r11⟩ ⟨c28,r12⟩ := by
    refine detStep_of (by change (2147485988#32).getLsbD 0 = false;decide) li2147485988 fun o => ?_
    have haddr : c27.get 2+0x00000074#32 = 2164255748#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255748#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 116) (width := 1) hm (by decide) (by decide)
    have hval : c27.get 26 = 3#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164255748#32) o (by decide) hmem]
    rfl
  have s28 : DetStep B img ⟨c28,r12⟩ ⟨c29,r13⟩ := by
    refine detStep_of (by change (2147485992#32).getLsbD 0 = false;decide) li2147485992 fun o => ?_
    have haddr : c28.get 2+0x00000078#32 = 2164255752#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255752#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 120) (width := 1) hm (by decide) (by decide)
    have hval : c28.get 18 = 2#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164255752#32) o (by decide) hmem]
    rfl
  have s29 : DetStep B img ⟨c29,r13⟩ ⟨c30,r14⟩ := by
    refine detStep_of (by change (2147485996#32).getLsbD 0 = false;decide) li2147485996 fun o => ?_
    have haddr : c29.get 2+0x0000007c#32 = 2164255756#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255756#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 124) (width := 1) hm (by decide) (by decide)
    have hval : c29.get 26 = 3#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164255756#32) o (by decide) hmem]
    rfl
  have s30 : DetStep B img ⟨c30,r14⟩ ⟨c31,r15⟩ := by
    refine detStep_of (by change (2147486000#32).getLsbD 0 = false;decide) li2147486000 fun o => ?_
    have haddr : c30.get 2+0x00000080#32 = 2164255760#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255760#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 128) (width := 1) hm (by decide) (by decide)
    have hval : c30.get 26 = 3#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164255760#32) o (by decide) hmem]
    rfl
  have s31 : DetStep B img ⟨c31,r15⟩ ⟨c32,r15⟩ := by
    refine detStep_of (by change (2147486004#32).getLsbD 0 = false;decide) li2147486004 fun o => ?_
    have ha : c31.get 2 = 0x80ffeb90#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0x80ffeb90#32)+(0x00000084#32) = 2164255764#32 by decide +kernel]
    rfl
  have s32 : DetStep B img ⟨c32,r15⟩ ⟨c33,r15⟩ := by
    refine detStep_of (by change (2147486006#32).getLsbD 0 = false;decide) li2147486006 fun o => ?_
    have ha : c32.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0#32)+(0x00000000#32) = 0#32 by decide +kernel]
    rfl
  have s33 : DetStep B img ⟨c33,r15⟩ ⟨c34,r16⟩ := by
    refine detStep_of (by change (2147486008#32).getLsbD 0 = false;decide) li2147486008 fun o => ?_
    have haddr : c33.get 2+0x00000010#32 = 2164255648#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255648#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 16) (width := 4) hm (by decide) (by decide)
    have hval : c33.get 12 = 2048#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255648#32) o (by decide) hmem]
    rfl
  have s34 : DetStep B img ⟨c34,r16⟩ ⟨c35,r16⟩ := by
    refine detStep_of (by change (2147486010#32).getLsbD 0 = false;decide) li2147486010 fun o => ?_
    rw [exec_auipc]
    change interp B img o (.done (c34.wr 1 (2147486010#32+0x00005000#32) 2147486014#32)) r16 0 [] = _
    rw [show 2147486010#32+0x00005000#32 = 2147506490#32 by decide +kernel]
    rfl
  have s35 : DetStep B img ⟨c35,r16⟩ ⟨c36,r16⟩ := by
    refine detStep_of (by change (2147486014#32).getLsbD 0 = false;decide) li2147486014 fun o => ?_
    have hv : c35.get 1 = 2147506490#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_jalr,hv]
    rfl
  exact .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.step s13 (.step s14 (.step s15 (.step s16 (.step s17 (.step s18 (.step s19 (.step s20 (.step s21 (.step s22 (.step s23 (.step s24 (.step s25 (.step s26 (.step s27 (.step s28 (.step s29 (.step s30 (.step s31 (.step s32 (.step s33 (.step s34 (.single s35)))))))))))))))))))))))))))))))))))
theorem fields (c : Core) (ram : Word → BitVec 8) :
    (execute c ram).core.pc = 0x80005638#32 ∧
    (execute c ram).core.get 1 = 2147486018#32 ∧
    (execute c ram).core.get 10 = 2164255764#32 ∧
    (execute c ram).core.get 11 = 0#32 ∧
    (execute c ram).core.get 12 = c.get 12 ∧
    (execute c ram).core.get 2 = c.get 2 ∧
    (execute c ram).core.get 8 = c.get 8 ∧
    (execute c ram).core.get 19 = c.get 19 ∧
    (execute c ram).core.get 22 = c.get 22 ∧
    (execute c ram).core.sameCsr c :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,by rfl⟩

/-- Raw Rust route storage; path and method slots are not zipped here. -/
def Layout (ram : Word → BitVec 8) : Prop :=
  (∀ i : Fin 5,
    ramRead ram (0x80ffebd8#32+BitVec.ofNat 32 (8*i.val)) .w =
      (match i.val with | 0 => 0x80005b9c#32 | 1 => 0x80005b97#32 | 2 => 0x80005b92#32 | 3 => 0x80005b89#32 | _ => 0x80005b83#32) ∧
    ramRead ram (0x80ffebdc#32+BitVec.ofNat 32 (8*i.val)) .w =
      (match i.val with | 0 => 10#32 | 1 => 5#32 | 2 => 5#32 | 3 => 9#32 | _ => 6#32) ∧
    ram (0x80ffec00#32+BitVec.ofNat 32 (4*i.val)) =
      (match i.val with | 0 => 0#8 | 1 => 3#8 | 2 => 2#8 | _ => 3#8)) ∧
  ramRead ram 0x80ffeba0#32 .w = 2048#32

theorem layout (ram : Word → BitVec 8) : Layout (memory ram) := by
  constructor
  · intro i
    have hi := i.isLt
    have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by omega
    rcases hc with h|h|h|h|h
    all_goals simp [h,memory,ramRead,ramWrite,ramPut,byteOf]
  · simp [memory,ramRead,ramWrite,ramPut,byteOf]

theorem frame (ram : Word → BitVec 8) (x : Word)
    (hr : ∀ i : Fin 60, x ≠ 0x80ffebd8#32+BitVec.ofNat 32 i.val)
    (hl : ∀ i : Fin 4, x ≠ 0x80ffeba0#32+BitVec.ofNat 32 i.val) : memory ram x = ram x := by
  have hr0 : x ≠ 2164255704#32 := hr ⟨0,by decide⟩
  have hr1 : x ≠ 2164255705#32 := hr ⟨1,by decide⟩
  have hr2 : x ≠ 2164255706#32 := hr ⟨2,by decide⟩
  have hr3 : x ≠ 2164255707#32 := hr ⟨3,by decide⟩
  have hr4 : x ≠ 2164255708#32 := hr ⟨4,by decide⟩
  have hr5 : x ≠ 2164255709#32 := hr ⟨5,by decide⟩
  have hr6 : x ≠ 2164255710#32 := hr ⟨6,by decide⟩
  have hr7 : x ≠ 2164255711#32 := hr ⟨7,by decide⟩
  have hr8 : x ≠ 2164255712#32 := hr ⟨8,by decide⟩
  have hr9 : x ≠ 2164255713#32 := hr ⟨9,by decide⟩
  have hr10 : x ≠ 2164255714#32 := hr ⟨10,by decide⟩
  have hr11 : x ≠ 2164255715#32 := hr ⟨11,by decide⟩
  have hr12 : x ≠ 2164255716#32 := hr ⟨12,by decide⟩
  have hr13 : x ≠ 2164255717#32 := hr ⟨13,by decide⟩
  have hr14 : x ≠ 2164255718#32 := hr ⟨14,by decide⟩
  have hr15 : x ≠ 2164255719#32 := hr ⟨15,by decide⟩
  have hr16 : x ≠ 2164255720#32 := hr ⟨16,by decide⟩
  have hr17 : x ≠ 2164255721#32 := hr ⟨17,by decide⟩
  have hr18 : x ≠ 2164255722#32 := hr ⟨18,by decide⟩
  have hr19 : x ≠ 2164255723#32 := hr ⟨19,by decide⟩
  have hr20 : x ≠ 2164255724#32 := hr ⟨20,by decide⟩
  have hr21 : x ≠ 2164255725#32 := hr ⟨21,by decide⟩
  have hr22 : x ≠ 2164255726#32 := hr ⟨22,by decide⟩
  have hr23 : x ≠ 2164255727#32 := hr ⟨23,by decide⟩
  have hr24 : x ≠ 2164255728#32 := hr ⟨24,by decide⟩
  have hr25 : x ≠ 2164255729#32 := hr ⟨25,by decide⟩
  have hr26 : x ≠ 2164255730#32 := hr ⟨26,by decide⟩
  have hr27 : x ≠ 2164255731#32 := hr ⟨27,by decide⟩
  have hr28 : x ≠ 2164255732#32 := hr ⟨28,by decide⟩
  have hr29 : x ≠ 2164255733#32 := hr ⟨29,by decide⟩
  have hr30 : x ≠ 2164255734#32 := hr ⟨30,by decide⟩
  have hr31 : x ≠ 2164255735#32 := hr ⟨31,by decide⟩
  have hr32 : x ≠ 2164255736#32 := hr ⟨32,by decide⟩
  have hr33 : x ≠ 2164255737#32 := hr ⟨33,by decide⟩
  have hr34 : x ≠ 2164255738#32 := hr ⟨34,by decide⟩
  have hr35 : x ≠ 2164255739#32 := hr ⟨35,by decide⟩
  have hr36 : x ≠ 2164255740#32 := hr ⟨36,by decide⟩
  have hr37 : x ≠ 2164255741#32 := hr ⟨37,by decide⟩
  have hr38 : x ≠ 2164255742#32 := hr ⟨38,by decide⟩
  have hr39 : x ≠ 2164255743#32 := hr ⟨39,by decide⟩
  have hr40 : x ≠ 2164255744#32 := hr ⟨40,by decide⟩
  have hr41 : x ≠ 2164255745#32 := hr ⟨41,by decide⟩
  have hr42 : x ≠ 2164255746#32 := hr ⟨42,by decide⟩
  have hr43 : x ≠ 2164255747#32 := hr ⟨43,by decide⟩
  have hr44 : x ≠ 2164255748#32 := hr ⟨44,by decide⟩
  have hr45 : x ≠ 2164255749#32 := hr ⟨45,by decide⟩
  have hr46 : x ≠ 2164255750#32 := hr ⟨46,by decide⟩
  have hr47 : x ≠ 2164255751#32 := hr ⟨47,by decide⟩
  have hr48 : x ≠ 2164255752#32 := hr ⟨48,by decide⟩
  have hr49 : x ≠ 2164255753#32 := hr ⟨49,by decide⟩
  have hr50 : x ≠ 2164255754#32 := hr ⟨50,by decide⟩
  have hr51 : x ≠ 2164255755#32 := hr ⟨51,by decide⟩
  have hr52 : x ≠ 2164255756#32 := hr ⟨52,by decide⟩
  have hr53 : x ≠ 2164255757#32 := hr ⟨53,by decide⟩
  have hr54 : x ≠ 2164255758#32 := hr ⟨54,by decide⟩
  have hr55 : x ≠ 2164255759#32 := hr ⟨55,by decide⟩
  have hr56 : x ≠ 2164255760#32 := hr ⟨56,by decide⟩
  have hr57 : x ≠ 2164255761#32 := hr ⟨57,by decide⟩
  have hr58 : x ≠ 2164255762#32 := hr ⟨58,by decide⟩
  have hr59 : x ≠ 2164255763#32 := hr ⟨59,by decide⟩
  have hl0 : x ≠ 2164255648#32 := hl ⟨0,by decide⟩
  have hl1 : x ≠ 2164255649#32 := hl ⟨1,by decide⟩
  have hl2 : x ≠ 2164255650#32 := hl ⟨2,by decide⟩
  have hl3 : x ≠ 2164255651#32 := hl ⟨3,by decide⟩
  simp [memory,ramWrite,ramPut,hr0,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8,hr9,hr10,hr11,hr12,hr13,hr14,hr15,hr16,hr17,hr18,hr19,hr20,hr21,hr22,hr23,hr24,hr25,hr26,hr27,hr28,hr29,hr30,hr31,hr32,hr33,hr34,hr35,hr36,hr37,hr38,hr39,hr40,hr41,hr42,hr43,hr44,hr45,hr46,hr47,hr48,hr49,hr50,hr51,hr52,hr53,hr54,hr55,hr56,hr57,hr58,hr59,hl0,hl1,hl2,hl3]


theorem layout_preserve (ram ram' : Word → BitVec 8) (h : Layout ram)
    (hf : ∀ i : Fin 60, ram' (0x80ffebd8#32+BitVec.ofNat 32 i.val) = ram (0x80ffebd8#32+BitVec.ofNat 32 i.val))
    (hl : ∀ i : Fin 4, ram' (0x80ffeba0#32+BitVec.ofNat 32 i.val) = ram (0x80ffeba0#32+BitVec.ofNat 32 i.val)) :
    Layout ram' := by
  have hw (off : Nat) (ho : off+4 ≤ 60) :
      ramRead ram' (0x80ffebd8#32+BitVec.ofNat 32 off) .w = ramRead ram (0x80ffebd8#32+BitVec.ofNat 32 off) .w := by
    apply ramRead_w_congr
    intro k hk
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hf ⟨off+k,by omega⟩
  constructor
  · intro i
    have hi := i.isLt
    obtain ⟨hp,hln,ht⟩ := h.1 i
    refine ⟨(hw (8*i.val) (by omega)).trans hp,?_,?_⟩
    · have hh := hw (4+8*i.val) (by omega)
      have ha : 0x80ffebd8#32+BitVec.ofNat 32 (4+8*i.val) = 0x80ffebdc#32+BitVec.ofNat 32 (8*i.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha] at hh
      exact hh.trans hln
    · have hh := hf ⟨40+4*i.val,by omega⟩
      have ha : 0x80ffebd8#32+BitVec.ofNat 32 (40+4*i.val) = 0x80ffec00#32+BitVec.ofNat 32 (4*i.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha] at hh
      exact hh.trans ht
  · have hh : ramRead ram' 0x80ffeba0#32 .w = ramRead ram 0x80ffeba0#32 .w := by
      apply ramRead_w_congr
      intro k hk
      exact hl ⟨k,hk⟩
    exact hh.trans h.2

end E5R.Thermostat.InitRoutes
