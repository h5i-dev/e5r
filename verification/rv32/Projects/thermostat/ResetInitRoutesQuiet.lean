-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.InitRoutes
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.InitRoutes
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 2147485912#32) (hsp : c.get 2 = 0x80ffeb90#32)
    (h12 : c.get 12 = 2048#32) (hm : Memory.Block B 0x80ffeb90#32 5232) :
    Quiet.Steps B img 36 ⟨c,ram⟩ (execute c ram) := by
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
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact li2147485912) fun o => ?_
    rw [exec_lui,hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (2147485916#32).getLsbD 0 = false;decide) li2147485916 fun o => ?_
    have ha : c1.get 10 = 2147508224#32 := by simp [c1,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (2147508224#32)+(0xfffffb9c#32) = 2147507100#32 by decide +kernel]
    rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (2147485920#32).getLsbD 0 = false;decide) li2147485920 fun o => ?_
    have ha : c2.get 0 = 0#32 := by simp [c1,c2,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0#32)+(0x0000000a#32) = 10#32 by decide +kernel]
    rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (2147485922#32).getLsbD 0 = false;decide) li2147485922 fun o => ?_
    rw [exec_lui]
    rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (2147485926#32).getLsbD 0 = false;decide) li2147485926 fun o => ?_
    have ha : c4.get 13 = 2147508224#32 := by simp [c1,c2,c3,c4,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (2147508224#32)+(0xfffffb97#32) = 2147507095#32 by decide +kernel]
    rfl
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (2147485930#32).getLsbD 0 = false;decide) li2147485930 fun o => ?_
    have ha : c5.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0#32)+(0x00000005#32) = 5#32 by decide +kernel]
    rfl
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,r1⟩ := by
    refine QuietDet.step_of (by change (2147485932#32).getLsbD 0 = false;decide) li2147485932 fun o => ?_
    have haddr : c6.get 2+0x00000048#32 = 2164255704#32 := by simp [c1,c2,c3,c4,c5,c6,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255704#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 72) (width := 4) hm (by decide) (by decide)
    have hval : c6.get 10 = 2147507100#32 := by simp [c1,c2,c3,c4,c5,c6,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255704#32) o (by decide) hmem]
    rfl
  have s7 : Quiet.Step B img ⟨c7,r1⟩ ⟨c8,r2⟩ := by
    refine QuietDet.step_of (by change (2147485934#32).getLsbD 0 = false;decide) li2147485934 fun o => ?_
    have haddr : c7.get 2+0x0000004c#32 = 2164255708#32 := by simp [c1,c2,c3,c4,c5,c6,c7,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255708#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 76) (width := 4) hm (by decide) (by decide)
    have hval : c7.get 11 = 10#32 := by simp [c1,c2,c3,c4,c5,c6,c7,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255708#32) o (by decide) hmem]
    rfl
  have s8 : Quiet.Step B img ⟨c8,r2⟩ ⟨c9,r3⟩ := by
    refine QuietDet.step_of (by change (2147485936#32).getLsbD 0 = false;decide) li2147485936 fun o => ?_
    have haddr : c8.get 2+0x00000050#32 = 2164255712#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255712#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 80) (width := 4) hm (by decide) (by decide)
    have hval : c8.get 13 = 2147507095#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255712#32) o (by decide) hmem]
    rfl
  have s9 : Quiet.Step B img ⟨c9,r3⟩ ⟨c10,r4⟩ := by
    refine QuietDet.step_of (by change (2147485938#32).getLsbD 0 = false;decide) li2147485938 fun o => ?_
    have haddr : c9.get 2+0x00000054#32 = 2164255716#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255716#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 84) (width := 4) hm (by decide) (by decide)
    have hval : c9.get 14 = 5#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255716#32) o (by decide) hmem]
    rfl
  have s10 : Quiet.Step B img ⟨c10,r4⟩ ⟨c11,r4⟩ := by
    refine QuietDet.step_of (by change (2147485940#32).getLsbD 0 = false;decide) li2147485940 fun o => ?_
    rw [exec_lui]
    rfl
  have s11 : Quiet.Step B img ⟨c11,r4⟩ ⟨c12,r4⟩ := by
    refine QuietDet.step_of (by change (2147485944#32).getLsbD 0 = false;decide) li2147485944 fun o => ?_
    have ha : c11.get 10 = 2147508224#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (2147508224#32)+(0xfffffb92#32) = 2147507090#32 by decide +kernel]
    rfl
  have s12 : Quiet.Step B img ⟨c12,r4⟩ ⟨c13,r4⟩ := by
    refine QuietDet.step_of (by change (2147485948#32).getLsbD 0 = false;decide) li2147485948 fun o => ?_
    rw [exec_lui]
    rfl
  have s13 : Quiet.Step B img ⟨c13,r4⟩ ⟨c14,r4⟩ := by
    refine QuietDet.step_of (by change (2147485952#32).getLsbD 0 = false;decide) li2147485952 fun o => ?_
    have ha : c13.get 11 = 2147508224#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (2147508224#32)+(0xfffffb89#32) = 2147507081#32 by decide +kernel]
    rfl
  have s14 : Quiet.Step B img ⟨c14,r4⟩ ⟨c15,r4⟩ := by
    refine QuietDet.step_of (by change (2147485956#32).getLsbD 0 = false;decide) li2147485956 fun o => ?_
    have ha : c14.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0#32)+(0x00000009#32) = 9#32 by decide +kernel]
    rfl
  have s15 : Quiet.Step B img ⟨c15,r4⟩ ⟨c16,r5⟩ := by
    refine QuietDet.step_of (by change (2147485958#32).getLsbD 0 = false;decide) li2147485958 fun o => ?_
    have haddr : c15.get 2+0x00000058#32 = 2164255720#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255720#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 88) (width := 4) hm (by decide) (by decide)
    have hval : c15.get 10 = 2147507090#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255720#32) o (by decide) hmem]
    rfl
  have s16 : Quiet.Step B img ⟨c16,r5⟩ ⟨c17,r6⟩ := by
    refine QuietDet.step_of (by change (2147485960#32).getLsbD 0 = false;decide) li2147485960 fun o => ?_
    have haddr : c16.get 2+0x0000005c#32 = 2164255724#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255724#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 92) (width := 4) hm (by decide) (by decide)
    have hval : c16.get 14 = 5#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255724#32) o (by decide) hmem]
    rfl
  have s17 : Quiet.Step B img ⟨c17,r6⟩ ⟨c18,r7⟩ := by
    refine QuietDet.step_of (by change (2147485962#32).getLsbD 0 = false;decide) li2147485962 fun o => ?_
    have haddr : c17.get 2+0x00000060#32 = 2164255728#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255728#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 96) (width := 4) hm (by decide) (by decide)
    have hval : c17.get 11 = 2147507081#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255728#32) o (by decide) hmem]
    rfl
  have s18 : Quiet.Step B img ⟨c18,r7⟩ ⟨c19,r8⟩ := by
    refine QuietDet.step_of (by change (2147485964#32).getLsbD 0 = false;decide) li2147485964 fun o => ?_
    have haddr : c18.get 2+0x00000064#32 = 2164255732#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255732#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 100) (width := 4) hm (by decide) (by decide)
    have hval : c18.get 13 = 9#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255732#32) o (by decide) hmem]
    rfl
  have s19 : Quiet.Step B img ⟨c19,r8⟩ ⟨c20,r8⟩ := by
    refine QuietDet.step_of (by change (2147485966#32).getLsbD 0 = false;decide) li2147485966 fun o => ?_
    rw [exec_lui]
    rfl
  have s20 : Quiet.Step B img ⟨c20,r8⟩ ⟨c21,r8⟩ := by
    refine QuietDet.step_of (by change (2147485970#32).getLsbD 0 = false;decide) li2147485970 fun o => ?_
    have ha : c20.get 10 = 2147508224#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (2147508224#32)+(0xfffffb83#32) = 2147507075#32 by decide +kernel]
    rfl
  have s21 : Quiet.Step B img ⟨c21,r8⟩ ⟨c22,r8⟩ := by
    refine QuietDet.step_of (by change (2147485974#32).getLsbD 0 = false;decide) li2147485974 fun o => ?_
    have ha : c21.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0#32)+(0x00000006#32) = 6#32 by decide +kernel]
    rfl
  have s22 : Quiet.Step B img ⟨c22,r8⟩ ⟨c23,r8⟩ := by
    refine QuietDet.step_of (by change (2147485976#32).getLsbD 0 = false;decide) li2147485976 fun o => ?_
    have ha : c22.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0#32)+(0x00000003#32) = 3#32 by decide +kernel]
    rfl
  have s23 : Quiet.Step B img ⟨c23,r8⟩ ⟨c24,r8⟩ := by
    refine QuietDet.step_of (by change (2147485978#32).getLsbD 0 = false;decide) li2147485978 fun o => ?_
    have ha : c23.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0#32)+(0x00000002#32) = 2#32 by decide +kernel]
    rfl
  have s24 : Quiet.Step B img ⟨c24,r8⟩ ⟨c25,r9⟩ := by
    refine QuietDet.step_of (by change (2147485980#32).getLsbD 0 = false;decide) li2147485980 fun o => ?_
    have haddr : c24.get 2+0x00000068#32 = 2164255736#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255736#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 104) (width := 4) hm (by decide) (by decide)
    have hval : c24.get 10 = 2147507075#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255736#32) o (by decide) hmem]
    rfl
  have s25 : Quiet.Step B img ⟨c25,r9⟩ ⟨c26,r10⟩ := by
    refine QuietDet.step_of (by change (2147485982#32).getLsbD 0 = false;decide) li2147485982 fun o => ?_
    have haddr : c25.get 2+0x0000006c#32 = 2164255740#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255740#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 108) (width := 4) hm (by decide) (by decide)
    have hval : c25.get 11 = 6#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255740#32) o (by decide) hmem]
    rfl
  have s26 : Quiet.Step B img ⟨c26,r10⟩ ⟨c27,r11⟩ := by
    refine QuietDet.step_of (by change (2147485984#32).getLsbD 0 = false;decide) li2147485984 fun o => ?_
    have haddr : c26.get 2+0x00000070#32 = 2164255744#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255744#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 112) (width := 1) hm (by decide) (by decide)
    have hval : c26.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164255744#32) o (by decide) hmem]
    rfl
  have s27 : Quiet.Step B img ⟨c27,r11⟩ ⟨c28,r12⟩ := by
    refine QuietDet.step_of (by change (2147485988#32).getLsbD 0 = false;decide) li2147485988 fun o => ?_
    have haddr : c27.get 2+0x00000074#32 = 2164255748#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255748#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 116) (width := 1) hm (by decide) (by decide)
    have hval : c27.get 26 = 3#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164255748#32) o (by decide) hmem]
    rfl
  have s28 : Quiet.Step B img ⟨c28,r12⟩ ⟨c29,r13⟩ := by
    refine QuietDet.step_of (by change (2147485992#32).getLsbD 0 = false;decide) li2147485992 fun o => ?_
    have haddr : c28.get 2+0x00000078#32 = 2164255752#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255752#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 120) (width := 1) hm (by decide) (by decide)
    have hval : c28.get 18 = 2#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164255752#32) o (by decide) hmem]
    rfl
  have s29 : Quiet.Step B img ⟨c29,r13⟩ ⟨c30,r14⟩ := by
    refine QuietDet.step_of (by change (2147485996#32).getLsbD 0 = false;decide) li2147485996 fun o => ?_
    have haddr : c29.get 2+0x0000007c#32 = 2164255756#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255756#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 124) (width := 1) hm (by decide) (by decide)
    have hval : c29.get 26 = 3#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164255756#32) o (by decide) hmem]
    rfl
  have s30 : Quiet.Step B img ⟨c30,r14⟩ ⟨c31,r15⟩ := by
    refine QuietDet.step_of (by change (2147486000#32).getLsbD 0 = false;decide) li2147486000 fun o => ?_
    have haddr : c30.get 2+0x00000080#32 = 2164255760#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255760#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 128) (width := 1) hm (by decide) (by decide)
    have hval : c30.get 26 = 3#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164255760#32) o (by decide) hmem]
    rfl
  have s31 : Quiet.Step B img ⟨c31,r15⟩ ⟨c32,r15⟩ := by
    refine QuietDet.step_of (by change (2147486004#32).getLsbD 0 = false;decide) li2147486004 fun o => ?_
    have ha : c31.get 2 = 0x80ffeb90#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0x80ffeb90#32)+(0x00000084#32) = 2164255764#32 by decide +kernel]
    rfl
  have s32 : Quiet.Step B img ⟨c32,r15⟩ ⟨c33,r15⟩ := by
    refine QuietDet.step_of (by change (2147486006#32).getLsbD 0 = false;decide) li2147486006 fun o => ?_
    have ha : c32.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0#32)+(0x00000000#32) = 0#32 by decide +kernel]
    rfl
  have s33 : Quiet.Step B img ⟨c33,r15⟩ ⟨c34,r16⟩ := by
    refine QuietDet.step_of (by change (2147486008#32).getLsbD 0 = false;decide) li2147486008 fun o => ?_
    have haddr : c33.get 2+0x00000010#32 = 2164255648#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    have hmem : B.inRam (2164255648#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 16) (width := 4) hm (by decide) (by decide)
    have hval : c33.get 12 = 2048#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255648#32) o (by decide) hmem]
    rfl
  have s34 : Quiet.Step B img ⟨c34,r16⟩ ⟨c35,r16⟩ := by
    refine QuietDet.step_of (by change (2147486010#32).getLsbD 0 = false;decide) li2147486010 fun o => ?_
    rw [exec_auipc]
    change interp B img o (.done (c34.wr 1 (2147486010#32+0x00005000#32) 2147486014#32)) r16 0 [] = _
    rw [show 2147486010#32+0x00005000#32 = 2147506490#32 by decide +kernel]
    rfl
  have s35 : Quiet.Step B img ⟨c35,r16⟩ ⟨c36,r16⟩ := by
    refine QuietDet.step_of (by change (2147486014#32).getLsbD 0 = false;decide) li2147486014 fun o => ?_
    have hv : c35.get 1 = 2147506490#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,h12]
    rw [exec_jalr,hv]
    rfl
  exact .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.step s13 (.step s14 (.step s15 (.step s16 (.step s17 (.step s18 (.step s19 (.step s20 (.step s21 (.step s22 (.step s23 (.step s24 (.step s25 (.step s26 (.step s27 (.step s28 (.step s29 (.step s30 (.step s31 (.step s32 (.step s33 (.step s34 (.single s35)))))))))))))))))))))))))))))))))))

end E5R.Thermostat.InitRoutes
