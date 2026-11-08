-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ReadMarshal
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.ReadMarshal
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80001a7e#32) (hsp : c.get 2 = 0x80ffeb90#32)
    (hfp : c.get 8 = 0x80fff814#32) (hstate : c.get 25 = 0x80ffebc0#32)
    (h10 : c.get 10 = 2#32) (hm : Memory.Block B 0x80ffeb40#32 5312) :
    Quiet.Steps B img 42 ⟨c,ram⟩ (execute c ram) := by
  let c1 := c.wr 11 4096#32 2147490432#32
  let c2 := c1.wr 11 4521#32 2147490436#32
  let c3 := c2.wr 6 2164260153#32 2147490440#32
  let v3 := extend .b false (ramRead ram 2164260161#32 .b)
  let c4 := c3.wr 11 v3 2147490444#32
  let v4 := extend .b false (ramRead ram 2164260157#32 .b)
  let c5 := c4.wr 12 v4 2147490448#32
  let v5 := extend .b false (ramRead ram 2164260158#32 .b)
  let c6 := c5.wr 13 v5 2147490452#32
  let v6 := extend .b false (ramRead ram 2164260159#32 .b)
  let c7 := c6.wr 14 v6 2147490456#32
  let v7 := extend .b false (ramRead ram 2164260160#32 .b)
  let c8 := c7.wr 15 v7 2147490460#32
  let v8 := extend .b false (ramRead ram 2164260153#32 .b)
  let c9 := c8.wr 16 v8 2147490464#32
  let v9 := extend .b false (ramRead ram 2164260154#32 .b)
  let c10 := c9.wr 17 v9 2147490468#32
  let v10 := extend .b false (ramRead ram 2164260155#32 .b)
  let c11 := c10.wr 5 v10 2147490472#32
  let v11 := extend .b false (ramRead ram 2164260156#32 .b)
  let c12 := c11.wr 6 v11 2147490476#32
  let c13 := c12.wr 7 4096#32 2147490478#32
  let c14 := c13.wr 7 4905#32 2147490482#32
  let c15 := c14.wr 7 2164260537#32 2147490484#32
  let r1 := ramWrite ram 2164260545#32 (v3) .b
  let c16 := c15.goto 2147490488#32
  let v16 := extend .b false (ramRead r1 2164260163#32 .b)
  let c17 := c16.wr 11 v16 2147490492#32
  let r2 := ramWrite r1 2164255640#32 (v16) .w
  let c18 := c17.goto 2147490494#32
  let v18 := extend .h false (ramRead r2 2164260164#32 .h)
  let c19 := c18.wr 11 v18 2147490498#32
  let r3 := ramWrite r2 2164255652#32 (v18) .w
  let c20 := c19.goto 2147490500#32
  let v20 := extend .h false (ramRead r3 2164260166#32 .h)
  let c21 := c20.wr 11 v20 2147490504#32
  let r4 := ramWrite r3 2164255644#32 (v20) .w
  let c22 := c21.goto 2147490506#32
  let v22 := extend .h false (ramRead r4 2164260168#32 .h)
  let c23 := c22.wr 27 v22 2147490510#32
  let v23 := extend .h false (ramRead r4 2164260170#32 .h)
  let c24 := c23.wr 21 v23 2147490514#32
  let r5 := ramWrite r4 2164260541#32 (v4) .b
  let c25 := c24.goto 2147490518#32
  let r6 := ramWrite r5 2164260542#32 (v5) .b
  let c26 := c25.goto 2147490522#32
  let r7 := ramWrite r6 2164260543#32 (v6) .b
  let c27 := c26.goto 2147490526#32
  let r8 := ramWrite r7 2164260544#32 (v7) .b
  let c28 := c27.goto 2147490530#32
  let r9 := ramWrite r8 2164260537#32 (v8) .b
  let c29 := c28.goto 2147490534#32
  let r10 := ramWrite r9 2164260538#32 (v9) .b
  let c30 := c29.goto 2147490538#32
  let r11 := ramWrite r10 2164260539#32 (v10) .b
  let c31 := c30.goto 2147490542#32
  let r12 := ramWrite r11 2164260540#32 (v11) .b
  let c32 := c31.goto 2147490546#32
  let r13 := ramWrite r12 2164260536#32 (2#32) .b
  let c33 := c32.goto 2147490550#32
  let c34 := c33.wr 10 4096#32 2147490552#32
  let c35 := c34.wr 10 4520#32 2147490556#32
  let c36 := c35.wr 10 2164260152#32 2147490558#32
  let c37 := c36.wr 11 4096#32 2147490560#32
  let c38 := c37.wr 11 4904#32 2147490564#32
  let c39 := c38.wr 12 2164260536#32 2147490568#32
  let c40 := c39.wr 11 2164255680#32 2147490570#32
  let c41 := c40.wr 1 2147490570#32 2147490574#32
  let c42 := c41.wr 1 2147490578#32 2147491384#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact re2147490430) fun o => ?_
    rw [exec_lui,hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (2147490432#32).getLsbD 0 = false;decide) re2147490432 fun o => ?_
    have ha : c1.get 11 = 4096#32 := by simp [c1,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (4096#32)+(0x000001a9#32) = 4521#32 by decide +kernel]
    rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (2147490436#32).getLsbD 0 = false;decide) re2147490436 fun o => ?_
    have ha : c2.get 2 = 0x80ffeb90#32 := by simp [c1,c2,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hb : c2.get 11 = 4521#32 := by simp [c1,c2,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_op,ha,hb]
    simp only [alu]
    rw [show (0x80ffeb90#32)+(4521#32) = 2164260153#32 by decide +kernel]
    rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (2147490440#32).getLsbD 0 = false;decide) re2147490440 fun o => ?_
    have haddr : c3.get 6+0x00000008#32 = 2164260161#32 := by simp [c1,c2,c3,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260161#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4609) (width := 1) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .b) (a := 2164260161#32) o (by decide) hmem]
    rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (2147490444#32).getLsbD 0 = false;decide) re2147490444 fun o => ?_
    have haddr : c4.get 6+0x00000004#32 = 2164260157#32 := by simp [c1,c2,c3,c4,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260157#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4605) (width := 1) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .b) (a := 2164260157#32) o (by decide) hmem]
    rfl
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (2147490448#32).getLsbD 0 = false;decide) re2147490448 fun o => ?_
    have haddr : c5.get 6+0x00000005#32 = 2164260158#32 := by simp [c1,c2,c3,c4,c5,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260158#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4606) (width := 1) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .b) (a := 2164260158#32) o (by decide) hmem]
    rfl
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (2147490452#32).getLsbD 0 = false;decide) re2147490452 fun o => ?_
    have haddr : c6.get 6+0x00000006#32 = 2164260159#32 := by simp [c1,c2,c3,c4,c5,c6,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260159#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4607) (width := 1) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .b) (a := 2164260159#32) o (by decide) hmem]
    rfl
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (2147490456#32).getLsbD 0 = false;decide) re2147490456 fun o => ?_
    have haddr : c7.get 6+0x00000007#32 = 2164260160#32 := by simp [c1,c2,c3,c4,c5,c6,c7,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260160#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4608) (width := 1) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .b) (a := 2164260160#32) o (by decide) hmem]
    rfl
  have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine QuietDet.step_of (by change (2147490460#32).getLsbD 0 = false;decide) re2147490460 fun o => ?_
    have haddr : c8.get 6+0x00000000#32 = 2164260153#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260153#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4601) (width := 1) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .b) (a := 2164260153#32) o (by decide) hmem]
    rfl
  have s9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine QuietDet.step_of (by change (2147490464#32).getLsbD 0 = false;decide) re2147490464 fun o => ?_
    have haddr : c9.get 6+0x00000001#32 = 2164260154#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260154#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4602) (width := 1) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .b) (a := 2164260154#32) o (by decide) hmem]
    rfl
  have s10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine QuietDet.step_of (by change (2147490468#32).getLsbD 0 = false;decide) re2147490468 fun o => ?_
    have haddr : c10.get 6+0x00000002#32 = 2164260155#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260155#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4603) (width := 1) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .b) (a := 2164260155#32) o (by decide) hmem]
    rfl
  have s11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine QuietDet.step_of (by change (2147490472#32).getLsbD 0 = false;decide) re2147490472 fun o => ?_
    have haddr : c11.get 6+0x00000003#32 = 2164260156#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260156#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4604) (width := 1) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .b) (a := 2164260156#32) o (by decide) hmem]
    rfl
  have s12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine QuietDet.step_of (by change (2147490476#32).getLsbD 0 = false;decide) re2147490476 fun o => ?_
    rw [exec_lui]
    rfl
  have s13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine QuietDet.step_of (by change (2147490478#32).getLsbD 0 = false;decide) re2147490478 fun o => ?_
    have ha : c13.get 7 = 4096#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (4096#32)+(0x00000329#32) = 4905#32 by decide +kernel]
    rfl
  have s14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine QuietDet.step_of (by change (2147490482#32).getLsbD 0 = false;decide) re2147490482 fun o => ?_
    have ha : c14.get 7 = 4905#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hb : c14.get 2 = 0x80ffeb90#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_op,ha,hb]
    simp only [alu]
    rw [show (4905#32)+(0x80ffeb90#32) = 2164260537#32 by decide +kernel]
    rfl
  have s15 : Quiet.Step B img ⟨c15,ram⟩ ⟨c16,r1⟩ := by
    refine QuietDet.step_of (by change (2147490484#32).getLsbD 0 = false;decide) re2147490484 fun o => ?_
    have haddr : c15.get 7+0x00000008#32 = 2164260545#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260545#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4993) (width := 1) hm (by decide) (by decide)
    have hval : c15.get 11 = v3 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164260545#32) o (by decide) hmem]
    rfl
  have s16 : Quiet.Step B img ⟨c16,r1⟩ ⟨c17,r1⟩ := by
    refine QuietDet.step_of (by change (2147490488#32).getLsbD 0 = false;decide) re2147490488 fun o => ?_
    have haddr : c16.get 8+0x0000052f#32 = 2164260163#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260163#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4611) (width := 1) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .b) (a := 2164260163#32) o (by decide) hmem]
    rfl
  have s17 : Quiet.Step B img ⟨c17,r1⟩ ⟨c18,r2⟩ := by
    refine QuietDet.step_of (by change (2147490492#32).getLsbD 0 = false;decide) re2147490492 fun o => ?_
    have haddr : c17.get 2+0x00000008#32 = 2164255640#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164255640#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 88) (width := 4) hm (by decide) (by decide)
    have hval : c17.get 11 = v16 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255640#32) o (by decide) hmem]
    rfl
  have s18 : Quiet.Step B img ⟨c18,r2⟩ ⟨c19,r2⟩ := by
    refine QuietDet.step_of (by change (2147490494#32).getLsbD 0 = false;decide) re2147490494 fun o => ?_
    have haddr : c18.get 8+0x00000530#32 = 2164260164#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260164#32) 2 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4612) (width := 2) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .h) (a := 2164260164#32) o (by decide) hmem]
    rfl
  have s19 : Quiet.Step B img ⟨c19,r2⟩ ⟨c20,r3⟩ := by
    refine QuietDet.step_of (by change (2147490498#32).getLsbD 0 = false;decide) re2147490498 fun o => ?_
    have haddr : c19.get 2+0x00000014#32 = 2164255652#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164255652#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 100) (width := 4) hm (by decide) (by decide)
    have hval : c19.get 11 = v18 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255652#32) o (by decide) hmem]
    rfl
  have s20 : Quiet.Step B img ⟨c20,r3⟩ ⟨c21,r3⟩ := by
    refine QuietDet.step_of (by change (2147490500#32).getLsbD 0 = false;decide) re2147490500 fun o => ?_
    have haddr : c20.get 8+0x00000532#32 = 2164260166#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260166#32) 2 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4614) (width := 2) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .h) (a := 2164260166#32) o (by decide) hmem]
    rfl
  have s21 : Quiet.Step B img ⟨c21,r3⟩ ⟨c22,r4⟩ := by
    refine QuietDet.step_of (by change (2147490504#32).getLsbD 0 = false;decide) re2147490504 fun o => ?_
    have haddr : c21.get 2+0x0000000c#32 = 2164255644#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164255644#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 92) (width := 4) hm (by decide) (by decide)
    have hval : c21.get 11 = v20 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255644#32) o (by decide) hmem]
    rfl
  have s22 : Quiet.Step B img ⟨c22,r4⟩ ⟨c23,r4⟩ := by
    refine QuietDet.step_of (by change (2147490506#32).getLsbD 0 = false;decide) re2147490506 fun o => ?_
    have haddr : c22.get 8+0x00000534#32 = 2164260168#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260168#32) 2 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4616) (width := 2) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .h) (a := 2164260168#32) o (by decide) hmem]
    rfl
  have s23 : Quiet.Step B img ⟨c23,r4⟩ ⟨c24,r4⟩ := by
    refine QuietDet.step_of (by change (2147490510#32).getLsbD 0 = false;decide) re2147490510 fun o => ?_
    have haddr : c23.get 8+0x00000536#32 = 2164260170#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260170#32) 2 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4618) (width := 2) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .h) (a := 2164260170#32) o (by decide) hmem]
    rfl
  have s24 : Quiet.Step B img ⟨c24,r4⟩ ⟨c25,r5⟩ := by
    refine QuietDet.step_of (by change (2147490514#32).getLsbD 0 = false;decide) re2147490514 fun o => ?_
    have haddr : c24.get 7+0x00000004#32 = 2164260541#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260541#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4989) (width := 1) hm (by decide) (by decide)
    have hval : c24.get 12 = v4 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164260541#32) o (by decide) hmem]
    rfl
  have s25 : Quiet.Step B img ⟨c25,r5⟩ ⟨c26,r6⟩ := by
    refine QuietDet.step_of (by change (2147490518#32).getLsbD 0 = false;decide) re2147490518 fun o => ?_
    have haddr : c25.get 7+0x00000005#32 = 2164260542#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260542#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4990) (width := 1) hm (by decide) (by decide)
    have hval : c25.get 13 = v5 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164260542#32) o (by decide) hmem]
    rfl
  have s26 : Quiet.Step B img ⟨c26,r6⟩ ⟨c27,r7⟩ := by
    refine QuietDet.step_of (by change (2147490522#32).getLsbD 0 = false;decide) re2147490522 fun o => ?_
    have haddr : c26.get 7+0x00000006#32 = 2164260543#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260543#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4991) (width := 1) hm (by decide) (by decide)
    have hval : c26.get 14 = v6 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164260543#32) o (by decide) hmem]
    rfl
  have s27 : Quiet.Step B img ⟨c27,r7⟩ ⟨c28,r8⟩ := by
    refine QuietDet.step_of (by change (2147490526#32).getLsbD 0 = false;decide) re2147490526 fun o => ?_
    have haddr : c27.get 7+0x00000007#32 = 2164260544#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260544#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4992) (width := 1) hm (by decide) (by decide)
    have hval : c27.get 15 = v7 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164260544#32) o (by decide) hmem]
    rfl
  have s28 : Quiet.Step B img ⟨c28,r8⟩ ⟨c29,r9⟩ := by
    refine QuietDet.step_of (by change (2147490530#32).getLsbD 0 = false;decide) re2147490530 fun o => ?_
    have haddr : c28.get 7+0x00000000#32 = 2164260537#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260537#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4985) (width := 1) hm (by decide) (by decide)
    have hval : c28.get 16 = v8 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164260537#32) o (by decide) hmem]
    rfl
  have s29 : Quiet.Step B img ⟨c29,r9⟩ ⟨c30,r10⟩ := by
    refine QuietDet.step_of (by change (2147490534#32).getLsbD 0 = false;decide) re2147490534 fun o => ?_
    have haddr : c29.get 7+0x00000001#32 = 2164260538#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260538#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4986) (width := 1) hm (by decide) (by decide)
    have hval : c29.get 17 = v9 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164260538#32) o (by decide) hmem]
    rfl
  have s30 : Quiet.Step B img ⟨c30,r10⟩ ⟨c31,r11⟩ := by
    refine QuietDet.step_of (by change (2147490538#32).getLsbD 0 = false;decide) re2147490538 fun o => ?_
    have haddr : c30.get 7+0x00000002#32 = 2164260539#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260539#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4987) (width := 1) hm (by decide) (by decide)
    have hval : c30.get 5 = v10 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164260539#32) o (by decide) hmem]
    rfl
  have s31 : Quiet.Step B img ⟨c31,r11⟩ ⟨c32,r12⟩ := by
    refine QuietDet.step_of (by change (2147490542#32).getLsbD 0 = false;decide) re2147490542 fun o => ?_
    have haddr : c31.get 7+0x00000003#32 = 2164260540#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260540#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4988) (width := 1) hm (by decide) (by decide)
    have hval : c31.get 6 = v11 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164260540#32) o (by decide) hmem]
    rfl
  have s32 : Quiet.Step B img ⟨c32,r12⟩ ⟨c33,r13⟩ := by
    refine QuietDet.step_of (by change (2147490546#32).getLsbD 0 = false;decide) re2147490546 fun o => ?_
    have haddr : c32.get 8+0x000006a4#32 = 2164260536#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hmem : B.inRam (2164260536#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4984) (width := 1) hm (by decide) (by decide)
    have hval : c32.get 10 = 2#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164260536#32) o (by decide) hmem]
    rfl
  have s33 : Quiet.Step B img ⟨c33,r13⟩ ⟨c34,r13⟩ := by
    refine QuietDet.step_of (by change (2147490550#32).getLsbD 0 = false;decide) re2147490550 fun o => ?_
    rw [exec_lui]
    rfl
  have s34 : Quiet.Step B img ⟨c34,r13⟩ ⟨c35,r13⟩ := by
    refine QuietDet.step_of (by change (2147490552#32).getLsbD 0 = false;decide) re2147490552 fun o => ?_
    have ha : c34.get 10 = 4096#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (4096#32)+(0x000001a8#32) = 4520#32 by decide +kernel]
    rfl
  have s35 : Quiet.Step B img ⟨c35,r13⟩ ⟨c36,r13⟩ := by
    refine QuietDet.step_of (by change (2147490556#32).getLsbD 0 = false;decide) re2147490556 fun o => ?_
    have ha : c35.get 10 = 4520#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hb : c35.get 2 = 0x80ffeb90#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_op,ha,hb]
    simp only [alu]
    rw [show (4520#32)+(0x80ffeb90#32) = 2164260152#32 by decide +kernel]
    rfl
  have s36 : Quiet.Step B img ⟨c36,r13⟩ ⟨c37,r13⟩ := by
    refine QuietDet.step_of (by change (2147490558#32).getLsbD 0 = false;decide) re2147490558 fun o => ?_
    rw [exec_lui]
    rfl
  have s37 : Quiet.Step B img ⟨c37,r13⟩ ⟨c38,r13⟩ := by
    refine QuietDet.step_of (by change (2147490560#32).getLsbD 0 = false;decide) re2147490560 fun o => ?_
    have ha : c37.get 11 = 4096#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (4096#32)+(0x00000328#32) = 4904#32 by decide +kernel]
    rfl
  have s38 : Quiet.Step B img ⟨c38,r13⟩ ⟨c39,r13⟩ := by
    refine QuietDet.step_of (by change (2147490564#32).getLsbD 0 = false;decide) re2147490564 fun o => ?_
    have ha : c38.get 2 = 0x80ffeb90#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hb : c38.get 11 = 4904#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_op,ha,hb]
    simp only [alu]
    rw [show (0x80ffeb90#32)+(4904#32) = 2164260536#32 by decide +kernel]
    rfl
  have s39 : Quiet.Step B img ⟨c39,r13⟩ ⟨c40,r13⟩ := by
    refine QuietDet.step_of (by change (2147490568#32).getLsbD 0 = false;decide) re2147490568 fun o => ?_
    have ha : c39.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    have hb : c39.get 25 = 0x80ffebc0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_op,ha,hb]
    simp only [alu]
    rw [show (0#32)+(0x80ffebc0#32) = 2164255680#32 by decide +kernel]
    rfl
  have s40 : Quiet.Step B img ⟨c40,r13⟩ ⟨c41,r13⟩ := by
    refine QuietDet.step_of (by change (2147490570#32).getLsbD 0 = false;decide) re2147490570 fun o => ?_
    rw [exec_auipc]
    change interp B img o (.done (c40.wr 1 (2147490570#32+0x00000000#32) 2147490574#32)) r13 0 [] = _
    rw [show 2147490570#32+0x00000000#32 = 2147490570#32 by decide +kernel]
    rfl
  have s41 : Quiet.Step B img ⟨c41,r13⟩ ⟨c42,r13⟩ := by
    refine QuietDet.step_of (by change (2147490574#32).getLsbD 0 = false;decide) re2147490574 fun o => ?_
    have hv : c41.get 1 = 2147490570#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,h10]
    rw [exec_jalr,hv]
    rfl
  exact .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.step s13 (.step s14 (.step s15 (.step s16 (.step s17 (.step s18 (.step s19 (.step s20 (.step s21 (.step s22 (.step s23 (.step s24 (.step s25 (.step s26 (.step s27 (.step s28 (.step s29 (.step s30 (.step s31 (.step s32 (.step s33 (.step s34 (.step s35 (.step s36 (.step s37 (.step s38 (.step s39 (.step s40 (.single s41)))))))))))))))))))))))))))))))))))))))))

end E5R.Thermostat.ReadMarshal
