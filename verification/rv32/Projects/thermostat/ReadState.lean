import Projects.thermostat.ReadEngineCode
import Projects.thermostat.Memory
import Projects.thermostat.ReadCache
import Projects.thermostat.StateStore
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace E5R.Thermostat.ReadState
open E5R E5R.Thermostat

def execute (c : Core) (ram : Word → BitVec 8) : Machine :=
  let v0 := extend .h true (ramRead ram 2164260158#32 .h)
  let c1 := c.wr 10 v0 2147490582#32
  let v1 := extend .h true (ramRead ram 2164260160#32 .h)
  let c2 := c1.wr 11 v1 2147490586#32
  let v2 := extend .w true (ramRead ram 2164255676#32 .w)
  let c3 := c2.wr 12 v2 2147490588#32
  let v3 := extend .h true (ramRead ram 2164260152#32 .h)
  let c4 := c3.wr 13 v3 2147490592#32
  let v4 := extend .h true (ramRead ram 2164260156#32 .h)
  let c5 := c4.wr 14 v4 2147490596#32
  let v5 := extend .h true (ramRead ram 2164260154#32 .h)
  let c6 := c5.wr 15 v5 2147490600#32
  let r1 := ramWrite ram 2164255686#32 (v0) .h
  let c7 := c6.goto 2147490604#32
  let r2 := ramWrite r1 2164255688#32 (v1) .h
  let c8 := c7.goto 2147490608#32
  let c9 := c8.wr 12 (v2+0x00000001#32) 2147490610#32
  let r3 := ramWrite r2 2164255676#32 ((v2+0x00000001#32)) .w
  let c10 := c9.goto 2147490612#32
  let r4 := ramWrite r3 2164255680#32 (v3) .h
  let c11 := c10.goto 2147490616#32
  let r5 := ramWrite r4 2164255682#32 (v5) .h
  let c12 := c11.goto 2147490620#32
  let r6 := ramWrite r5 2164255684#32 (v4) .h
  let c13 := c12.goto 2147490624#32
  ⟨c13,r6⟩

def memory (c : Core) (ram : Word → BitVec 8) : Word → BitVec 8 :=
  let v0 := extend .h true (ramRead ram 2164260158#32 .h)
  let v1 := extend .h true (ramRead ram 2164260160#32 .h)
  let v2 := extend .w true (ramRead ram 2164255676#32 .w)
  let v3 := extend .h true (ramRead ram 2164260152#32 .h)
  let v4 := extend .h true (ramRead ram 2164260156#32 .h)
  let v5 := extend .h true (ramRead ram 2164260154#32 .h)
  let r1 := ramWrite ram 2164255686#32 (v0) .h
  let r2 := ramWrite r1 2164255688#32 (v1) .h
  let r3 := ramWrite r2 2164255676#32 ((v2+0x00000001#32)) .w
  let r4 := ramWrite r3 2164255680#32 (v3) .h
  let r5 := ramWrite r4 2164255682#32 (v5) .h
  let r6 := ramWrite r5 2164255684#32 (v4) .h
  r6

theorem execute_ram (c : Core) (ram : Word → BitVec 8) : (execute c ram).ram = memory c ram := rfl

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 2147490578#32) (hsp : c.get 2 = 0x80ffeb90#32)
    (hfp : c.get 8 = 0x80fff814#32) (hstate : c.get 25 = 0x80ffebc0#32)
    (he : c.get 9 = 0x80ffebbc#32) (hm : Memory.Block B 0x80ffeb40#32 5312) :
    DetSteps B img 13 ⟨c,ram⟩ (execute c ram) := by
  let v0 := extend .h true (ramRead ram 2164260158#32 .h)
  let c1 := c.wr 10 v0 2147490582#32
  let v1 := extend .h true (ramRead ram 2164260160#32 .h)
  let c2 := c1.wr 11 v1 2147490586#32
  let v2 := extend .w true (ramRead ram 2164255676#32 .w)
  let c3 := c2.wr 12 v2 2147490588#32
  let v3 := extend .h true (ramRead ram 2164260152#32 .h)
  let c4 := c3.wr 13 v3 2147490592#32
  let v4 := extend .h true (ramRead ram 2164260156#32 .h)
  let c5 := c4.wr 14 v4 2147490596#32
  let v5 := extend .h true (ramRead ram 2164260154#32 .h)
  let c6 := c5.wr 15 v5 2147490600#32
  let r1 := ramWrite ram 2164255686#32 (v0) .h
  let c7 := c6.goto 2147490604#32
  let r2 := ramWrite r1 2164255688#32 (v1) .h
  let c8 := c7.goto 2147490608#32
  let c9 := c8.wr 12 (v2+0x00000001#32) 2147490610#32
  let r3 := ramWrite r2 2164255676#32 ((v2+0x00000001#32)) .w
  let c10 := c9.goto 2147490612#32
  let r4 := ramWrite r3 2164255680#32 (v3) .h
  let c11 := c10.goto 2147490616#32
  let r5 := ramWrite r4 2164255682#32 (v5) .h
  let c12 := c11.goto 2147490620#32
  let r6 := ramWrite r5 2164255684#32 (v4) .h
  let c13 := c12.goto 2147490624#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact re2147490578) fun o => ?_
    have haddr : c.get 8+0x0000052a#32 = 2164260158#32 := by simp [Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164260158#32) 2 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4606) (width := 2) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .h) (a := 2164260158#32) o (by decide) hmem,hp]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (2147490582#32).getLsbD 0 = false;decide) re2147490582 fun o => ?_
    have haddr : c1.get 8+0x0000052c#32 = 2164260160#32 := by simp [c1,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164260160#32) 2 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4608) (width := 2) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .h) (a := 2164260160#32) o (by decide) hmem]
    rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (2147490586#32).getLsbD 0 = false;decide) re2147490586 fun o => ?_
    have haddr : c2.get 9+0x00000000#32 = 2164255676#32 := by simp [c1,c2,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164255676#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 124) (width := 4) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164255676#32) o (by decide) hmem]
    rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (2147490588#32).getLsbD 0 = false;decide) re2147490588 fun o => ?_
    have haddr : c3.get 8+0x00000524#32 = 2164260152#32 := by simp [c1,c2,c3,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164260152#32) 2 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4600) (width := 2) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .h) (a := 2164260152#32) o (by decide) hmem]
    rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (2147490592#32).getLsbD 0 = false;decide) re2147490592 fun o => ?_
    have haddr : c4.get 8+0x00000528#32 = 2164260156#32 := by simp [c1,c2,c3,c4,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164260156#32) 2 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4604) (width := 2) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .h) (a := 2164260156#32) o (by decide) hmem]
    rfl
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (2147490596#32).getLsbD 0 = false;decide) re2147490596 fun o => ?_
    have haddr : c5.get 8+0x00000526#32 = 2164260154#32 := by simp [c1,c2,c3,c4,c5,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164260154#32) 2 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4602) (width := 2) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .h) (a := 2164260154#32) o (by decide) hmem]
    rfl
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,r1⟩ := by
    refine detStep_of (by change (2147490600#32).getLsbD 0 = false;decide) re2147490600 fun o => ?_
    have haddr : c6.get 25+0x00000006#32 = 2164255686#32 := by simp [c1,c2,c3,c4,c5,c6,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164255686#32) 2 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 134) (width := 2) hm (by decide) (by decide)
    have hval : c6.get 10 = v0 := by simp [c1,c2,c3,c4,c5,c6,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .h) (a := 2164255686#32) o (by decide) hmem]
    rfl
  have s7 : DetStep B img ⟨c7,r1⟩ ⟨c8,r2⟩ := by
    refine detStep_of (by change (2147490604#32).getLsbD 0 = false;decide) re2147490604 fun o => ?_
    have haddr : c7.get 25+0x00000008#32 = 2164255688#32 := by simp [c1,c2,c3,c4,c5,c6,c7,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164255688#32) 2 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 136) (width := 2) hm (by decide) (by decide)
    have hval : c7.get 11 = v1 := by simp [c1,c2,c3,c4,c5,c6,c7,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .h) (a := 2164255688#32) o (by decide) hmem]
    rfl
  have s8 : DetStep B img ⟨c8,r2⟩ ⟨c9,r2⟩ := by
    refine detStep_of (by change (2147490608#32).getLsbD 0 = false;decide) re2147490608 fun o => ?_
    have ha : c8.get 12 = v2 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    rw [exec_opimm,ha]
    simp only [alu]
    rfl
  have s9 : DetStep B img ⟨c9,r2⟩ ⟨c10,r3⟩ := by
    refine detStep_of (by change (2147490610#32).getLsbD 0 = false;decide) re2147490610 fun o => ?_
    have haddr : c9.get 9+0x00000000#32 = 2164255676#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164255676#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 124) (width := 4) hm (by decide) (by decide)
    have hval : c9.get 12 = (v2+0x00000001#32) := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255676#32) o (by decide) hmem]
    rfl
  have s10 : DetStep B img ⟨c10,r3⟩ ⟨c11,r4⟩ := by
    refine detStep_of (by change (2147490612#32).getLsbD 0 = false;decide) re2147490612 fun o => ?_
    have haddr : c10.get 25+0x00000000#32 = 2164255680#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164255680#32) 2 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 128) (width := 2) hm (by decide) (by decide)
    have hval : c10.get 13 = v3 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .h) (a := 2164255680#32) o (by decide) hmem]
    rfl
  have s11 : DetStep B img ⟨c11,r4⟩ ⟨c12,r5⟩ := by
    refine detStep_of (by change (2147490616#32).getLsbD 0 = false;decide) re2147490616 fun o => ?_
    have haddr : c11.get 25+0x00000002#32 = 2164255682#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164255682#32) 2 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 130) (width := 2) hm (by decide) (by decide)
    have hval : c11.get 15 = v5 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .h) (a := 2164255682#32) o (by decide) hmem]
    rfl
  have s12 : DetStep B img ⟨c12,r5⟩ ⟨c13,r6⟩ := by
    refine detStep_of (by change (2147490620#32).getLsbD 0 = false;decide) re2147490620 fun o => ?_
    have haddr : c12.get 25+0x00000004#32 = 2164255684#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164255684#32) 2 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 132) (width := 2) hm (by decide) (by decide)
    have hval : c12.get 14 = v4 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .h) (a := 2164255684#32) o (by decide) hmem]
    rfl
  exact .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.single s12))))))))))))
theorem fields (c : Core) (ram : Word → BitVec 8) :
    (execute c ram).core.pc = 0x80001b40#32 ∧
    (execute c ram).core.get 2 = c.get 2 ∧
    (execute c ram).core.get 8 = c.get 8 ∧
    (execute c ram).core.get 9 = c.get 9 ∧
    (execute c ram).core.get 18 = c.get 18 ∧
    (execute c ram).core.get 21 = c.get 21 ∧
    (execute c ram).core.get 25 = c.get 25 ∧
    (execute c ram).core.get 27 = c.get 27 ∧
    (execute c ram).core.sameCsr c := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,by rfl⟩

/-- Same dataflow as the verified state-store layout, at the Read output slice. -/
theorem memory_eq (c : Core) (ram : Word → BitVec 8) :
    memory c ram = StateStore.result ram 0x80fffd20#32 0x80ffebbc#32 := by rfl

theorem source (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot)
    (hs : Encoding.SnapshotAt ram 0x80fffd38#32 s) :
    Encoding.SnapshotAt (memory c ram) 0x80ffebc0#32 s := by
  rw [memory_eq]
  exact StateStore.source ram 0x80fffd20#32 0x80ffebbc#32 s hs

theorem released (c : Core) (ram : Word → BitVec 8)
    (hb : ramRead ram 0x80ffebbc#32 .w = 0xffffffff#32) :
    ramRead (memory c ram) 0x80ffebbc#32 .w = 0#32 := by
  rw [memory_eq]
  exact StateStore.released ram 0x80fffd20#32 0x80ffebbc#32 hb

theorem frame (c : Core) (ram : Word → BitVec 8) (x : Word)
    (hx : ∀ i : Fin 14, x ≠ 0x80ffebbc#32+BitVec.ofNat 32 i.val) : memory c ram x = ram x := by
  rw [memory_eq]
  exact StateStore.frame ram 0x80fffd20#32 0x80ffebbc#32 x hx

end E5R.Thermostat.ReadState
