import Projects.thermostat.ReadEngineCode
import Projects.thermostat.Memory
import Projects.thermostat.ReadCache
import Projects.thermostat.StateStore
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace E5R.Thermostat.ReadRestore
open E5R E5R.Thermostat

def execute (c : Core) (ram : Word → BitVec 8) : Machine :=
  let r1 := ramWrite ram 2164260158#32 (c.get 27) .h
  let c1 := c.goto 2147490628#32
  let r2 := ramWrite r1 2164260160#32 (c.get 21) .h
  let c2 := c1.goto 2147490632#32
  let r3 := ramWrite r2 2164260152#32 (c.get 18) .b
  let c3 := c2.goto 2147490636#32
  let v3 := extend .w true (ramRead r3 2164255640#32 .w)
  let c4 := c3.wr 10 v3 2147490638#32
  let r4 := ramWrite r3 2164260153#32 (v3) .b
  let c5 := c4.goto 2147490642#32
  let v5 := extend .w true (ramRead r4 2164255652#32 .w)
  let c6 := c5.wr 10 v5 2147490644#32
  let r5 := ramWrite r4 2164260154#32 (v5) .h
  let c7 := c6.goto 2147490648#32
  let v7 := extend .w true (ramRead r5 2164255644#32 .w)
  let c8 := c7.wr 10 v7 2147490650#32
  let r6 := ramWrite r5 2164260156#32 (v7) .h
  let c9 := c8.goto 2147490654#32
  ⟨c9,r6⟩

def memory (c : Core) (ram : Word → BitVec 8) : Word → BitVec 8 :=
  let r1 := ramWrite ram 2164260158#32 (c.get 27) .h
  let r2 := ramWrite r1 2164260160#32 (c.get 21) .h
  let r3 := ramWrite r2 2164260152#32 (c.get 18) .b
  let v3 := extend .w true (ramRead r3 2164255640#32 .w)
  let r4 := ramWrite r3 2164260153#32 (v3) .b
  let v5 := extend .w true (ramRead r4 2164255652#32 .w)
  let r5 := ramWrite r4 2164260154#32 (v5) .h
  let v7 := extend .w true (ramRead r5 2164255644#32 .w)
  let r6 := ramWrite r5 2164260156#32 (v7) .h
  r6

theorem execute_ram (c : Core) (ram : Word → BitVec 8) : (execute c ram).ram = memory c ram := rfl

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 2147490624#32) (hsp : c.get 2 = 0x80ffeb90#32)
    (hfp : c.get 8 = 0x80fff814#32) (hstate : c.get 25 = 0x80ffebc0#32)
    (he : c.get 9 = 0x80ffebbc#32) (hm : Memory.Block B 0x80ffeb40#32 5312) :
    DetSteps B img 9 ⟨c,ram⟩ (execute c ram) := by
  let r1 := ramWrite ram 2164260158#32 (c.get 27) .h
  let c1 := c.goto 2147490628#32
  let r2 := ramWrite r1 2164260160#32 (c.get 21) .h
  let c2 := c1.goto 2147490632#32
  let r3 := ramWrite r2 2164260152#32 (c.get 18) .b
  let c3 := c2.goto 2147490636#32
  let v3 := extend .w true (ramRead r3 2164255640#32 .w)
  let c4 := c3.wr 10 v3 2147490638#32
  let r4 := ramWrite r3 2164260153#32 (v3) .b
  let c5 := c4.goto 2147490642#32
  let v5 := extend .w true (ramRead r4 2164255652#32 .w)
  let c6 := c5.wr 10 v5 2147490644#32
  let r5 := ramWrite r4 2164260154#32 (v5) .h
  let c7 := c6.goto 2147490648#32
  let v7 := extend .w true (ramRead r5 2164255644#32 .w)
  let c8 := c7.wr 10 v7 2147490650#32
  let r6 := ramWrite r5 2164260156#32 (v7) .h
  let c9 := c8.goto 2147490654#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,r1⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact re2147490624) fun o => ?_
    have haddr : c.get 8+0x0000052a#32 = 2164260158#32 := by simp [Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164260158#32) 2 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4606) (width := 2) hm (by decide) (by decide)
    have hval : c.get 27 = c.get 27 := by simp [Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .h) (a := 2164260158#32) o (by decide) hmem,hp]
    rfl
  have s1 : DetStep B img ⟨c1,r1⟩ ⟨c2,r2⟩ := by
    refine detStep_of (by change (2147490628#32).getLsbD 0 = false;decide) re2147490628 fun o => ?_
    have haddr : c1.get 8+0x0000052c#32 = 2164260160#32 := by simp [c1,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164260160#32) 2 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4608) (width := 2) hm (by decide) (by decide)
    have hval : c1.get 21 = c.get 21 := by simp [c1,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .h) (a := 2164260160#32) o (by decide) hmem]
    rfl
  have s2 : DetStep B img ⟨c2,r2⟩ ⟨c3,r3⟩ := by
    refine detStep_of (by change (2147490632#32).getLsbD 0 = false;decide) re2147490632 fun o => ?_
    have haddr : c2.get 8+0x00000524#32 = 2164260152#32 := by simp [c1,c2,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164260152#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4600) (width := 1) hm (by decide) (by decide)
    have hval : c2.get 18 = c.get 18 := by simp [c1,c2,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164260152#32) o (by decide) hmem]
    rfl
  have s3 : DetStep B img ⟨c3,r3⟩ ⟨c4,r3⟩ := by
    refine detStep_of (by change (2147490636#32).getLsbD 0 = false;decide) re2147490636 fun o => ?_
    have haddr : c3.get 2+0x00000008#32 = 2164255640#32 := by simp [c1,c2,c3,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164255640#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 88) (width := 4) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164255640#32) o (by decide) hmem]
    rfl
  have s4 : DetStep B img ⟨c4,r3⟩ ⟨c5,r4⟩ := by
    refine detStep_of (by change (2147490638#32).getLsbD 0 = false;decide) re2147490638 fun o => ?_
    have haddr : c4.get 8+0x00000525#32 = 2164260153#32 := by simp [c1,c2,c3,c4,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164260153#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4601) (width := 1) hm (by decide) (by decide)
    have hval : c4.get 10 = v3 := by simp [c1,c2,c3,c4,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164260153#32) o (by decide) hmem]
    rfl
  have s5 : DetStep B img ⟨c5,r4⟩ ⟨c6,r4⟩ := by
    refine detStep_of (by change (2147490642#32).getLsbD 0 = false;decide) re2147490642 fun o => ?_
    have haddr : c5.get 2+0x00000014#32 = 2164255652#32 := by simp [c1,c2,c3,c4,c5,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164255652#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 100) (width := 4) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164255652#32) o (by decide) hmem]
    rfl
  have s6 : DetStep B img ⟨c6,r4⟩ ⟨c7,r5⟩ := by
    refine detStep_of (by change (2147490644#32).getLsbD 0 = false;decide) re2147490644 fun o => ?_
    have haddr : c6.get 8+0x00000526#32 = 2164260154#32 := by simp [c1,c2,c3,c4,c5,c6,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164260154#32) 2 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4602) (width := 2) hm (by decide) (by decide)
    have hval : c6.get 10 = v5 := by simp [c1,c2,c3,c4,c5,c6,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .h) (a := 2164260154#32) o (by decide) hmem]
    rfl
  have s7 : DetStep B img ⟨c7,r5⟩ ⟨c8,r5⟩ := by
    refine detStep_of (by change (2147490648#32).getLsbD 0 = false;decide) re2147490648 fun o => ?_
    have haddr : c7.get 2+0x0000000c#32 = 2164255644#32 := by simp [c1,c2,c3,c4,c5,c6,c7,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164255644#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 92) (width := 4) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164255644#32) o (by decide) hmem]
    rfl
  have s8 : DetStep B img ⟨c8,r5⟩ ⟨c9,r6⟩ := by
    refine detStep_of (by change (2147490650#32).getLsbD 0 = false;decide) re2147490650 fun o => ?_
    have haddr : c8.get 8+0x00000528#32 = 2164260156#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    have hmem : B.inRam (2164260156#32) 2 = true := Memory.block_access (B := B) (p := 0x80ffeb40#32) (n := 5312) (off := 4604) (width := 2) hm (by decide) (by decide)
    have hval : c8.get 10 = v7 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp,hstate,he]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .h) (a := 2164260156#32) o (by decide) hmem]
    rfl
  exact .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.single s8))))))))
theorem fields (c : Core) (ram : Word → BitVec 8) :
    (execute c ram).core.pc = 0x80001b5e#32 ∧
    (execute c ram).core.get 2 = c.get 2 ∧
    (execute c ram).core.get 8 = c.get 8 ∧
    (execute c ram).core.get 9 = c.get 9 ∧
    (execute c ram).core.get 18 = c.get 18 ∧
    (execute c ram).core.get 21 = c.get 21 ∧
    (execute c ram).core.get 25 = c.get 25 ∧
    (execute c ram).core.get 27 = c.get 27 ∧
    (execute c ram).core.sameCsr c := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,by rfl⟩

theorem bytes (c : Core) (ram : Word → BitVec 8) (i : Fin 10) :
    memory c ram (0x80fffd38#32+BitVec.ofNat 32 i.val) = ReadCache.byte c ram i := by
  have hi := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
      i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 := by omega
  rcases hc with h|h|h|h|h|h|h|h|h|h
  all_goals simp [h,memory,ReadCache.byte,ramWrite,ramPut,ramRead,extend]

theorem source (c : Core) (ram : Word → BitVec 8) (reply : Spec.Snapshot)
    (hc : ReadCache.At c ram reply) : Encoding.SnapshotAt (memory c ram) 0x80fffd38#32 reply := by
  intro i
  exact (bytes c ram i).trans (hc i)

theorem frame (c : Core) (ram : Word → BitVec 8) (x : Word)
    (hx : ∀ i : Fin 10, x ≠ 0x80fffd38#32+BitVec.ofNat 32 i.val) : memory c ram x = ram x := by
  have h0 : x ≠ 2164260152#32 := hx ⟨0,by decide⟩
  have h1 : x ≠ 2164260153#32 := hx ⟨1,by decide⟩
  have h2 : x ≠ 2164260154#32 := hx ⟨2,by decide⟩
  have h3 : x ≠ 2164260155#32 := hx ⟨3,by decide⟩
  have h4 : x ≠ 2164260156#32 := hx ⟨4,by decide⟩
  have h5 : x ≠ 2164260157#32 := hx ⟨5,by decide⟩
  have h6 : x ≠ 2164260158#32 := hx ⟨6,by decide⟩
  have h7 : x ≠ 2164260159#32 := hx ⟨7,by decide⟩
  have h8 : x ≠ 2164260160#32 := hx ⟨8,by decide⟩
  have h9 : x ≠ 2164260161#32 := hx ⟨9,by decide⟩
  simp [memory,ramWrite,ramPut,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]

end E5R.Thermostat.ReadRestore
