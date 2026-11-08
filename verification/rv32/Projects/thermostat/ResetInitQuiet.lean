-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.Init
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.constructorNameAsVariable false
open E5R E5R.Thermostat
namespace E5R.Thermostat.Init
theorem contract_full_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000862) (hsp : c.get 2 = 0x81000000)
    (hmem : Memory.Block B 0x80ffeb90 5232) :
    ∃ d r, Quiet.Steps B img 33 ⟨c,ram⟩ ⟨d,r⟩ ∧
      d.pc = 0x800008d8 ∧ d.get 2 = 0x80ffeb90 ∧ d.sameCsr c ∧
      Encoding.SnapshotAt r 0x80ffebc0 Spec.initial ∧
      ramRead r 0x80ffebbc .w = 0 ∧
      ramRead r 0x80ffebcc .w = 0x80005b7c ∧
      ramRead r 0x80ffebd0 .w = 7 ∧ r 0x80ffebd4 = 1 ∧
      (∀ x, (∀ i : Fin 5232, x ≠ 0x80ffeb90+BitVec.ofNat 32 i.val) → r x = ram x) ∧ d.get 8 = 0x80fff814#32 ∧ d.get 19 = 0x10000000#32 ∧ d.get 22 = 1#32 ∧ d.get 12 = 2048#32 := by
  let r2 := ramWrite ram 2164260860#32 (c.get 1) .w
  let r3 := ramWrite r2 2164260856#32 (c.get 8) .w
  let r4 := ramWrite r3 2164260852#32 (c.get 9) .w
  let r5 := ramWrite r4 2164260848#32 (c.get 18) .w
  let r6 := ramWrite r5 2164260844#32 (c.get 19) .w
  let r7 := ramWrite r6 2164260840#32 (c.get 20) .w
  let r8 := ramWrite r7 2164260836#32 (c.get 21) .w
  let r9 := ramWrite r8 2164260832#32 (c.get 22) .w
  let r10 := ramWrite r9 2164260828#32 (c.get 23) .w
  let r11 := ramWrite r10 2164260824#32 (c.get 24) .w
  let r12 := ramWrite r11 2164260820#32 (c.get 25) .w
  let r13 := ramWrite r12 2164260816#32 (c.get 26) .w
  let r14 := ramWrite r13 2164260812#32 (c.get 27) .w
  let r24 := ramWrite r14 2164255676#32 (0#32) .w
  let r25 := ramWrite r24 2164255680#32 (0#32) .w
  let r26 := ramWrite r25 2164255684#32 (13107400#32) .w
  let r27 := ramWrite r26 2164255688#32 (0#32) .h
  let r31 := ramWrite r27 2164255692#32 (2147507068#32) .w
  let r32 := ramWrite r31 2164255696#32 (7#32) .w
  let r33 := ramWrite r32 2164255700#32 (1#32) .b
  let c1 := c.wr 2 2164258832#32 2147485798#32
  let c2 := c1.goto 2147485802#32
  let c3 := c2.goto 2147485806#32
  let c4 := c3.goto 2147485810#32
  let c5 := c4.goto 2147485814#32
  let c6 := c5.goto 2147485818#32
  let c7 := c6.goto 2147485822#32
  let c8 := c7.goto 2147485826#32
  let c9 := c8.goto 2147485830#32
  let c10 := c9.goto 2147485834#32
  let c11 := c10.goto 2147485838#32
  let c12 := c11.goto 2147485842#32
  let c13 := c12.goto 2147485846#32
  let c14 := c13.goto 2147485850#32
  let c15 := c14.wr 2 2164256784#32 2147485854#32
  let c16 := c15.wr 2 2164255632#32 2147485858#32
  let c17 := c16.wr 8 2164257679#32 2147485862#32
  let c18 := c17.wr 8 2164258836#32 2147485866#32
  let c19 := c18.wr 19 268435456#32 2147485870#32
  let c20 := c19.wr 22 1#32 2147485872#32
  let c21 := c20.wr 12 2048#32 2147485876#32
  let c22 := c21.wr 10 13107200#32 2147485880#32
  let c23 := c22.wr 10 13107400#32 2147485884#32
  let c24 := c23.goto 2147485886#32
  let c25 := c24.goto 2147485888#32
  let c26 := c25.goto 2147485890#32
  let c27 := c26.goto 2147485894#32
  let c28 := c27.wr 10 2147508224#32 2147485898#32
  let c29 := c28.wr 10 2147507068#32 2147485902#32
  let c30 := c29.wr 11 7#32 2147485904#32
  let c31 := c30.goto 2147485906#32
  let c32 := c31.goto 2147485908#32
  let c33 := c32.goto 2147485912#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact ini2147485794) fun o => ?_
    rw [exec_opimm]
    have hs : c.get 2 = 2164260864#32 := by simp [Core.wr_get,hsp]
    rw [hs]
    rw [hp]
    rw [show alu .add 2164260864#32 4294965264#32 = 2164258832#32 by decide +kernel]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r2⟩ := by
    refine QuietDet.step_of (by change (2147485798#32).getLsbD 0 = false;decide) (ini2147485798) fun o => ?_
    have hs : c1.get 2 = 2164258832#32 := by simp [c1,Core.wr_get,hsp]
    have hv : c1.get 1 = (c.get 1) := by simp [c1,Core.wr_get]
    rw [exec_store,hs,hv]
    have hm : B.inRam 2164260860#32 4 = true := by
      exact Memory.block_access (B := B) (p := 0x80ffeb90) (n := 5232) (off := 5228) (width := 4) hmem (by decide) (by decide)
    change interp B img o (.store .w 2164260860#32 (c.get 1) false (.done c2)) ram 0 [] = _
    rw [interp_store_ram o (by decide) hm]
    rfl
  have s2 : Quiet.Step B img ⟨c2,r2⟩ ⟨c3,r3⟩ := by
    refine QuietDet.step_of (by change (2147485802#32).getLsbD 0 = false;decide) (ini2147485802) fun o => ?_
    have hs : c2.get 2 = 2164258832#32 := by simp [c1,c2,Core.wr_get,hsp]
    have hv : c2.get 8 = (c.get 8) := by simp [c1,c2,Core.wr_get]
    rw [exec_store,hs,hv]
    have hm : B.inRam 2164260856#32 4 = true := by
      exact Memory.block_access (B := B) (p := 0x80ffeb90) (n := 5232) (off := 5224) (width := 4) hmem (by decide) (by decide)
    change interp B img o (.store .w 2164260856#32 (c.get 8) false (.done c3)) r2 0 [] = _
    rw [interp_store_ram o (by decide) hm]
    rfl
  have s3 : Quiet.Step B img ⟨c3,r3⟩ ⟨c4,r4⟩ := by
    refine QuietDet.step_of (by change (2147485806#32).getLsbD 0 = false;decide) (ini2147485806) fun o => ?_
    have hs : c3.get 2 = 2164258832#32 := by simp [c1,c2,c3,Core.wr_get,hsp]
    have hv : c3.get 9 = (c.get 9) := by simp [c1,c2,c3,Core.wr_get]
    rw [exec_store,hs,hv]
    have hm : B.inRam 2164260852#32 4 = true := by
      exact Memory.block_access (B := B) (p := 0x80ffeb90) (n := 5232) (off := 5220) (width := 4) hmem (by decide) (by decide)
    change interp B img o (.store .w 2164260852#32 (c.get 9) false (.done c4)) r3 0 [] = _
    rw [interp_store_ram o (by decide) hm]
    rfl
  have s4 : Quiet.Step B img ⟨c4,r4⟩ ⟨c5,r5⟩ := by
    refine QuietDet.step_of (by change (2147485810#32).getLsbD 0 = false;decide) (ini2147485810) fun o => ?_
    have hs : c4.get 2 = 2164258832#32 := by simp [c1,c2,c3,c4,Core.wr_get,hsp]
    have hv : c4.get 18 = (c.get 18) := by simp [c1,c2,c3,c4,Core.wr_get]
    rw [exec_store,hs,hv]
    have hm : B.inRam 2164260848#32 4 = true := by
      exact Memory.block_access (B := B) (p := 0x80ffeb90) (n := 5232) (off := 5216) (width := 4) hmem (by decide) (by decide)
    change interp B img o (.store .w 2164260848#32 (c.get 18) false (.done c5)) r4 0 [] = _
    rw [interp_store_ram o (by decide) hm]
    rfl
  have s5 : Quiet.Step B img ⟨c5,r5⟩ ⟨c6,r6⟩ := by
    refine QuietDet.step_of (by change (2147485814#32).getLsbD 0 = false;decide) (ini2147485814) fun o => ?_
    have hs : c5.get 2 = 2164258832#32 := by simp [c1,c2,c3,c4,c5,Core.wr_get,hsp]
    have hv : c5.get 19 = (c.get 19) := by simp [c1,c2,c3,c4,c5,Core.wr_get]
    rw [exec_store,hs,hv]
    have hm : B.inRam 2164260844#32 4 = true := by
      exact Memory.block_access (B := B) (p := 0x80ffeb90) (n := 5232) (off := 5212) (width := 4) hmem (by decide) (by decide)
    change interp B img o (.store .w 2164260844#32 (c.get 19) false (.done c6)) r5 0 [] = _
    rw [interp_store_ram o (by decide) hm]
    rfl
  have s6 : Quiet.Step B img ⟨c6,r6⟩ ⟨c7,r7⟩ := by
    refine QuietDet.step_of (by change (2147485818#32).getLsbD 0 = false;decide) (ini2147485818) fun o => ?_
    have hs : c6.get 2 = 2164258832#32 := by simp [c1,c2,c3,c4,c5,c6,Core.wr_get,hsp]
    have hv : c6.get 20 = (c.get 20) := by simp [c1,c2,c3,c4,c5,c6,Core.wr_get]
    rw [exec_store,hs,hv]
    have hm : B.inRam 2164260840#32 4 = true := by
      exact Memory.block_access (B := B) (p := 0x80ffeb90) (n := 5232) (off := 5208) (width := 4) hmem (by decide) (by decide)
    change interp B img o (.store .w 2164260840#32 (c.get 20) false (.done c7)) r6 0 [] = _
    rw [interp_store_ram o (by decide) hm]
    rfl
  have s7 : Quiet.Step B img ⟨c7,r7⟩ ⟨c8,r8⟩ := by
    refine QuietDet.step_of (by change (2147485822#32).getLsbD 0 = false;decide) (ini2147485822) fun o => ?_
    have hs : c7.get 2 = 2164258832#32 := by simp [c1,c2,c3,c4,c5,c6,c7,Core.wr_get,hsp]
    have hv : c7.get 21 = (c.get 21) := by simp [c1,c2,c3,c4,c5,c6,c7,Core.wr_get]
    rw [exec_store,hs,hv]
    have hm : B.inRam 2164260836#32 4 = true := by
      exact Memory.block_access (B := B) (p := 0x80ffeb90) (n := 5232) (off := 5204) (width := 4) hmem (by decide) (by decide)
    change interp B img o (.store .w 2164260836#32 (c.get 21) false (.done c8)) r7 0 [] = _
    rw [interp_store_ram o (by decide) hm]
    rfl
  have s8 : Quiet.Step B img ⟨c8,r8⟩ ⟨c9,r9⟩ := by
    refine QuietDet.step_of (by change (2147485826#32).getLsbD 0 = false;decide) (ini2147485826) fun o => ?_
    have hs : c8.get 2 = 2164258832#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,Core.wr_get,hsp]
    have hv : c8.get 22 = (c.get 22) := by simp [c1,c2,c3,c4,c5,c6,c7,c8,Core.wr_get]
    rw [exec_store,hs,hv]
    have hm : B.inRam 2164260832#32 4 = true := by
      exact Memory.block_access (B := B) (p := 0x80ffeb90) (n := 5232) (off := 5200) (width := 4) hmem (by decide) (by decide)
    change interp B img o (.store .w 2164260832#32 (c.get 22) false (.done c9)) r8 0 [] = _
    rw [interp_store_ram o (by decide) hm]
    rfl
  have s9 : Quiet.Step B img ⟨c9,r9⟩ ⟨c10,r10⟩ := by
    refine QuietDet.step_of (by change (2147485830#32).getLsbD 0 = false;decide) (ini2147485830) fun o => ?_
    have hs : c9.get 2 = 2164258832#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,Core.wr_get,hsp]
    have hv : c9.get 23 = (c.get 23) := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,Core.wr_get]
    rw [exec_store,hs,hv]
    have hm : B.inRam 2164260828#32 4 = true := by
      exact Memory.block_access (B := B) (p := 0x80ffeb90) (n := 5232) (off := 5196) (width := 4) hmem (by decide) (by decide)
    change interp B img o (.store .w 2164260828#32 (c.get 23) false (.done c10)) r9 0 [] = _
    rw [interp_store_ram o (by decide) hm]
    rfl
  have s10 : Quiet.Step B img ⟨c10,r10⟩ ⟨c11,r11⟩ := by
    refine QuietDet.step_of (by change (2147485834#32).getLsbD 0 = false;decide) (ini2147485834) fun o => ?_
    have hs : c10.get 2 = 2164258832#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,Core.wr_get,hsp]
    have hv : c10.get 24 = (c.get 24) := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,Core.wr_get]
    rw [exec_store,hs,hv]
    have hm : B.inRam 2164260824#32 4 = true := by
      exact Memory.block_access (B := B) (p := 0x80ffeb90) (n := 5232) (off := 5192) (width := 4) hmem (by decide) (by decide)
    change interp B img o (.store .w 2164260824#32 (c.get 24) false (.done c11)) r10 0 [] = _
    rw [interp_store_ram o (by decide) hm]
    rfl
  have s11 : Quiet.Step B img ⟨c11,r11⟩ ⟨c12,r12⟩ := by
    refine QuietDet.step_of (by change (2147485838#32).getLsbD 0 = false;decide) (ini2147485838) fun o => ?_
    have hs : c11.get 2 = 2164258832#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,Core.wr_get,hsp]
    have hv : c11.get 25 = (c.get 25) := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,Core.wr_get]
    rw [exec_store,hs,hv]
    have hm : B.inRam 2164260820#32 4 = true := by
      exact Memory.block_access (B := B) (p := 0x80ffeb90) (n := 5232) (off := 5188) (width := 4) hmem (by decide) (by decide)
    change interp B img o (.store .w 2164260820#32 (c.get 25) false (.done c12)) r11 0 [] = _
    rw [interp_store_ram o (by decide) hm]
    rfl
  have s12 : Quiet.Step B img ⟨c12,r12⟩ ⟨c13,r13⟩ := by
    refine QuietDet.step_of (by change (2147485842#32).getLsbD 0 = false;decide) (ini2147485842) fun o => ?_
    have hs : c12.get 2 = 2164258832#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,Core.wr_get,hsp]
    have hv : c12.get 26 = (c.get 26) := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,Core.wr_get]
    rw [exec_store,hs,hv]
    have hm : B.inRam 2164260816#32 4 = true := by
      exact Memory.block_access (B := B) (p := 0x80ffeb90) (n := 5232) (off := 5184) (width := 4) hmem (by decide) (by decide)
    change interp B img o (.store .w 2164260816#32 (c.get 26) false (.done c13)) r12 0 [] = _
    rw [interp_store_ram o (by decide) hm]
    rfl
  have s13 : Quiet.Step B img ⟨c13,r13⟩ ⟨c14,r14⟩ := by
    refine QuietDet.step_of (by change (2147485846#32).getLsbD 0 = false;decide) (ini2147485846) fun o => ?_
    have hs : c13.get 2 = 2164258832#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,Core.wr_get,hsp]
    have hv : c13.get 27 = (c.get 27) := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,Core.wr_get]
    rw [exec_store,hs,hv]
    have hm : B.inRam 2164260812#32 4 = true := by
      exact Memory.block_access (B := B) (p := 0x80ffeb90) (n := 5232) (off := 5180) (width := 4) hmem (by decide) (by decide)
    change interp B img o (.store .w 2164260812#32 (c.get 27) false (.done c14)) r13 0 [] = _
    rw [interp_store_ram o (by decide) hm]
    rfl
  have s14 : Quiet.Step B img ⟨c14,r14⟩ ⟨c15,r14⟩ := by
    refine QuietDet.step_of (by change (2147485850#32).getLsbD 0 = false;decide) (ini2147485850) fun o => ?_
    rw [exec_opimm]
    have hs : c14.get 2 = 2164258832#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,Core.wr_get,hsp]
    rw [hs]
    
    rw [show alu .add 2164258832#32 4294965248#32 = 2164256784#32 by decide +kernel]
    rfl
  have s15 : Quiet.Step B img ⟨c15,r14⟩ ⟨c16,r14⟩ := by
    refine QuietDet.step_of (by change (2147485854#32).getLsbD 0 = false;decide) (ini2147485854) fun o => ?_
    rw [exec_opimm]
    have hs : c15.get 2 = 2164256784#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,Core.wr_get,hsp]
    rw [hs]
    
    rw [show alu .add 2164256784#32 4294966144#32 = 2164255632#32 by decide +kernel]
    rfl
  have s16 : Quiet.Step B img ⟨c16,r14⟩ ⟨c17,r14⟩ := by
    refine QuietDet.step_of (by change (2147485858#32).getLsbD 0 = false;decide) (ini2147485858) fun o => ?_
    rw [exec_opimm]
    have hs : c16.get 2 = 2164255632#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,Core.wr_get,hsp]
    rw [hs]
    
    rw [show alu .add 2164255632#32 2047#32 = 2164257679#32 by decide +kernel]
    rfl
  have s17 : Quiet.Step B img ⟨c17,r14⟩ ⟨c18,r14⟩ := by
    refine QuietDet.step_of (by change (2147485862#32).getLsbD 0 = false;decide) (ini2147485862) fun o => ?_
    rw [exec_opimm]
    have hs : c17.get 8 = 2164257679#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,Core.wr_get,hsp]
    rw [hs]
    
    rw [show alu .add 2164257679#32 1157#32 = 2164258836#32 by decide +kernel]
    rfl
  have s18 : Quiet.Step B img ⟨c18,r14⟩ ⟨c19,r14⟩ := by
    refine QuietDet.step_of (by change (2147485866#32).getLsbD 0 = false;decide) (ini2147485866) fun o => ?_
    rw [exec_lui]
    
    rfl
  have s19 : Quiet.Step B img ⟨c19,r14⟩ ⟨c20,r14⟩ := by
    refine QuietDet.step_of (by change (2147485870#32).getLsbD 0 = false;decide) (ini2147485870) fun o => ?_
    rw [exec_opimm]
    have hs : c19.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,Core.wr_get,hsp]
    rw [hs]
    
    rw [show alu .add 0#32 1#32 = 1#32 by decide +kernel]
    rfl
  have s20 : Quiet.Step B img ⟨c20,r14⟩ ⟨c21,r14⟩ := by
    refine QuietDet.step_of (by change (2147485872#32).getLsbD 0 = false;decide) (ini2147485872) fun o => ?_
    rw [exec_opimm]
    have hs : c20.get 22 = 1#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,Core.wr_get,hsp]
    rw [hs]
    
    rw [show alu .sll 1#32 11#32 = 2048#32 by decide +kernel]
    rfl
  have s21 : Quiet.Step B img ⟨c21,r14⟩ ⟨c22,r14⟩ := by
    refine QuietDet.step_of (by change (2147485876#32).getLsbD 0 = false;decide) (ini2147485876) fun o => ?_
    rw [exec_lui]
    
    rfl
  have s22 : Quiet.Step B img ⟨c22,r14⟩ ⟨c23,r14⟩ := by
    refine QuietDet.step_of (by change (2147485880#32).getLsbD 0 = false;decide) (ini2147485880) fun o => ?_
    rw [exec_opimm]
    have hs : c22.get 10 = 13107200#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,Core.wr_get,hsp]
    rw [hs]
    
    rw [show alu .add 13107200#32 200#32 = 13107400#32 by decide +kernel]
    rfl
  have s23 : Quiet.Step B img ⟨c23,r14⟩ ⟨c24,r24⟩ := by
    refine QuietDet.step_of (by change (2147485884#32).getLsbD 0 = false;decide) (ini2147485884) fun o => ?_
    have hs : c23.get 2 = 2164255632#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,Core.wr_get,hsp]
    have hv : c23.get 0 = (0#32) := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,Core.wr_get]
    rw [exec_store,hs,hv]
    have hm : B.inRam 2164255676#32 4 = true := by
      exact Memory.block_access (B := B) (p := 0x80ffeb90) (n := 5232) (off := 44) (width := 4) hmem (by decide) (by decide)
    change interp B img o (.store .w 2164255676#32 (0#32) false (.done c24)) r14 0 [] = _
    rw [interp_store_ram o (by decide) hm]
    rfl
  have s24 : Quiet.Step B img ⟨c24,r24⟩ ⟨c25,r25⟩ := by
    refine QuietDet.step_of (by change (2147485886#32).getLsbD 0 = false;decide) (ini2147485886) fun o => ?_
    have hs : c24.get 2 = 2164255632#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,Core.wr_get,hsp]
    have hv : c24.get 0 = (0#32) := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,Core.wr_get]
    rw [exec_store,hs,hv]
    have hm : B.inRam 2164255680#32 4 = true := by
      exact Memory.block_access (B := B) (p := 0x80ffeb90) (n := 5232) (off := 48) (width := 4) hmem (by decide) (by decide)
    change interp B img o (.store .w 2164255680#32 (0#32) false (.done c25)) r24 0 [] = _
    rw [interp_store_ram o (by decide) hm]
    rfl
  have s25 : Quiet.Step B img ⟨c25,r25⟩ ⟨c26,r26⟩ := by
    refine QuietDet.step_of (by change (2147485888#32).getLsbD 0 = false;decide) (ini2147485888) fun o => ?_
    have hs : c25.get 2 = 2164255632#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,Core.wr_get,hsp]
    have hv : c25.get 10 = (13107400#32) := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,Core.wr_get]
    rw [exec_store,hs,hv]
    have hm : B.inRam 2164255684#32 4 = true := by
      exact Memory.block_access (B := B) (p := 0x80ffeb90) (n := 5232) (off := 52) (width := 4) hmem (by decide) (by decide)
    change interp B img o (.store .w 2164255684#32 (13107400#32) false (.done c26)) r25 0 [] = _
    rw [interp_store_ram o (by decide) hm]
    rfl
  have s26 : Quiet.Step B img ⟨c26,r26⟩ ⟨c27,r27⟩ := by
    refine QuietDet.step_of (by change (2147485890#32).getLsbD 0 = false;decide) (ini2147485890) fun o => ?_
    have hs : c26.get 2 = 2164255632#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,Core.wr_get,hsp]
    have hv : c26.get 0 = (0#32) := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,Core.wr_get]
    rw [exec_store,hs,hv]
    have hm : B.inRam 2164255688#32 2 = true := by
      exact Memory.block_access (B := B) (p := 0x80ffeb90) (n := 5232) (off := 56) (width := 2) hmem (by decide) (by decide)
    change interp B img o (.store .h 2164255688#32 (0#32) false (.done c27)) r26 0 [] = _
    rw [interp_store_ram o (by decide) hm]
    rfl
  have s27 : Quiet.Step B img ⟨c27,r27⟩ ⟨c28,r27⟩ := by
    refine QuietDet.step_of (by change (2147485894#32).getLsbD 0 = false;decide) (ini2147485894) fun o => ?_
    rw [exec_lui]
    
    rfl
  have s28 : Quiet.Step B img ⟨c28,r27⟩ ⟨c29,r27⟩ := by
    refine QuietDet.step_of (by change (2147485898#32).getLsbD 0 = false;decide) (ini2147485898) fun o => ?_
    rw [exec_opimm]
    have hs : c28.get 10 = 2147508224#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,Core.wr_get,hsp]
    rw [hs]
    
    rw [show alu .add 2147508224#32 4294966140#32 = 2147507068#32 by decide +kernel]
    rfl
  have s29 : Quiet.Step B img ⟨c29,r27⟩ ⟨c30,r27⟩ := by
    refine QuietDet.step_of (by change (2147485902#32).getLsbD 0 = false;decide) (ini2147485902) fun o => ?_
    rw [exec_opimm]
    have hs : c29.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,Core.wr_get,hsp]
    rw [hs]
    
    rw [show alu .add 0#32 7#32 = 7#32 by decide +kernel]
    rfl
  have s30 : Quiet.Step B img ⟨c30,r27⟩ ⟨c31,r31⟩ := by
    refine QuietDet.step_of (by change (2147485904#32).getLsbD 0 = false;decide) (ini2147485904) fun o => ?_
    have hs : c30.get 2 = 2164255632#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,Core.wr_get,hsp]
    have hv : c30.get 10 = (2147507068#32) := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,Core.wr_get]
    rw [exec_store,hs,hv]
    have hm : B.inRam 2164255692#32 4 = true := by
      exact Memory.block_access (B := B) (p := 0x80ffeb90) (n := 5232) (off := 60) (width := 4) hmem (by decide) (by decide)
    change interp B img o (.store .w 2164255692#32 (2147507068#32) false (.done c31)) r27 0 [] = _
    rw [interp_store_ram o (by decide) hm]
    rfl
  have s31 : Quiet.Step B img ⟨c31,r31⟩ ⟨c32,r32⟩ := by
    refine QuietDet.step_of (by change (2147485906#32).getLsbD 0 = false;decide) (ini2147485906) fun o => ?_
    have hs : c31.get 2 = 2164255632#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,Core.wr_get,hsp]
    have hv : c31.get 11 = (7#32) := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,Core.wr_get]
    rw [exec_store,hs,hv]
    have hm : B.inRam 2164255696#32 4 = true := by
      exact Memory.block_access (B := B) (p := 0x80ffeb90) (n := 5232) (off := 64) (width := 4) hmem (by decide) (by decide)
    change interp B img o (.store .w 2164255696#32 (7#32) false (.done c32)) r31 0 [] = _
    rw [interp_store_ram o (by decide) hm]
    rfl
  have s32 : Quiet.Step B img ⟨c32,r32⟩ ⟨c33,r33⟩ := by
    refine QuietDet.step_of (by change (2147485908#32).getLsbD 0 = false;decide) (ini2147485908) fun o => ?_
    have hs : c32.get 2 = 2164255632#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,Core.wr_get,hsp]
    have hv : c32.get 22 = (1#32) := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,Core.wr_get]
    rw [exec_store,hs,hv]
    have hm : B.inRam 2164255700#32 1 = true := by
      exact Memory.block_access (B := B) (p := 0x80ffeb90) (n := 5232) (off := 68) (width := 1) hmem (by decide) (by decide)
    change interp B img o (.store .b 2164255700#32 (1#32) false (.done c33)) r32 0 [] = _
    rw [interp_store_ram o (by decide) hm]
    rfl
  refine ⟨c33,r33,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.step s13 (.step s14 (.step s15 (.step s16 (.step s17 (.step s18 (.step s19 (.step s20 (.step s21 (.step s22 (.step s23 (.step s24 (.step s25 (.step s26 (.step s27 (.step s28 (.step s29 (.step s30 (.step s31 (.single s32)))))))))))))))))))))))))))))))),rfl,?_,by rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,Core.wr_get]
  · intro i
    rcases i with ⟨i,hi⟩
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r24,r25,r26,r27,r31,r32,r33,ramWrite,ramPut,byteOf,Encoding.snapshotByte,Encoding.boolByte,Encoding.shortByte,Encoding.modeByte,Spec.initial]
  · simp [r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r24,r25,r26,r27,r31,r32,r33,ramRead,ramWrite,ramPut,byteOf]
  · simp [r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r24,r25,r26,r27,r31,r32,r33,ramRead,ramWrite,ramPut,byteOf]
  · simp [r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r24,r25,r26,r27,r31,r32,r33,ramRead,ramWrite,ramPut,byteOf]
  · simp [r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r24,r25,r26,r27,r31,r32,r33,ramRead,ramWrite,ramPut,byteOf]
  · intro x hx
    simp only [r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r24,r25,r26,r27,r31,r32,r33]
    have hr33 : ∀ j : Fin 1, x ≠ 2164255700#32+BitVec.ofNat 32 j.val := by
      intro j
      have hj := j.isLt
      have ha : (0x80ffeb90 : Word)+BitVec.ofNat 32 68 = 2164255700#32 := by decide +kernel
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hx ⟨68+j.val,by omega⟩
    rw [write_frame _ _ _ x .b hr33]
    have hr32 : ∀ j : Fin 4, x ≠ 2164255696#32+BitVec.ofNat 32 j.val := by
      intro j
      have hj := j.isLt
      have ha : (0x80ffeb90 : Word)+BitVec.ofNat 32 64 = 2164255696#32 := by decide +kernel
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hx ⟨64+j.val,by omega⟩
    rw [write_frame _ _ _ x .w hr32]
    have hr31 : ∀ j : Fin 4, x ≠ 2164255692#32+BitVec.ofNat 32 j.val := by
      intro j
      have hj := j.isLt
      have ha : (0x80ffeb90 : Word)+BitVec.ofNat 32 60 = 2164255692#32 := by decide +kernel
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hx ⟨60+j.val,by omega⟩
    rw [write_frame _ _ _ x .w hr31]
    have hr27 : ∀ j : Fin 2, x ≠ 2164255688#32+BitVec.ofNat 32 j.val := by
      intro j
      have hj := j.isLt
      have ha : (0x80ffeb90 : Word)+BitVec.ofNat 32 56 = 2164255688#32 := by decide +kernel
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hx ⟨56+j.val,by omega⟩
    rw [write_frame _ _ _ x .h hr27]
    have hr26 : ∀ j : Fin 4, x ≠ 2164255684#32+BitVec.ofNat 32 j.val := by
      intro j
      have hj := j.isLt
      have ha : (0x80ffeb90 : Word)+BitVec.ofNat 32 52 = 2164255684#32 := by decide +kernel
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hx ⟨52+j.val,by omega⟩
    rw [write_frame _ _ _ x .w hr26]
    have hr25 : ∀ j : Fin 4, x ≠ 2164255680#32+BitVec.ofNat 32 j.val := by
      intro j
      have hj := j.isLt
      have ha : (0x80ffeb90 : Word)+BitVec.ofNat 32 48 = 2164255680#32 := by decide +kernel
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hx ⟨48+j.val,by omega⟩
    rw [write_frame _ _ _ x .w hr25]
    have hr24 : ∀ j : Fin 4, x ≠ 2164255676#32+BitVec.ofNat 32 j.val := by
      intro j
      have hj := j.isLt
      have ha : (0x80ffeb90 : Word)+BitVec.ofNat 32 44 = 2164255676#32 := by decide +kernel
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hx ⟨44+j.val,by omega⟩
    rw [write_frame _ _ _ x .w hr24]
    have hr14 : ∀ j : Fin 4, x ≠ 2164260812#32+BitVec.ofNat 32 j.val := by
      intro j
      have hj := j.isLt
      have ha : (0x80ffeb90 : Word)+BitVec.ofNat 32 5180 = 2164260812#32 := by decide +kernel
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hx ⟨5180+j.val,by omega⟩
    rw [write_frame _ _ _ x .w hr14]
    have hr13 : ∀ j : Fin 4, x ≠ 2164260816#32+BitVec.ofNat 32 j.val := by
      intro j
      have hj := j.isLt
      have ha : (0x80ffeb90 : Word)+BitVec.ofNat 32 5184 = 2164260816#32 := by decide +kernel
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hx ⟨5184+j.val,by omega⟩
    rw [write_frame _ _ _ x .w hr13]
    have hr12 : ∀ j : Fin 4, x ≠ 2164260820#32+BitVec.ofNat 32 j.val := by
      intro j
      have hj := j.isLt
      have ha : (0x80ffeb90 : Word)+BitVec.ofNat 32 5188 = 2164260820#32 := by decide +kernel
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hx ⟨5188+j.val,by omega⟩
    rw [write_frame _ _ _ x .w hr12]
    have hr11 : ∀ j : Fin 4, x ≠ 2164260824#32+BitVec.ofNat 32 j.val := by
      intro j
      have hj := j.isLt
      have ha : (0x80ffeb90 : Word)+BitVec.ofNat 32 5192 = 2164260824#32 := by decide +kernel
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hx ⟨5192+j.val,by omega⟩
    rw [write_frame _ _ _ x .w hr11]
    have hr10 : ∀ j : Fin 4, x ≠ 2164260828#32+BitVec.ofNat 32 j.val := by
      intro j
      have hj := j.isLt
      have ha : (0x80ffeb90 : Word)+BitVec.ofNat 32 5196 = 2164260828#32 := by decide +kernel
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hx ⟨5196+j.val,by omega⟩
    rw [write_frame _ _ _ x .w hr10]
    have hr9 : ∀ j : Fin 4, x ≠ 2164260832#32+BitVec.ofNat 32 j.val := by
      intro j
      have hj := j.isLt
      have ha : (0x80ffeb90 : Word)+BitVec.ofNat 32 5200 = 2164260832#32 := by decide +kernel
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hx ⟨5200+j.val,by omega⟩
    rw [write_frame _ _ _ x .w hr9]
    have hr8 : ∀ j : Fin 4, x ≠ 2164260836#32+BitVec.ofNat 32 j.val := by
      intro j
      have hj := j.isLt
      have ha : (0x80ffeb90 : Word)+BitVec.ofNat 32 5204 = 2164260836#32 := by decide +kernel
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hx ⟨5204+j.val,by omega⟩
    rw [write_frame _ _ _ x .w hr8]
    have hr7 : ∀ j : Fin 4, x ≠ 2164260840#32+BitVec.ofNat 32 j.val := by
      intro j
      have hj := j.isLt
      have ha : (0x80ffeb90 : Word)+BitVec.ofNat 32 5208 = 2164260840#32 := by decide +kernel
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hx ⟨5208+j.val,by omega⟩
    rw [write_frame _ _ _ x .w hr7]
    have hr6 : ∀ j : Fin 4, x ≠ 2164260844#32+BitVec.ofNat 32 j.val := by
      intro j
      have hj := j.isLt
      have ha : (0x80ffeb90 : Word)+BitVec.ofNat 32 5212 = 2164260844#32 := by decide +kernel
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hx ⟨5212+j.val,by omega⟩
    rw [write_frame _ _ _ x .w hr6]
    have hr5 : ∀ j : Fin 4, x ≠ 2164260848#32+BitVec.ofNat 32 j.val := by
      intro j
      have hj := j.isLt
      have ha : (0x80ffeb90 : Word)+BitVec.ofNat 32 5216 = 2164260848#32 := by decide +kernel
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hx ⟨5216+j.val,by omega⟩
    rw [write_frame _ _ _ x .w hr5]
    have hr4 : ∀ j : Fin 4, x ≠ 2164260852#32+BitVec.ofNat 32 j.val := by
      intro j
      have hj := j.isLt
      have ha : (0x80ffeb90 : Word)+BitVec.ofNat 32 5220 = 2164260852#32 := by decide +kernel
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hx ⟨5220+j.val,by omega⟩
    rw [write_frame _ _ _ x .w hr4]
    have hr3 : ∀ j : Fin 4, x ≠ 2164260856#32+BitVec.ofNat 32 j.val := by
      intro j
      have hj := j.isLt
      have ha : (0x80ffeb90 : Word)+BitVec.ofNat 32 5224 = 2164260856#32 := by decide +kernel
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hx ⟨5224+j.val,by omega⟩
    rw [write_frame _ _ _ x .w hr3]
    have hr2 : ∀ j : Fin 4, x ≠ 2164260860#32+BitVec.ofNat 32 j.val := by
      intro j
      have hj := j.isLt
      have ha : (0x80ffeb90 : Word)+BitVec.ofNat 32 5228 = 2164260860#32 := by decide +kernel
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,ha] using hx ⟨5228+j.val,by omega⟩
    rw [write_frame _ _ _ x .w hr2]
  all_goals simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,Core.wr_get]

end E5R.Thermostat.Init
