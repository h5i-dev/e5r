import Projects.thermostat.Upper
import Projects.thermostat.Scratch
import Projects.thermostat.KernelCode
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.RelayPatch
open E5R E5R.Thermostat

def result (ram : Word → BitVec 8) (src sp : Word) (idx : BitVec 8) (on : Bool) : Word → BitVec 8 :=
  ramPut (Scratch.copyWords ram ram src (sp+24#32)) ((sp+24#32)+BitVec.ofNat 32 idx.toNat) (Encoding.boolByte on)

theorem contract_full (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot) (idx : BitVec 8) (on : Bool)
    (hp : c.pc = 0x800001be) (hidx : c.get 11 = BitVec.ofNat 32 idx.toNat) (hi : idx.toNat < 4)
    (hs : Encoding.SnapshotAt ram (c.get 12) s) (hstate : Memory.Block B (c.get 12) 10)
    (haState : (c.get 12).toNat % 2 = 0) (hstack : Memory.Block B (c.get 2) 64)
    (haStack : (c.get 2).toNat % 4 = 0) (honRam : B.inRam (c.get 13+2#32) 1 = true)
    (hon : ram (c.get 13+2#32) = Encoding.boolByte on) :
    ∃ d, DetSteps B img 16 ⟨c,ram⟩ ⟨d,result ram (c.get 12) (c.get 2) idx on⟩ ∧
      d.pc = 0x800001f4 ∧ d.get 2 = c.get 2 ∧ d.get 10 = c.get 10 ∧ d.sameCsr c ∧
      Encoding.SnapshotAt (result ram (c.get 12) (c.get 2) idx on) (c.get 2+24#32) (Scratch.patched s idx on) ∧ Upper.Frame c d := by
  let state := c.get 12
  let cmd := c.get 13
  let sp := c.get 2
  let tmp := sp+24#32
  let ix := BitVec.ofNat 32 idx.toNat
  let von : Word := if on then 1 else 0
  let vtemp := extend .h false (ramRead ram (state+6#32) .h)
  let vhi := extend .h false (ramRead ram (state+2#32) .h)
  let vsp := extend .h false (ramRead ram (state+4#32) .h)
  let vlo := extend .h false (ramRead ram (state+0#32) .h)
  let vhm := extend .h true (ramRead ram (state+8#32) .h)
  let wlo := ramRead ram (state+0#32) .w
  let whi := ramRead ram (state+4#32) .w
  let r0 := ram
  let c1 := c.wr 14 (vtemp) 0x800001c2
  let c2 := c1.wr 15 (vhi) 0x800001c6
  let c3 := c2.wr 16 (vsp) 0x800001ca
  let c4 := c3.wr 17 (vlo) 0x800001ce
  let c5 := c4.wr 12 (vhm) 0x800001d2
  let c6 := c5.wr 5 (tmp) 0x800001d6
  let c7 := c6.wr 13 (von) 0x800001da
  let c8 := c7.wr 11 (tmp+ix) 0x800001dc
  let c9 := c8.wr 14 (vtemp <<< 16) 0x800001de
  let c10 := c9.wr 15 (vhi <<< 16) 0x800001e0
  let c11 := c10.wr 14 (whi) 0x800001e4
  let c12 := c11.wr 15 (wlo) 0x800001e8
  let r1 := ramWrite r0 (sp+24#32) (wlo) .w
  let c13 := c12.goto 0x800001ea
  let r2 := ramWrite r1 (sp+28#32) (whi) .w
  let c14 := c13.goto 0x800001ec
  let r3 := ramWrite r2 (sp+32#32) (vhm) .h
  let c15 := c14.goto 0x800001f0
  let r4 := ramPut r3 (tmp+ix) (Encoding.boolByte on)
  let c16 := c15.goto 0x800001f4
  have s0 : DetStep B img ⟨c,r0⟩ ⟨c1,r0⟩ := by
    have ha : c.get 12 = state := by simp [state,Core.wr_get_ne]
    have hm : B.inRam (state+6#32) 2 = true := Memory.block_access (B := B) (p := state) (n := 10) (off := 6) (width := 2) hstate (by decide) (by decide)
    have hal : (state+6#32).toNat % 2 = 0 := Memory.half_aligned state 3 haState
    refine detStep_of (by rw [hp];decide) (by rw [hp]; exact d2147484094) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := state+6#32) o hal hm]
    rw [hp]
    rfl
  have s1 : DetStep B img ⟨c1,r0⟩ ⟨c2,r0⟩ := by
    have ha : c1.get 12 = state := by simp [c1,state,Core.wr_get_ne]
    have hm : B.inRam (state+2#32) 2 = true := Memory.block_access (B := B) (p := state) (n := 10) (off := 2) (width := 2) hstate (by decide) (by decide)
    have hal : (state+2#32).toNat % 2 = 0 := Memory.half_aligned state 1 haState
    refine detStep_of (by change (0x800001c2 : Word).getLsbD 0 = false;decide) (by exact d2147484098) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := state+2#32) o hal hm]
    rfl
  have s2 : DetStep B img ⟨c2,r0⟩ ⟨c3,r0⟩ := by
    have ha : c2.get 12 = state := by simp [c2,c1,state,Core.wr_get_ne]
    have hm : B.inRam (state+4#32) 2 = true := Memory.block_access (B := B) (p := state) (n := 10) (off := 4) (width := 2) hstate (by decide) (by decide)
    have hal : (state+4#32).toNat % 2 = 0 := Memory.half_aligned state 2 haState
    refine detStep_of (by change (0x800001c6 : Word).getLsbD 0 = false;decide) (by exact d2147484102) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := state+4#32) o hal hm]
    rfl
  have s3 : DetStep B img ⟨c3,r0⟩ ⟨c4,r0⟩ := by
    have ha : c3.get 12 = state := by simp [c3,c2,c1,state,Core.wr_get_ne]
    have hm : B.inRam (state+0#32) 2 = true := Memory.block_access (B := B) (p := state) (n := 10) (off := 0) (width := 2) hstate (by decide) (by decide)
    have hal : (state+0#32).toNat % 2 = 0 := Memory.half_aligned state 0 haState
    refine detStep_of (by change (0x800001ca : Word).getLsbD 0 = false;decide) (by exact d2147484106) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := state+0#32) o hal hm]
    rfl
  have s4 : DetStep B img ⟨c4,r0⟩ ⟨c5,r0⟩ := by
    have ha : c4.get 12 = state := by simp [c4,c3,c2,c1,state,Core.wr_get_ne]
    have hm : B.inRam (state+8#32) 2 = true := Memory.block_access (B := B) (p := state) (n := 10) (off := 8) (width := 2) hstate (by decide) (by decide)
    have hal : (state+8#32).toNat % 2 = 0 := Memory.half_aligned state 4 haState
    refine detStep_of (by change (0x800001ce : Word).getLsbD 0 = false;decide) (by exact d2147484110) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := state+8#32) o hal hm]
    rfl
  have s5 : DetStep B img ⟨c5,r0⟩ ⟨c6,r0⟩ := by
    refine detStep_of (by change (0x800001d2 : Word).getLsbD 0 = false;decide) (by exact d2147484114) fun o => ?_
    have ha : c5.get 2 = sp := by simp [c5,c4,c3,c2,c1,sp,Core.wr_get_ne]
    rw [exec_opimm,ha]
    rfl
  have s6 : DetStep B img ⟨c6,r0⟩ ⟨c7,r0⟩ := by
    have ha : c6.get 13 = cmd := by simp [c6,c5,c4,c3,c2,c1,cmd,Core.wr_get_ne]
    have hm : B.inRam (cmd+2#32) 1 = true := honRam
    have hal : (cmd+2#32).toNat % 1 = 0 := Nat.mod_one _
    refine detStep_of (by change (0x800001d6 : Word).getLsbD 0 = false;decide) (by exact d2147484118) fun o => ?_
    rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .b) (a := cmd+2#32) o hal hm]
    have hv : extend .b false (ramRead ram (cmd+2#32) .b) = von := by
      rw [Memory.load_byte,hon]
      cases on <;> rfl
    rw [hv]
    rfl
  have s7 : DetStep B img ⟨c7,r0⟩ ⟨c8,r0⟩ := by
    refine detStep_of (by change (0x800001da : Word).getLsbD 0 = false;decide) (by exact d2147484122) fun o => ?_
    have hv1 : c7.get 11 = ix := by simp [c7,c6,c5,c4,c3,c2,c1,ix,Core.wr_get_ne,hidx]
    have hv2 : c7.get 5 = tmp := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    rw [exec_op,hv1,hv2]
    have hc : alu .add ix tmp = tmp+ix := BitVec.add_comm _ _
    rw [hc]
    rfl
  have s8 : DetStep B img ⟨c8,r0⟩ ⟨c9,r0⟩ := by
    refine detStep_of (by change (0x800001dc : Word).getLsbD 0 = false;decide) (by exact d2147484124) fun o => ?_
    have hv : c8.get 14 = vtemp := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    rw [exec_opimm,hv]
    rfl
  have s9 : DetStep B img ⟨c9,r0⟩ ⟨c10,r0⟩ := by
    refine detStep_of (by change (0x800001de : Word).getLsbD 0 = false;decide) (by exact d2147484126) fun o => ?_
    have hv : c9.get 15 = vhi := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    rw [exec_opimm,hv]
    rfl
  have s10 : DetStep B img ⟨c10,r0⟩ ⟨c11,r0⟩ := by
    refine detStep_of (by change (0x800001e0 : Word).getLsbD 0 = false;decide) (by exact d2147484128) fun o => ?_
    have hv1 : c10.get 14 = vtemp <<< 16 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    have hv2 : c10.get 16 = vsp := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    have hpack : alu .or (vtemp <<< 16) (vsp) = whi := by
      simpa [alu,vtemp,vsp,whi,BitVec.add_assoc] using Scratch.pack_word ram (state+4#32)
    rw [exec_op,hv1,hv2,hpack]
    rfl
  have s11 : DetStep B img ⟨c11,r0⟩ ⟨c12,r0⟩ := by
    refine detStep_of (by change (0x800001e4 : Word).getLsbD 0 = false;decide) (by exact d2147484132) fun o => ?_
    have hv1 : c11.get 15 = vhi <<< 16 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    have hv2 : c11.get 17 = vlo := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    have hpack : alu .or (vhi <<< 16) (vlo) = wlo := by
      simpa [alu,vhi,vlo,wlo,BitVec.add_assoc] using Scratch.pack_word ram state
    rw [exec_op,hv1,hv2,hpack]
    rfl
  have s12 : DetStep B img ⟨c12,r0⟩ ⟨c13,r1⟩ := by
    have ha : c12.get 2 = sp := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,sp,tmp,ix,hidx]
    have hv : c12.get 15 = wlo := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    have hm : B.inRam (sp+24#32) 4 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 24) (width := 4) hstack (by decide) (by decide)
    have hal : (sp+24#32).toNat % 4 = 0 := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat]
      have hh := hstack.2.2
      have hb := (c.get 2).isLt
      dsimp only [sp] at *
      omega
    refine detStep_of (by change (0x800001e8 : Word).getLsbD 0 = false;decide) (by exact d2147484136) fun o => ?_
    rw [exec_store,ha,hv]
    rw [interp_store_ram (B := B) (img := img) (w := .w) (a := sp+24#32) (v := wlo) o hal hm]
    rfl
  have s13 : DetStep B img ⟨c13,r1⟩ ⟨c14,r2⟩ := by
    have ha : c13.get 2 = sp := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,sp,tmp,ix,hidx]
    have hv : c13.get 14 = whi := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    have hm : B.inRam (sp+28#32) 4 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 28) (width := 4) hstack (by decide) (by decide)
    have hal : (sp+28#32).toNat % 4 = 0 := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat]
      have hh := hstack.2.2
      have hb := (c.get 2).isLt
      dsimp only [sp] at *
      omega
    refine detStep_of (by change (0x800001ea : Word).getLsbD 0 = false;decide) (by exact d2147484138) fun o => ?_
    rw [exec_store,ha,hv]
    rw [interp_store_ram (B := B) (img := img) (w := .w) (a := sp+28#32) (v := whi) o hal hm]
    rfl
  have s14 : DetStep B img ⟨c14,r2⟩ ⟨c15,r3⟩ := by
    have ha : c14.get 2 = sp := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,sp,tmp,ix,hidx]
    have hv : c14.get 12 = vhm := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    have hm : B.inRam (sp+32#32) 2 = true := Memory.block_access (B := B) (p := sp) (n := 64) (off := 32) (width := 2) hstack (by decide) (by decide)
    have hal : (sp+32#32).toNat % 2 = 0 := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat]
      have hh := hstack.2.2
      have hb := (c.get 2).isLt
      dsimp only [sp] at *
      omega
    refine detStep_of (by change (0x800001ec : Word).getLsbD 0 = false;decide) (by exact d2147484140) fun o => ?_
    rw [exec_store,ha,hv]
    rw [interp_store_ram (B := B) (img := img) (w := .h) (a := sp+32#32) (v := vhm) o hal hm]
    rfl
  have s15 : DetStep B img ⟨c15,r3⟩ ⟨c16,r4⟩ := by
    have ha : c15.get 11 = tmp+ix := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,sp,tmp,ix,hidx]
    have hv : c15.get 13 = von := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
    have hm : B.inRam (tmp+ix) 1 = true := by
      have hh := Memory.block_access (B := B) (p := sp) (n := 64) (off := 24+idx.toNat) (width := 1) hstack (by decide) (by omega)
      simpa only [tmp,ix,BitVec.ofNat_add,BitVec.add_assoc] using hh
    have hal : (tmp+ix).toNat % 1 = 0 := Nat.mod_one _
    refine detStep_of (by change (0x800001f0 : Word).getLsbD 0 = false;decide) (by exact d2147484144) fun o => ?_
    rw [exec_store,ha,hv]
    rw [BitVec.add_zero]
    rw [interp_store_ram (B := B) (img := img) (w := .b) (a := tmp+ix) (v := von) o hal hm]
    have hb : byteOf von 0 = Encoding.boolByte on := Fields.bool_byte on
    simp only [ramWrite,hb]
    rfl
  have hr : r4 = result ram state sp idx on := by
    simp [r4,r3,r2,r1,r0,result,Scratch.copyWords,tmp,ix,vhm,wlo,whi,BitVec.add_assoc]
  refine ⟨c16,?_,rfl,?_,?_,?_,?_,?_⟩
  · rw [← hr]
    exact .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.step s13 (.step s14 (.single s15)))))))))))))))
  · simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
  · simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
  · rfl
  · exact Scratch.patch_snapshot (Scratch.copyWords ram ram state tmp) tmp s idx on
      (Scratch.copy_snapshot ram ram state tmp s hs) hi

  · intro r hr
    have hn0 := Upper.ne_low r hr 0 (by decide)
    have hn1 := Upper.ne_low r hr 1 (by decide)
    have hn2 := Upper.ne_low r hr 2 (by decide)
    have hn3 := Upper.ne_low r hr 3 (by decide)
    have hn4 := Upper.ne_low r hr 4 (by decide)
    have hn5 := Upper.ne_low r hr 5 (by decide)
    have hn6 := Upper.ne_low r hr 6 (by decide)
    have hn7 := Upper.ne_low r hr 7 (by decide)
    have hn8 := Upper.ne_low r hr 8 (by decide)
    have hn9 := Upper.ne_low r hr 9 (by decide)
    have hn10 := Upper.ne_low r hr 10 (by decide)
    have hn11 := Upper.ne_low r hr 11 (by decide)
    have hn12 := Upper.ne_low r hr 12 (by decide)
    have hn13 := Upper.ne_low r hr 13 (by decide)
    have hn14 := Upper.ne_low r hr 14 (by decide)
    have hn15 := Upper.ne_low r hr 15 (by decide)
    have hn16 := Upper.ne_low r hr 16 (by decide)
    have hn17 := Upper.ne_low r hr 17 (by decide)
    have hn18 := Upper.ne_low r hr 18 (by decide)
    have hn19 := Upper.ne_low r hr 19 (by decide)
    have hn20 := Upper.ne_low r hr 20 (by decide)
    have hn21 := Upper.ne_low r hr 21 (by decide)
    simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,hn0,hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8,hn9,hn10,hn11,hn12,hn13,hn14,hn15,hn16,hn17,hn18,hn19,hn20,hn21]


theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot) (idx : BitVec 8) (on : Bool)
    (hp : c.pc = 0x800001be) (hidx : c.get 11 = BitVec.ofNat 32 idx.toNat) (hi : idx.toNat < 4)
    (hs : Encoding.SnapshotAt ram (c.get 12) s) (hstate : Memory.Block B (c.get 12) 10)
    (haState : (c.get 12).toNat % 2 = 0) (hstack : Memory.Block B (c.get 2) 64)
    (haStack : (c.get 2).toNat % 4 = 0) (honRam : B.inRam (c.get 13+2#32) 1 = true)
    (hon : ram (c.get 13+2#32) = Encoding.boolByte on) :
    ∃ d, DetSteps B img 16 ⟨c,ram⟩ ⟨d,result ram (c.get 12) (c.get 2) idx on⟩ ∧
      d.pc = 0x800001f4 ∧ d.get 2 = c.get 2 ∧ d.get 10 = c.get 10 ∧ d.sameCsr c ∧
      Encoding.SnapshotAt (result ram (c.get 12) (c.get 2) idx on) (c.get 2+24#32) (Scratch.patched s idx on) := by
  obtain ⟨d,hr,hpc,hsp,hout,hcsr,hsnap,_⟩ := contract_full B c ram s idx on hp hidx hi hs hstate haState hstack haStack honRam hon
  exact ⟨d,hr,hpc,hsp,hout,hcsr,hsnap⟩

end E5R.Thermostat.RelayPatch
