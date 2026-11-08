-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.Prepare
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.Prepare
theorem contract_full_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (kind : Fin 3)
    (s : Spec.Snapshot) (m : Spec.Mode) (dc : BitVec 16)
    (hp : c.pc = start kind) (hs : Encoding.SnapshotAt ram (c.get 12) s)
    (hstate : Memory.Block B (c.get 12) 10) (hal : (c.get 12).toNat % 2 = 0)
    (hcmd : Input B c ram kind m dc) :
    ∃ n ch, n ≤ 11 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨ch,ram⟩ ∧
      HeaterReady.Ready ch (next kind s m dc) kind (c.get 10) ∧
      ch.get 2 = c.get 2 ∧ ch.sameCsr c ∧ Upper.Frame c ch := by
  have hi := kind.isLt
  have hc : kind.val = 0 ∨ kind.val = 1 ∨ kind.val = 2 := by omega
  rcases hc with hkind|hkind|hkind
  · have hp' : c.pc = 0x8000007e := by simpa [start,hkind] using hp
    simp only [Input,hkind] at hcmd
    let state := c.get 12
    let cmd := c.get 13
    let out := c.get 10
    let vlo := extend .h false (ramRead ram (state+0#32) .h)
    let vhi := extend .h false (ramRead ram (state+2#32) .h)
    let vsp := s.setpoint.signExtend 32
    let vt := s.temp.signExtend 32
    let vm := Fields.modeWord m
    let c1 := c.wr 8 (vm) 0x80000082
    let c2 := c1.wr 19 (vlo) 0x80000086
    let c3 := c2.wr 20 (vhi) 0x8000008a
    let c4 := c3.wr 9 (vsp) 0x8000008e
    let c5 := c4.wr 18 (vt) 0x80000092
    let c6 := c5.wr 21 (out) 0x80000094
    let c7 := c6.wr 10 (vm) 0x80000096
    let c8 := c7.wr 11 (vt) 0x80000098
    let c9 := c8.wr 12 (vsp) 0x8000009a
    let c10 := c9.wr 1 (0x8000009a#32) 0x8000009e
    let c11 := c10.wr 1 (0x800000a2#32) 0x80000036
    have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
      have ha : c.get 13 = cmd := by simp [cmd,Core.wr_get_ne]
      have hm : B.inRam (cmd+1#32) 1 = true := hcmd.1
      have hal' : (cmd+1#32).toNat % 1 = 0 := Nat.mod_one _
      refine QuietDet.step_of (by rw [hp'];decide) (by rw [hp']; exact d2147483774) fun o => ?_
      rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .b) (a := cmd+1#32) o hal' hm]
      have hv : extend .b false (ramRead ram (cmd+1#32) .b) = Fields.modeWord m := by
        rw [Memory.load_byte,hcmd.2]
        cases m <;> rfl
      rw [hv]
      rw [hp']
      rfl
    have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
      have ha : c1.get 12 = state := by simp [c1,state,Core.wr_get_ne]
      have hm : B.inRam (state+0#32) 2 = true := Memory.block_access (B := B) (p := state) (n := 10) (off := 0) (width := 2) hstate (by decide) (by decide)
      have hal' : (state+0#32).toNat % 2 = 0 := Memory.half_aligned state 0 hal
      refine QuietDet.step_of (by change (0x80000082 : Word).getLsbD 0 = false;decide) (by exact d2147483778) fun o => ?_
      rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := state+0#32) o hal' hm]
      rfl
    have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
      have ha : c2.get 12 = state := by simp [c2,c1,state,Core.wr_get_ne]
      have hm : B.inRam (state+2#32) 2 = true := Memory.block_access (B := B) (p := state) (n := 10) (off := 2) (width := 2) hstate (by decide) (by decide)
      have hal' : (state+2#32).toNat % 2 = 0 := Memory.half_aligned state 1 hal
      refine QuietDet.step_of (by change (0x80000086 : Word).getLsbD 0 = false;decide) (by exact d2147483782) fun o => ?_
      rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := state+2#32) o hal' hm]
      rfl
    have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
      have ha : c3.get 12 = state := by simp [c3,c2,c1,state,Core.wr_get_ne]
      have hm : B.inRam (state+4#32) 2 = true := Memory.block_access (B := B) (p := state) (n := 10) (off := 4) (width := 2) hstate (by decide) (by decide)
      have hal' : (state+4#32).toNat % 2 = 0 := Memory.half_aligned state 2 hal
      refine QuietDet.step_of (by change (0x8000008a : Word).getLsbD 0 = false;decide) (by exact d2147483786) fun o => ?_
      rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := state+4#32) o hal' hm]
      rw [Fields.setpoint ram state s hs]
      rfl
    have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
      have ha : c4.get 12 = state := by simp [c4,c3,c2,c1,state,Core.wr_get_ne]
      have hm : B.inRam (state+6#32) 2 = true := Memory.block_access (B := B) (p := state) (n := 10) (off := 6) (width := 2) hstate (by decide) (by decide)
      have hal' : (state+6#32).toNat % 2 = 0 := Memory.half_aligned state 3 hal
      refine QuietDet.step_of (by change (0x8000008e : Word).getLsbD 0 = false;decide) (by exact d2147483790) fun o => ?_
      rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := state+6#32) o hal' hm]
      rw [Fields.temp ram state s hs]
      rfl
    have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
      refine QuietDet.step_of (by change (0x80000092 : Word).getLsbD 0 = false;decide) (by exact d2147483794) fun o => ?_
      have hv : c5.get 10 = out := by simp [c5,c4,c3,c2,c1,Core.wr_get,out]
      rw [exec_op,Core.get_zero,hv,zero_add]
      rfl
    have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
      refine QuietDet.step_of (by change (0x80000094 : Word).getLsbD 0 = false;decide) (by exact d2147483796) fun o => ?_
      have hv : c6.get 8 = vm := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get,out]
      rw [exec_op,Core.get_zero,hv,zero_add]
      rfl
    have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
      refine QuietDet.step_of (by change (0x80000096 : Word).getLsbD 0 = false;decide) (by exact d2147483798) fun o => ?_
      have hv : c7.get 18 = vt := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get,out]
      rw [exec_op,Core.get_zero,hv,zero_add]
      rfl
    have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
      refine QuietDet.step_of (by change (0x80000098 : Word).getLsbD 0 = false;decide) (by exact d2147483800) fun o => ?_
      have hv : c8.get 9 = vsp := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,out]
      rw [exec_op,Core.get_zero,hv,zero_add]
      rfl
    have s9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
      refine QuietDet.step_of (by change (0x8000009a : Word).getLsbD 0 = false;decide) (by exact d2147483802) fun o => ?_
      rw [exec_auipc]
      rfl
    have s10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
      refine QuietDet.step_of (by change (0x8000009e : Word).getLsbD 0 = false;decide) (by exact d2147483806) fun o => ?_
      have hv : c10.get 1 = 0x8000009a#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
      have ht : (0x8000009a#32+0xffffff9c#32) &&& ~~~1 = 0x80000036#32 := by decide +kernel
      rw [exec_jalr,hv,ht,jump_ok _ 0x80000036#32 (by decide)]
      rfl
    refine ⟨11,c11,by decide,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.single s10)))))))))),?_,?_,?_,?_⟩
    · constructor
      · rfl
      · simp [next,Spec.settle,WriteTwo.start,hkind,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,out,vm,vsp,vt]
      · simp [next,Spec.settle,WriteTwo.start,hkind,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,out,vm,vsp,vt]
      · simp [next,Spec.settle,WriteTwo.start,hkind,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,out,vm,vsp,vt]
      · simp [next,Spec.settle,WriteTwo.start,hkind,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,out,vm,vsp,vt]
      · simp [next,Spec.settle,WriteTwo.start,hkind,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,out,vm,vsp,vt]
      · rfl
      · intro i hi
        have hx := i.isLt
        have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
          i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 := by omega
        have hb0 := hs ⟨0,by decide⟩
        change ram (state+0#32) = Encoding.boolByte (s.relays 0) at hb0
        rw [BitVec.add_zero] at hb0
        have hb1 := hs ⟨1,by decide⟩
        change ram (state+1#32) = Encoding.boolByte (s.relays 1) at hb1
        have hb2 := hs ⟨2,by decide⟩
        change ram (state+2#32) = Encoding.boolByte (s.relays 2) at hb2
        have hb3 := hs ⟨3,by decide⟩
        change ram (state+3#32) = Encoding.boolByte (s.relays 3) at hb3
        rcases hc with hx|hx|hx|hx|hx|hx|hx|hx|hx|hx
        all_goals first
        | exact False.elim (hi hx)
        | simp [WriteTwo.regs,WriteTwo.byte,next,Spec.settle,hkind,hx,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,
            vlo,vhi,vsp,vt,vm,out,Fields.signed_byte0,Fields.signed_byte1,Fields.mode_byte,
            Fields.unsigned_half_byte0,Fields.unsigned_half_byte1,Encoding.snapshotByte,
            BitVec.add_assoc,hb0,hb1,hb2,hb3,hcmd]
    · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    · rfl
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
      simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,hn0,hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8,hn9,hn10,hn11,hn12,hn13,hn14,hn15,hn16,hn17,hn18,hn19,hn20,hn21]

  · have hp' : c.pc = 0x80000158 := by simpa [start,hkind] using hp
    simp only [Input,hkind] at hcmd
    let state := c.get 12
    let cmd := c.get 13
    let out := c.get 10
    let vlo := extend .h false (ramRead ram (state+0#32) .h)
    let vhi := extend .h false (ramRead ram (state+2#32) .h)
    let vsp := s.setpoint.signExtend 32
    let vt := dc.signExtend 32
    let vm := Fields.modeWord s.mode
    let c1 := c.wr 19 (vlo) 0x8000015c
    let c2 := c1.wr 20 (vhi) 0x80000160
    let c3 := c2.wr 8 (vsp) 0x80000164
    let c4 := c3.wr 9 (vm) 0x80000168
    let c5 := c4.wr 18 (vt) 0x8000016c
    let c6 := c5.wr 21 (out) 0x8000016e
    let c7 := c6.wr 10 (vm) 0x80000170
    let c8 := c7.wr 11 (vt) 0x80000172
    let c9 := c8.wr 12 (vsp) 0x80000174
    let c10 := c9.wr 1 (0x80000174#32) 0x80000178
    let c11 := c10.wr 1 (0x8000017c#32) 0x80000036
    have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
      have ha : c.get 12 = state := by simp [state,Core.wr_get_ne]
      have hm : B.inRam (state+0#32) 2 = true := Memory.block_access (B := B) (p := state) (n := 10) (off := 0) (width := 2) hstate (by decide) (by decide)
      have hal' : (state+0#32).toNat % 2 = 0 := Memory.half_aligned state 0 hal
      refine QuietDet.step_of (by rw [hp'];decide) (by rw [hp']; exact d2147483992) fun o => ?_
      rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := state+0#32) o hal' hm]
      rw [hp']
      rfl
    have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
      have ha : c1.get 12 = state := by simp [c1,state,Core.wr_get_ne]
      have hm : B.inRam (state+2#32) 2 = true := Memory.block_access (B := B) (p := state) (n := 10) (off := 2) (width := 2) hstate (by decide) (by decide)
      have hal' : (state+2#32).toNat % 2 = 0 := Memory.half_aligned state 1 hal
      refine QuietDet.step_of (by change (0x8000015c : Word).getLsbD 0 = false;decide) (by exact d2147483996) fun o => ?_
      rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := state+2#32) o hal' hm]
      rfl
    have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
      have ha : c2.get 12 = state := by simp [c2,c1,state,Core.wr_get_ne]
      have hm : B.inRam (state+4#32) 2 = true := Memory.block_access (B := B) (p := state) (n := 10) (off := 4) (width := 2) hstate (by decide) (by decide)
      have hal' : (state+4#32).toNat % 2 = 0 := Memory.half_aligned state 2 hal
      refine QuietDet.step_of (by change (0x80000160 : Word).getLsbD 0 = false;decide) (by exact d2147484000) fun o => ?_
      rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := state+4#32) o hal' hm]
      rw [Fields.setpoint ram state s hs]
      rfl
    have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
      have ha : c3.get 12 = state := by simp [c3,c2,c1,state,Core.wr_get_ne]
      have hm : B.inRam (state+9#32) 1 = true := Memory.block_access (B := B) (p := state) (n := 10) (off := 9) (width := 1) hstate (by decide) (by decide)
      have hal' : (state+9#32).toNat % 1 = 0 := Nat.mod_one _
      refine QuietDet.step_of (by change (0x80000164 : Word).getLsbD 0 = false;decide) (by exact d2147484004) fun o => ?_
      rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .b) (a := state+9#32) o hal' hm]
      rw [Fields.mode ram state s hs]
      rfl
    have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
      have ha : c4.get 13 = cmd := by simp [c4,c3,c2,c1,cmd,Core.wr_get_ne]
      have hm : B.inRam (cmd+2#32) 2 = true := hcmd.2.1
      have hal' : (cmd+2#32).toNat % 2 = 0 := hcmd.1
      refine QuietDet.step_of (by change (0x80000168 : Word).getLsbD 0 = false;decide) (by exact d2147484008) fun o => ?_
      rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := cmd+2#32) o hal' hm]
      rw [hcmd.2.2]
      rfl
    have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
      refine QuietDet.step_of (by change (0x8000016c : Word).getLsbD 0 = false;decide) (by exact d2147484012) fun o => ?_
      have hv : c5.get 10 = out := by simp [c5,c4,c3,c2,c1,Core.wr_get,out]
      rw [exec_op,Core.get_zero,hv,zero_add]
      rfl
    have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
      refine QuietDet.step_of (by change (0x8000016e : Word).getLsbD 0 = false;decide) (by exact d2147484014) fun o => ?_
      have hv : c6.get 9 = vm := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get,out]
      rw [exec_op,Core.get_zero,hv,zero_add]
      rfl
    have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
      refine QuietDet.step_of (by change (0x80000170 : Word).getLsbD 0 = false;decide) (by exact d2147484016) fun o => ?_
      have hv : c7.get 18 = vt := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get,out]
      rw [exec_op,Core.get_zero,hv,zero_add]
      rfl
    have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
      refine QuietDet.step_of (by change (0x80000172 : Word).getLsbD 0 = false;decide) (by exact d2147484018) fun o => ?_
      have hv : c8.get 8 = vsp := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,out]
      rw [exec_op,Core.get_zero,hv,zero_add]
      rfl
    have s9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
      refine QuietDet.step_of (by change (0x80000174 : Word).getLsbD 0 = false;decide) (by exact d2147484020) fun o => ?_
      rw [exec_auipc]
      rfl
    have s10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
      refine QuietDet.step_of (by change (0x80000178 : Word).getLsbD 0 = false;decide) (by exact d2147484024) fun o => ?_
      have hv : c10.get 1 = 0x80000174#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
      have ht : (0x80000174#32+0xfffffec2#32) &&& ~~~1 = 0x80000036#32 := by decide +kernel
      rw [exec_jalr,hv,ht,jump_ok _ 0x80000036#32 (by decide)]
      rfl
    refine ⟨11,c11,by decide,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.single s10)))))))))),?_,?_,?_,?_⟩
    · constructor
      · rfl
      · simp [next,Spec.settle,WriteTwo.start,hkind,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,out,vm,vsp,vt]
      · simp [next,Spec.settle,WriteTwo.start,hkind,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,out,vm,vsp,vt]
      · simp [next,Spec.settle,WriteTwo.start,hkind,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,out,vm,vsp,vt]
      · simp [next,Spec.settle,WriteTwo.start,hkind,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,out,vm,vsp,vt]
      · simp [next,Spec.settle,WriteTwo.start,hkind,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,out,vm,vsp,vt]
      · rfl
      · intro i hi
        have hx := i.isLt
        have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
          i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 := by omega
        have hb0 := hs ⟨0,by decide⟩
        change ram (state+0#32) = Encoding.boolByte (s.relays 0) at hb0
        rw [BitVec.add_zero] at hb0
        have hb1 := hs ⟨1,by decide⟩
        change ram (state+1#32) = Encoding.boolByte (s.relays 1) at hb1
        have hb2 := hs ⟨2,by decide⟩
        change ram (state+2#32) = Encoding.boolByte (s.relays 2) at hb2
        have hb3 := hs ⟨3,by decide⟩
        change ram (state+3#32) = Encoding.boolByte (s.relays 3) at hb3
        rcases hc with hx|hx|hx|hx|hx|hx|hx|hx|hx|hx
        all_goals first
        | exact False.elim (hi hx)
        | simp [WriteTwo.regs,WriteTwo.byte,next,Spec.settle,hkind,hx,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,
            vlo,vhi,vsp,vt,vm,out,Fields.signed_byte0,Fields.signed_byte1,Fields.mode_byte,
            Fields.unsigned_half_byte0,Fields.unsigned_half_byte1,Encoding.snapshotByte,
            BitVec.add_assoc,hb0,hb1,hb2,hb3,hcmd]
    · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    · rfl
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
      simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,hn0,hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8,hn9,hn10,hn11,hn12,hn13,hn14,hn15,hn16,hn17,hn18,hn19,hn20,hn21]

  · have hp' : c.pc = 0x8000027a := by simpa [start,hkind] using hp
    simp only [Input,hkind] at hcmd
    let state := c.get 12
    let cmd := c.get 13
    let out := c.get 10
    let vlo := extend .h false (ramRead ram (state+0#32) .h)
    let vhi := extend .h false (ramRead ram (state+2#32) .h)
    let vsp := dc.signExtend 32
    let vt := s.temp.signExtend 32
    let vm := Fields.modeWord s.mode
    let c1 := c.wr 19 (vlo) 0x8000027e
    let c2 := c1.wr 20 (vhi) 0x80000282
    let c3 := c2.wr 9 (vt) 0x80000286
    let c4 := c3.wr 18 (vm) 0x8000028a
    let c5 := c4.wr 21 (out) 0x8000028c
    let c6 := c5.wr 10 (vm) 0x8000028e
    let c7 := c6.wr 11 (vt) 0x80000290
    let c8 := c7.wr 12 (vsp) 0x80000292
    let c9 := c8.wr 1 (0x80000292#32) 0x80000296
    let c10 := c9.wr 1 (0x8000029a#32) 0x80000036
    have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
      have ha : c.get 12 = state := by simp [state,Core.wr_get_ne]
      have hm : B.inRam (state+0#32) 2 = true := Memory.block_access (B := B) (p := state) (n := 10) (off := 0) (width := 2) hstate (by decide) (by decide)
      have hal' : (state+0#32).toNat % 2 = 0 := Memory.half_aligned state 0 hal
      refine QuietDet.step_of (by rw [hp'];decide) (by rw [hp']; exact d2147484282) fun o => ?_
      rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := state+0#32) o hal' hm]
      rw [hp']
      rfl
    have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
      have ha : c1.get 12 = state := by simp [c1,state,Core.wr_get_ne]
      have hm : B.inRam (state+2#32) 2 = true := Memory.block_access (B := B) (p := state) (n := 10) (off := 2) (width := 2) hstate (by decide) (by decide)
      have hal' : (state+2#32).toNat % 2 = 0 := Memory.half_aligned state 1 hal
      refine QuietDet.step_of (by change (0x8000027e : Word).getLsbD 0 = false;decide) (by exact d2147484286) fun o => ?_
      rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := state+2#32) o hal' hm]
      rfl
    have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
      have ha : c2.get 12 = state := by simp [c2,c1,state,Core.wr_get_ne]
      have hm : B.inRam (state+6#32) 2 = true := Memory.block_access (B := B) (p := state) (n := 10) (off := 6) (width := 2) hstate (by decide) (by decide)
      have hal' : (state+6#32).toNat % 2 = 0 := Memory.half_aligned state 3 hal
      refine QuietDet.step_of (by change (0x80000282 : Word).getLsbD 0 = false;decide) (by exact d2147484290) fun o => ?_
      rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .h) (a := state+6#32) o hal' hm]
      rw [Fields.temp ram state s hs]
      rfl
    have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
      have ha : c3.get 12 = state := by simp [c3,c2,c1,state,Core.wr_get_ne]
      have hm : B.inRam (state+9#32) 1 = true := Memory.block_access (B := B) (p := state) (n := 10) (off := 9) (width := 1) hstate (by decide) (by decide)
      have hal' : (state+9#32).toNat % 1 = 0 := Nat.mod_one _
      refine QuietDet.step_of (by change (0x80000286 : Word).getLsbD 0 = false;decide) (by exact d2147484294) fun o => ?_
      rw [exec_load,ha,interp_load_ram (B := B) (img := img) (w := .b) (a := state+9#32) o hal' hm]
      rw [Fields.mode ram state s hs]
      rfl
    have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
      refine QuietDet.step_of (by change (0x8000028a : Word).getLsbD 0 = false;decide) (by exact d2147484298) fun o => ?_
      have hv : c4.get 10 = out := by simp [c4,c3,c2,c1,Core.wr_get,out]
      rw [exec_op,Core.get_zero,hv,zero_add]
      rfl
    have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
      refine QuietDet.step_of (by change (0x8000028c : Word).getLsbD 0 = false;decide) (by exact d2147484300) fun o => ?_
      have hv : c5.get 18 = vm := by simp [c5,c4,c3,c2,c1,Core.wr_get,out]
      rw [exec_op,Core.get_zero,hv,zero_add]
      rfl
    have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
      refine QuietDet.step_of (by change (0x8000028e : Word).getLsbD 0 = false;decide) (by exact d2147484302) fun o => ?_
      have hv : c6.get 9 = vt := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get,out]
      rw [exec_op,Core.get_zero,hv,zero_add]
      rfl
    have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
      refine QuietDet.step_of (by change (0x80000290 : Word).getLsbD 0 = false;decide) (by exact d2147484304) fun o => ?_
      have hv : c7.get 8 = vsp := by simp [c7,c6,c5,c4,c3,c2,c1,vsp,Core.wr_get_ne,hcmd]
      rw [exec_op,Core.get_zero,hv,zero_add]
      rfl
    have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
      refine QuietDet.step_of (by change (0x80000292 : Word).getLsbD 0 = false;decide) (by exact d2147484306) fun o => ?_
      rw [exec_auipc]
      rfl
    have s9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
      refine QuietDet.step_of (by change (0x80000296 : Word).getLsbD 0 = false;decide) (by exact d2147484310) fun o => ?_
      have hv : c9.get 1 = 0x80000292#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get]
      have ht : (0x80000292#32+0xfffffda4#32) &&& ~~~1 = 0x80000036#32 := by decide +kernel
      rw [exec_jalr,hv,ht,jump_ok _ 0x80000036#32 (by decide)]
      rfl
    refine ⟨10,c10,by decide,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.single s9))))))))),?_,?_,?_,?_⟩
    · constructor
      · rfl
      · simp [next,Spec.settle,WriteTwo.start,hkind,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,out,vm,vsp,vt]
      · simp [next,Spec.settle,WriteTwo.start,hkind,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,out,vm,vsp,vt]
      · simp [next,Spec.settle,WriteTwo.start,hkind,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,out,vm,vsp,vt]
      · simp [next,Spec.settle,WriteTwo.start,hkind,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,out,vm,vsp,vt]
      · simp [next,Spec.settle,WriteTwo.start,hkind,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,out,vm,vsp,vt]
      · rfl
      · intro i hi
        have hx := i.isLt
        have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
          i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 := by omega
        have hb0 := hs ⟨0,by decide⟩
        change ram (state+0#32) = Encoding.boolByte (s.relays 0) at hb0
        rw [BitVec.add_zero] at hb0
        have hb1 := hs ⟨1,by decide⟩
        change ram (state+1#32) = Encoding.boolByte (s.relays 1) at hb1
        have hb2 := hs ⟨2,by decide⟩
        change ram (state+2#32) = Encoding.boolByte (s.relays 2) at hb2
        have hb3 := hs ⟨3,by decide⟩
        change ram (state+3#32) = Encoding.boolByte (s.relays 3) at hb3
        rcases hc with hx|hx|hx|hx|hx|hx|hx|hx|hx|hx
        all_goals first
        | exact False.elim (hi hx)
        | simp [WriteTwo.regs,WriteTwo.byte,next,Spec.settle,hkind,hx,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get,
            vlo,vhi,vsp,vt,vm,out,Fields.signed_byte0,Fields.signed_byte1,Fields.mode_byte,
            Fields.unsigned_half_byte0,Fields.unsigned_half_byte1,Encoding.snapshotByte,
            BitVec.add_assoc,hb0,hb1,hb2,hb3,hcmd]
    · simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    · rfl

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
      simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,hn0,hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8,hn9,hn10,hn11,hn12,hn13,hn14,hn15,hn16,hn17,hn18,hn19,hn20,hn21]

end E5R.Thermostat.Prepare
