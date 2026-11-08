import Projects.thermostat.UartPlatform
import Projects.thermostat.MainLengthCode
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainLengthUart
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def byte (v : Word) : Word := devVal .b v

theorem extend_byte (v : Word) : extend .b false (byte v) = byte v := by
  change (v &&& 0xff#32) &&& 0xff#32 = v &&& 0xff#32
  rw [BitVec.and_assoc,BitVec.and_self]

theorem rx_load (c : Core) (ram : Word → BitVec 8) (o : Oracle)
    (hp : c.pc = 0x80000c6c#32) (hu : c.get 19 = 0x10000000#32) :
    Observed.stepInstr B img ⟨c,ram⟩ o =
      ⟨.ok (c.wr 10 (byte (o 0)) 0x80000c70#32) ram [],[⟨0x10000005#32,.b,byte (o 0),0⟩]⟩ := by
  have hk := UartPlatform.load ⟨c,ram⟩ o 10 19 5#32 4#32 0x10000005#32 UartPlatform.lsr
    (by rw [hp];decide) (by rw [hp];exact ml2147486828)
    (by rw [hu];decide +kernel) (by decide +kernel) UartPlatform.lsr_device rfl rfl
  have hext : extend .b false (devVal .b (o 0)) = byte (o 0) := extend_byte (o 0)
  have hraw : devVal .b (o 0) = byte (o 0) := rfl
  have hpcAdd : 0x80000c6c#32+4#32 = 0x80000c70#32 := by decide +kernel
  simpa only [hp,hext,hraw,extend_byte,hpcAdd] using hk

theorem rx_data_load (c : Core) (ram : Word → BitVec 8) (o : Oracle)
    (hp : c.pc = 0x80000c74#32) (hu : c.get 19 = 0x10000000#32) :
    Observed.stepInstr B img ⟨c,ram⟩ o =
      ⟨.ok (c.wr 10 (byte (o 0)) 0x80000c78#32) ram [],[⟨0x10000000#32,.b,byte (o 0),0⟩]⟩ := by
  have hk := UartPlatform.load ⟨c,ram⟩ o 10 19 0#32 4#32 0x10000000#32 UartPlatform.data
    (by rw [hp];decide) (by rw [hp];exact ml2147486836)
    (by rw [hu];decide +kernel) (by decide +kernel) UartPlatform.data_device rfl rfl
  have hext : extend .b false (devVal .b (o 0)) = byte (o 0) := extend_byte (o 0)
  have hraw : devVal .b (o 0) = byte (o 0) := rfl
  have hpcAdd : 0x80000c74#32+4#32 = 0x80000c78#32 := by decide +kernel
  simpa only [hp,hext,hraw,extend_byte,hpcAdd] using hk

theorem byteOf_zero (v : Word) : byteOf v 0 = v.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [byteOf,BitVec.toNat_setWidth]

/-- A readiness-conditioned finite execution certificate: when that LSR read is ready,
    the next RBR value is stored in the caller's checked byte destination.
    This constructs the five-instruction path for the specified reads; global
    progress additionally needs instruction scheduling and the no-IRQ envelope.
    No assumption says that a ready poll must eventually occur. -/
theorem rx_ready_full (c : Core) (ram : Word → BitVec 8) (status datum : Word)
    (hp : c.pc = 0x80000c6c#32) (hu : c.get 19 = 0x10000000#32)
    (hready : byte status &&& 1#32 ≠ 0#32) (hm : B.inRam (c.get 12) 1 = true) :
    ∃ d r, Observed.Steps B img 5 ⟨c,ram⟩ ⟨d,r⟩
      [⟨0x10000005#32,.b,byte status,0⟩,⟨0x10000000#32,.b,byte datum,0⟩] [] ∧
      d.pc = 0x80000c7c#32 ∧ d.get 12 = c.get 12 ∧ d.get 19 = c.get 19 ∧ d.sameCsr c ∧
      r (c.get 12) = (byte datum).setWidth 8 ∧
      (∀ x, x ≠ c.get 12 → r x = ram x) ∧
      (∀ rr : Reg, rr ≠ 10 → d.get rr = c.get rr) := by
  let c1 := c.wr 10 (byte status) 0x80000c70#32
  let c2 := c1.wr 10 (byte status &&& 1#32) 0x80000c72#32
  let c3 := c2.goto 0x80000c74#32
  let c4 := c3.wr 10 (byte datum) 0x80000c78#32
  let d := c4.goto 0x80000c7c#32
  let r := ramWrite ram (c.get 12) (byte datum) .b
  have h0 : Observed.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ [⟨0x10000005#32,.b,byte status,0⟩] [] := by
    have hk := rx_load c ram (fun _ => status) hp hu
    have hs : Observed.Step B img ⟨c,ram⟩ ⟨c1,ram⟩
        (Observed.stepInstr B img ⟨c,ram⟩ (fun _ => status)).reads [] := .instr (fun _ => status) (by rw [hk])
    simpa only [hk] using hs
  have h1 : Observed.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ [] [] := by
    apply Observed.pure_step (m := ⟨c1,ram⟩) (by change (0x80000c70#32).getLsbD 0 = false;decide) ml2147486832
    have hv : c1.get 10 = byte status := by simp [c1,Core.wr_get]
    rw [exec_opimm,hv]
    rfl
  have h2 : Observed.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ [] [] := by
    apply Observed.pure_step (m := ⟨c2,ram⟩) (by change (0x80000c72#32).getLsbD 0 = false;decide) ml2147486834
    have hv : c2.get 10 = byte status &&& 1#32 := by simp [c2,Core.wr_get]
    rw [exec_branch,hv,Core.get_zero]
    have hn : byte status &&& 1#32 ≠ (0 : Word) := hready
    have ht : taken .eq (byte status &&& 1#32) (0 : Word) = false := by
      simp [taken]
      exact hready
    rw [ht]
    rfl
  have h3 : Observed.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ [⟨0x10000000#32,.b,byte datum,0⟩] [] := by
    have hb : c3.get 19 = 0x10000000#32 := by simp [c3,c2,c1,Core.wr_get_ne,hu]
    have hk := rx_data_load c3 ram (fun _ => datum) rfl hb
    have hs : Observed.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩
        (Observed.stepInstr B img ⟨c3,ram⟩ (fun _ => datum)).reads [] := .instr (fun _ => datum) (by rw [hk])
    simpa only [hk] using hs
  have h4 : Observed.Step B img ⟨c4,ram⟩ ⟨d,r⟩ [] [] := by
    let o : Oracle := fun _ => 0#32
    have hk : Observed.stepInstr B img ⟨c4,ram⟩ o = ⟨.ok d r [],[]⟩ := by
      rw [Observed.stepInstr_of (m := ⟨c4,ram⟩) (by change (0x80000c78#32).getLsbD 0 = false;decide) ml2147486840,exec_store]
      have ha : c4.get 12 = c.get 12 := by simp [c4,c3,c2,c1,Core.wr_get_ne]
      have hv : c4.get 10 = byte datum := by simp [c4,Core.wr_get]
      rw [ha,hv,BitVec.add_zero]
      unfold Observed.interp
      have he : ¬((c.get 12).toNat%Width.b.bytes ≠ 0) := by simp [Width.bytes,Nat.mod_one]
      rw [ite_eq_right_of_eq_false _ _ (eq_false he)]
      have hr : B.inRam (c.get 12) Width.b.bytes = true := hm
      rw [hr]
      rfl
    have hs : Observed.Step B img ⟨c4,ram⟩ ⟨d,r⟩ (Observed.stepInstr B img ⟨c4,ram⟩ o).reads [] :=
      .instr o (by rw [hk])
    simpa only [hk] using hs
  refine ⟨d,r,.step h0 (.step h1 (.step h2 (.step h3 (.single h4)))),rfl,?_,?_,by rfl,?_,?_,?_⟩
  · simp [d,c4,c3,c2,c1,Core.wr_get_ne]
  · simp [d,c4,c3,c2,c1,Core.wr_get_ne]
  · change ramPut ram (c.get 12) (byteOf (byte datum) 0) (c.get 12) = _
    simp only [ramPut,ite_true,byteOf_zero]
  · intro x hx
    exact ramPut_ne _ hx

  · intro rr hrr
    simp [d,c4,c3,c2,c1,Core.wr_get_ne,hrr]

end E5R.Thermostat.MainLengthUart
