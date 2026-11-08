import Projects.thermostat.UartPlatform
import Projects.thermostat.UartPollCode
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.UartPoll
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def byte (v : Word) : Word := devVal .b v

theorem extend_byte (v : Word) : extend .b false (byte v) = byte v := by
  change (v &&& 0xff#32) &&& 0xff#32 = v &&& 0xff#32
  rw [BitVec.and_assoc,BitVec.and_self]

theorem rx_load (c : Core) (ram : Word → BitVec 8) (o : Oracle)
    (hp : c.pc = 0x80000ba2#32) (hu : c.get 19 = 0x10000000#32) :
    Observed.stepInstr B img ⟨c,ram⟩ o =
      ⟨.ok (c.wr 10 (byte (o 0)) 0x80000ba6#32) ram [],[⟨0x10000005#32,.b,byte (o 0),0⟩]⟩ := by
  have hk := UartPlatform.load ⟨c,ram⟩ o 10 19 5#32 4#32 0x10000005#32 UartPlatform.lsr
    (by rw [hp];decide) (by rw [hp];exact up2147486626)
    (by rw [hu];decide +kernel) (by decide +kernel) UartPlatform.lsr_device rfl rfl
  have hext : extend .b false (devVal .b (o 0)) = byte (o 0) := extend_byte (o 0)
  have hraw : devVal .b (o 0) = byte (o 0) := rfl
  have hpcAdd : 0x80000ba2#32+4#32 = 0x80000ba6#32 := by decide +kernel
  simpa only [hp,hext,hraw,extend_byte,hpcAdd] using hk

def rx0 (c : Core) := c.wr 10 0#32 0x80000ba2#32
def rx1 (c : Core) := (rx0 c).wr 10 0#32 0x80000ba6#32
def rx2 (c : Core) := (rx1 c).wr 10 0#32 0x80000ba8#32
def rx3 (c : Core) := (rx2 c).goto 0x80000b9e#32

theorem overwrite (c : Core) (p q : Word) : (c.wr 10 0#32 p).wr 10 0#32 q = c.wr 10 0#32 q := by
  simp [Core.wr,Core.set]
  funext i
  by_cases hi : i = 10 <;> simp [hi]

/-- One real receive-wait cycle for an LSR read of zero. It records status,
    accepts no input byte and emits no output event. -/
theorem rx_cycle (c : Core) (ram : Word → BitVec 8) (hu : c.get 19 = 0x10000000#32) :
    Observed.Step B img ⟨rx0 c,ram⟩ ⟨rx1 c,ram⟩ [⟨0x10000005#32,.b,0#32,0⟩] [] ∧
    Observed.Step B img ⟨rx1 c,ram⟩ ⟨rx2 c,ram⟩ [] [] ∧
    Observed.Step B img ⟨rx2 c,ram⟩ ⟨rx3 c,ram⟩ [] [] ∧
    Observed.Step B img ⟨rx3 c,ram⟩ ⟨rx0 c,ram⟩ [] [] := by
  have hload := rx_load (rx0 c) ram (fun _ => 0#32) rfl (by simp [rx0,Core.wr_get_ne,hu])
  have h0 : Observed.Step B img ⟨rx0 c,ram⟩ ⟨rx1 c,ram⟩ [⟨0x10000005#32,.b,0#32,0⟩] [] := by
    have hs : Observed.Step B img ⟨rx0 c,ram⟩ ⟨rx1 c,ram⟩
        (Observed.stepInstr B img ⟨rx0 c,ram⟩ (fun _ => 0#32)).reads [] :=
      .instr (fun _ => 0#32) (by rw [hload];rfl)
    have hb : byte 0#32 = 0#32 := by decide +kernel
    simpa only [hload,hb] using hs
  have h1 : Observed.Step B img ⟨rx1 c,ram⟩ ⟨rx2 c,ram⟩ [] [] := by
    apply Observed.pure_step (m := ⟨rx1 c,ram⟩) (by change (0x80000ba6#32).getLsbD 0 = false;decide) up2147486630
    rw [exec_opimm]
    have hv : (rx1 c).get 10 = 0#32 := by simp [rx1,Core.wr_get]
    rw [hv]
    simp only [alu,BitVec.zero_and]
    rfl
  have h2 : Observed.Step B img ⟨rx2 c,ram⟩ ⟨rx3 c,ram⟩ [] [] := by
    apply Observed.pure_step (m := ⟨rx2 c,ram⟩) (by change (0x80000ba8#32).getLsbD 0 = false;decide) up2147486632
    rw [exec_branch]
    have hv : (rx2 c).get 10 = 0#32 := by simp [rx2,Core.wr_get]
    rw [hv,Core.get_zero]
    have ht : taken .eq 0#32 (0 : Word) = true := by decide +kernel
    rw [ht]
    simp only [ite_true]
    change jump (rx2 c) (0x80000ba8#32+0xfffffff6#32) = _
    rw [show 0x80000ba8#32+0xfffffff6#32 = 0x80000b9e#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  have h3 : Observed.Step B img ⟨rx3 c,ram⟩ ⟨rx0 c,ram⟩ [] [] := by
    apply Observed.pure_step (m := ⟨rx3 c,ram⟩) (by change (0x80000b9e#32).getLsbD 0 = false;decide) up2147486622
    change Eff.done ((rx3 c).goto 0x80000ba2#32) = .done (rx0 c)
    have he : (rx3 c).goto 0x80000ba2#32 = rx0 c := by
      change ((c.wr 10 0#32 0x80000ba2#32).wr 10 0#32 0x80000ba6#32).wr 10 0#32 0x80000ba2#32 = _
      rw [overwrite,overwrite]
      rfl
    rw [he]
  exact ⟨h0,h1,h2,h3⟩

def rxPhase (c : Core) (i : Nat) : Core := match i with
  | 0 => rx0 c | 1 => rx1 c | 2 => rx2 c | _ => rx3 c

def rxForever (c : Core) (ram : Word → BitVec 8) (t : Nat) : Machine := ⟨rxPhase c (t%4),ram⟩
def rxReads (t : Nat) : List Observed.Read := if t%4 = 0 then [⟨0x10000005#32,.b,0#32,0⟩] else []

/-- A concrete infinite execution under the existing arbitrary-read model.
    This is an interior polling witness until its reset prefix is connected. -/
theorem rx_forever_steps (c : Core) (ram : Word → BitVec 8) (hu : c.get 19 = 0x10000000#32) :
    ∀ t, Observed.Step B img (rxForever c ram t) (rxForever c ram (t+1)) (rxReads t) [] := by
  intro t
  obtain ⟨h0,h1,h2,h3⟩ := rx_cycle c ram hu
  have hm : t%4 = 0 ∨ t%4 = 1 ∨ t%4 = 2 ∨ t%4 = 3 := by omega
  rcases hm with h|h|h|h
  · have hn : (t+1)%4 = 1 := by omega
    simpa [rxForever,rxPhase,rxReads,h,hn] using h0
  · have hn : (t+1)%4 = 2 := by omega
    simpa [rxForever,rxPhase,rxReads,h,hn] using h1
  · have hn : (t+1)%4 = 3 := by omega
    simpa [rxForever,rxPhase,rxReads,h,hn] using h2
  · have hn : (t+1)%4 = 0 := by omega
    simpa [rxForever,rxPhase,rxReads,h,hn] using h3

theorem rx_forever_erased (c : Core) (ram : Word → BitVec 8) (hu : c.get 19 = 0x10000000#32) :
    ∀ t, E5R.Step B img (rxForever c ram t) (rxForever c ram (t+1)) [] :=
  fun t => Observed.step_erase (rx_forever_steps c ram hu t)

theorem rx_data_load (c : Core) (ram : Word → BitVec 8) (o : Oracle)
    (hp : c.pc = 0x80000baa#32) (hu : c.get 19 = 0x10000000#32) :
    Observed.stepInstr B img ⟨c,ram⟩ o =
      ⟨.ok (c.wr 10 (byte (o 0)) 0x80000bae#32) ram [],[⟨0x10000000#32,.b,byte (o 0),0⟩]⟩ := by
  have hk := UartPlatform.load ⟨c,ram⟩ o 10 19 0#32 4#32 0x10000000#32 UartPlatform.data
    (by rw [hp];decide) (by rw [hp];exact up2147486634)
    (by rw [hu];decide +kernel) (by decide +kernel) UartPlatform.data_device rfl rfl
  have hext : extend .b false (devVal .b (o 0)) = byte (o 0) := extend_byte (o 0)
  have hraw : devVal .b (o 0) = byte (o 0) := rfl
  have hpcAdd : 0x80000baa#32+4#32 = 0x80000bae#32 := by decide +kernel
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
    (hp : c.pc = 0x80000ba2#32) (hu : c.get 19 = 0x10000000#32)
    (hready : byte status &&& 1#32 ≠ 0#32) (hm : B.inRam (c.get 12) 1 = true) :
    ∃ d r, Observed.Steps B img 5 ⟨c,ram⟩ ⟨d,r⟩
      [⟨0x10000005#32,.b,byte status,0⟩,⟨0x10000000#32,.b,byte datum,0⟩] [] ∧
      d.pc = 0x80000bb2#32 ∧ d.get 12 = c.get 12 ∧ d.get 19 = c.get 19 ∧ d.sameCsr c ∧
      r (c.get 12) = (byte datum).setWidth 8 ∧
      (∀ x, x ≠ c.get 12 → r x = ram x) ∧
      (∀ rr : Reg, rr ≠ 10 → d.get rr = c.get rr) := by
  let c1 := c.wr 10 (byte status) 0x80000ba6#32
  let c2 := c1.wr 10 (byte status &&& 1#32) 0x80000ba8#32
  let c3 := c2.goto 0x80000baa#32
  let c4 := c3.wr 10 (byte datum) 0x80000bae#32
  let d := c4.goto 0x80000bb2#32
  let r := ramWrite ram (c.get 12) (byte datum) .b
  have h0 : Observed.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ [⟨0x10000005#32,.b,byte status,0⟩] [] := by
    have hk := rx_load c ram (fun _ => status) hp hu
    have hs : Observed.Step B img ⟨c,ram⟩ ⟨c1,ram⟩
        (Observed.stepInstr B img ⟨c,ram⟩ (fun _ => status)).reads [] := .instr (fun _ => status) (by rw [hk])
    simpa only [hk] using hs
  have h1 : Observed.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ [] [] := by
    apply Observed.pure_step (m := ⟨c1,ram⟩) (by change (0x80000ba6#32).getLsbD 0 = false;decide) up2147486630
    have hv : c1.get 10 = byte status := by simp [c1,Core.wr_get]
    rw [exec_opimm,hv]
    rfl
  have h2 : Observed.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ [] [] := by
    apply Observed.pure_step (m := ⟨c2,ram⟩) (by change (0x80000ba8#32).getLsbD 0 = false;decide) up2147486632
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
      rw [Observed.stepInstr_of (m := ⟨c4,ram⟩) (by change (0x80000bae#32).getLsbD 0 = false;decide) up2147486638,exec_store]
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

theorem rx_ready (c : Core) (ram : Word → BitVec 8) (status datum : Word)
    (hp : c.pc = 0x80000ba2#32) (hu : c.get 19 = 0x10000000#32)
    (hready : byte status &&& 1#32 ≠ 0#32) (hm : B.inRam (c.get 12) 1 = true) :
    ∃ d r, Observed.Steps B img 5 ⟨c,ram⟩ ⟨d,r⟩
      [⟨0x10000005#32,.b,byte status,0⟩,⟨0x10000000#32,.b,byte datum,0⟩] [] ∧
      d.pc = 0x80000bb2#32 ∧ d.get 12 = c.get 12 ∧ d.get 19 = c.get 19 ∧ d.sameCsr c ∧
      r (c.get 12) = (byte datum).setWidth 8 ∧
      (∀ x, x ≠ c.get 12 → r x = ram x) := by
  obtain ⟨d,r,hr,hpc,h12,h19,hcsr,hat,hframe,_⟩ := rx_ready_full c ram status datum hp hu hready hm
  exact ⟨d,r,hr,hpc,h12,h19,hcsr,hat,hframe⟩

end E5R.Thermostat.UartPoll
