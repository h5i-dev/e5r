import Projects.thermostat.Outcome
import Projects.thermostat.Memory
set_option maxRecDepth 2000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.WriteTwo
open E5R E5R.Thermostat

structure Values where
  relaysLo : Word
  relaysHi : Word
  setpoint : Word
  temp : Word
  heater : Word
  mode : Word

def write (ram : Word → BitVec 8) (out : Word) (v : Values) : Word → BitVec 8 :=
  let r1 := ramWrite ram (out+0#32) v.relaysLo .h
  let r2 := ramWrite r1 (out+2#32) v.relaysHi .h
  let r3 := ramWrite r2 (out+4#32) v.setpoint .h
  let r4 := ramWrite r3 (out+6#32) v.temp .h
  let r5 := ramWrite r4 (out+8#32) v.heater .b
  let r6 := ramWrite r5 (out+9#32) v.mode .b
  let r7 := ramWrite r6 (out+10#32) v.relaysLo .h
  let r8 := ramWrite r7 (out+12#32) v.relaysHi .h
  let r9 := ramWrite r8 (out+14#32) v.setpoint .h
  let r10 := ramWrite r9 (out+16#32) v.temp .h
  let r11 := ramWrite r10 (out+18#32) v.heater .b
  let r12 := ramWrite r11 (out+19#32) v.mode .b
  r12

def byte (v : Values) (i : Fin 10) : BitVec 8 := match i.val with
 | 0 => byteOf v.relaysLo 0
 | 1 => byteOf v.relaysLo 1
 | 2 => byteOf v.relaysHi 0
 | 3 => byteOf v.relaysHi 1
 | 4 => byteOf v.setpoint 0
 | 5 => byteOf v.setpoint 1
 | 6 => byteOf v.temp 0
 | 7 => byteOf v.temp 1
 | 8 => byteOf v.heater 0
 | _ => byteOf v.mode 0

theorem bytes_first (ram : Word → BitVec 8) (out : Word) (v : Values) (i : Fin 10) :
    write ram out v (out+BitVec.ofNat 32 i.val) = byte v i := by
  have hi := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
    i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 := by omega
  rcases hc with h|h|h|h|h|h|h|h|h|h
  all_goals simp [h,write,byte,ramWrite,ramPut,BitVec.add_assoc,BitVec.self_eq_add_right,BitVec.add_right_inj]

theorem bytes_second (ram : Word → BitVec 8) (out : Word) (v : Values) (i : Fin 10) :
    write ram out v ((out+10#32)+BitVec.ofNat 32 i.val) = byte v i := by
  have hi := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
    i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 := by omega
  rcases hc with h|h|h|h|h|h|h|h|h|h
  all_goals simp [h,write,byte,ramWrite,ramPut,BitVec.add_assoc,BitVec.self_eq_add_right,BitVec.add_right_inj]

theorem frame (ram : Word → BitVec 8) (out x : Word) (v : Values)
    (hx : ∀ i : Fin 20, x ≠ out+BitVec.ofNat 32 i.val) : write ram out v x = ram x := by
  have h0 := hx ⟨0,by decide⟩
  have h1 := hx ⟨1,by decide⟩
  have h2 := hx ⟨2,by decide⟩
  have h3 := hx ⟨3,by decide⟩
  have h4 := hx ⟨4,by decide⟩
  have h5 := hx ⟨5,by decide⟩
  have h6 := hx ⟨6,by decide⟩
  have h7 := hx ⟨7,by decide⟩
  have h8 := hx ⟨8,by decide⟩
  have h9 := hx ⟨9,by decide⟩
  have h10 := hx ⟨10,by decide⟩
  have h11 := hx ⟨11,by decide⟩
  have h12 := hx ⟨12,by decide⟩
  have h13 := hx ⟨13,by decide⟩
  have h14 := hx ⟨14,by decide⟩
  have h15 := hx ⟨15,by decide⟩
  have h16 := hx ⟨16,by decide⟩
  have h17 := hx ⟨17,by decide⟩
  have h18 := hx ⟨18,by decide⟩
  have h19 := hx ⟨19,by decide⟩
  simp [write,ramWrite,ramPut,BitVec.add_assoc] at *
  simp_all

theorem source (ram : Word → BitVec 8) (out : Word) (v : Values) (s : Spec.Snapshot)
    (h : ∀ i : Fin 10, byte v i = Encoding.snapshotByte s i) :
    Outcome.At (write ram out v) out (.ok ⟨some s,s⟩) := by
  constructor
  · intro i; exact (bytes_first ram out v i).trans (h i)
  · intro i; exact (bytes_second ram out v i).trans (h i)

def start (kind : Fin 3) : Word := match kind.val with
 | 0 => 0x800000a2 | 1 => 0x8000017c | _ => 0x8000029a

def regs (c : Core) (kind : Fin 3) : Values :=
  match kind.val with
  | 0 => ⟨c.get 19,c.get 20,c.get 9,c.get 18,c.get 10,c.get 8⟩
  | 1 => ⟨c.get 19,c.get 20,c.get 8,c.get 18,c.get 10,c.get 9⟩
  | _ => ⟨c.get 19,c.get 20,c.get 8,c.get 9,c.get 10,c.get 18⟩

def steps (kind : Fin 3) : Nat := match kind.val with
 | 0 => 13 | 1 => 12 | _ => 13

theorem steps_le (kind : Fin 3) : steps kind ≤ 13 := by
  unfold steps
  split <;> decide

/-- The three actual success tails, covering SetMode, ReportTemp and SetSetpoint.
    The exact final core states that all GPRs and CSRs are preserved. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (kind : Fin 3)
    (hp : c.pc = start kind) (hmem : Memory.Block B (c.get 21) 20) (hal : (c.get 21).toNat % 2 = 0) :
    DetSteps B img (steps kind) ⟨c,ram⟩ ⟨c.goto 0x800001ac,write ram (c.get 21) (regs c kind)⟩ := by
  have hi := kind.isLt
  have hc : kind.val = 0 ∨ kind.val = 1 ∨ kind.val = 2 := by omega
  rcases hc with hkind|hkind|hkind
  · have hp' : c.pc = 0x800000a2 := by simpa [start,hkind] using hp
    let r0 := ram
    let r1 := ramWrite r0 (c.get 21+0#32) (c.get 19) .h
    let c1 := c.goto 0x800000a6
    let r2 := ramWrite r1 (c.get 21+2#32) (c.get 20) .h
    let c2 := c.goto 0x800000aa
    let r3 := ramWrite r2 (c.get 21+4#32) (c.get 9) .h
    let c3 := c.goto 0x800000ae
    let r4 := ramWrite r3 (c.get 21+6#32) (c.get 18) .h
    let c4 := c.goto 0x800000b2
    let r5 := ramWrite r4 (c.get 21+8#32) (c.get 10) .b
    let c5 := c.goto 0x800000b6
    let r6 := ramWrite r5 (c.get 21+9#32) (c.get 8) .b
    let c6 := c.goto 0x800000ba
    let r7 := ramWrite r6 (c.get 21+10#32) (c.get 19) .h
    let c7 := c.goto 0x800000be
    let r8 := ramWrite r7 (c.get 21+12#32) (c.get 20) .h
    let c8 := c.goto 0x800000c2
    let r9 := ramWrite r8 (c.get 21+14#32) (c.get 9) .h
    let c9 := c.goto 0x800000c6
    let r10 := ramWrite r9 (c.get 21+16#32) (c.get 18) .h
    let c10 := c.goto 0x800000ca
    let r11 := ramWrite r10 (c.get 21+18#32) (c.get 10) .b
    let c11 := c.goto 0x800000ce
    let r12 := ramWrite r11 (c.get 21+19#32) (c.get 8) .b
    let c12 := c.goto 0x800000d2
    have s0 : DetStep B img ⟨c,r0⟩ ⟨c1,r1⟩ := by
      have hm : B.inRam (c.get 21+0#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 0) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+0#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 0 hal
      refine detStep_of (by rw [hp'];decide)
        (by rw [hp']; exact d2147483810) fun o => ?_
      rw [exec_store]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+0#32) (v := c.get 19) o ha hm]
      rw [hp']
      rfl
    have s1 : DetStep B img ⟨c1,r1⟩ ⟨c2,r2⟩ := by
      have hm : B.inRam (c.get 21+2#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 2) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+2#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 1 hal
      refine detStep_of (by change (0x800000a6 : Word).getLsbD 0 = false;decide)
        (by exact d2147483814) fun o => ?_
      rw [exec_store]
      simp only [c1,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+2#32) (v := c.get 20) o ha hm]
      rfl
    have s2 : DetStep B img ⟨c2,r2⟩ ⟨c3,r3⟩ := by
      have hm : B.inRam (c.get 21+4#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 4) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+4#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 2 hal
      refine detStep_of (by change (0x800000aa : Word).getLsbD 0 = false;decide)
        (by exact d2147483818) fun o => ?_
      rw [exec_store]
      simp only [c2,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+4#32) (v := c.get 9) o ha hm]
      rfl
    have s3 : DetStep B img ⟨c3,r3⟩ ⟨c4,r4⟩ := by
      have hm : B.inRam (c.get 21+6#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 6) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+6#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 3 hal
      refine detStep_of (by change (0x800000ae : Word).getLsbD 0 = false;decide)
        (by exact d2147483822) fun o => ?_
      rw [exec_store]
      simp only [c3,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+6#32) (v := c.get 18) o ha hm]
      rfl
    have s4 : DetStep B img ⟨c4,r4⟩ ⟨c5,r5⟩ := by
      have hm : B.inRam (c.get 21+8#32) 1 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 8) (width := 1) hmem (by decide) (by decide)
      have ha : (c.get 21+8#32).toNat % 1 = 0 := by
        exact Nat.mod_one _
      refine detStep_of (by change (0x800000b2 : Word).getLsbD 0 = false;decide)
        (by exact d2147483826) fun o => ?_
      rw [exec_store]
      simp only [c4,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .b) (a := c.get 21+8#32) (v := c.get 10) o ha hm]
      rfl
    have s5 : DetStep B img ⟨c5,r5⟩ ⟨c6,r6⟩ := by
      have hm : B.inRam (c.get 21+9#32) 1 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 9) (width := 1) hmem (by decide) (by decide)
      have ha : (c.get 21+9#32).toNat % 1 = 0 := by
        exact Nat.mod_one _
      refine detStep_of (by change (0x800000b6 : Word).getLsbD 0 = false;decide)
        (by exact d2147483830) fun o => ?_
      rw [exec_store]
      simp only [c5,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .b) (a := c.get 21+9#32) (v := c.get 8) o ha hm]
      rfl
    have s6 : DetStep B img ⟨c6,r6⟩ ⟨c7,r7⟩ := by
      have hm : B.inRam (c.get 21+10#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 10) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+10#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 5 hal
      refine detStep_of (by change (0x800000ba : Word).getLsbD 0 = false;decide)
        (by exact d2147483834) fun o => ?_
      rw [exec_store]
      simp only [c6,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+10#32) (v := c.get 19) o ha hm]
      rfl
    have s7 : DetStep B img ⟨c7,r7⟩ ⟨c8,r8⟩ := by
      have hm : B.inRam (c.get 21+12#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 12) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+12#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 6 hal
      refine detStep_of (by change (0x800000be : Word).getLsbD 0 = false;decide)
        (by exact d2147483838) fun o => ?_
      rw [exec_store]
      simp only [c7,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+12#32) (v := c.get 20) o ha hm]
      rfl
    have s8 : DetStep B img ⟨c8,r8⟩ ⟨c9,r9⟩ := by
      have hm : B.inRam (c.get 21+14#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 14) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+14#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 7 hal
      refine detStep_of (by change (0x800000c2 : Word).getLsbD 0 = false;decide)
        (by exact d2147483842) fun o => ?_
      rw [exec_store]
      simp only [c8,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+14#32) (v := c.get 9) o ha hm]
      rfl
    have s9 : DetStep B img ⟨c9,r9⟩ ⟨c10,r10⟩ := by
      have hm : B.inRam (c.get 21+16#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 16) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+16#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 8 hal
      refine detStep_of (by change (0x800000c6 : Word).getLsbD 0 = false;decide)
        (by exact d2147483846) fun o => ?_
      rw [exec_store]
      simp only [c9,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+16#32) (v := c.get 18) o ha hm]
      rfl
    have s10 : DetStep B img ⟨c10,r10⟩ ⟨c11,r11⟩ := by
      have hm : B.inRam (c.get 21+18#32) 1 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 18) (width := 1) hmem (by decide) (by decide)
      have ha : (c.get 21+18#32).toNat % 1 = 0 := by
        exact Nat.mod_one _
      refine detStep_of (by change (0x800000ca : Word).getLsbD 0 = false;decide)
        (by exact d2147483850) fun o => ?_
      rw [exec_store]
      simp only [c10,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .b) (a := c.get 21+18#32) (v := c.get 10) o ha hm]
      rfl
    have s11 : DetStep B img ⟨c11,r11⟩ ⟨c12,r12⟩ := by
      have hm : B.inRam (c.get 21+19#32) 1 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 19) (width := 1) hmem (by decide) (by decide)
      have ha : (c.get 21+19#32).toNat % 1 = 0 := by
        exact Nat.mod_one _
      refine detStep_of (by change (0x800000ce : Word).getLsbD 0 = false;decide)
        (by exact d2147483854) fun o => ?_
      rw [exec_store]
      simp only [c11,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .b) (a := c.get 21+19#32) (v := c.get 8) o ha hm]
      rfl
    have s12 : DetStep B img ⟨c12,r12⟩ ⟨c.goto 0x800001ac,r12⟩ := by
      refine detStep_of (by change (0x800000d2 : Word).getLsbD 0 = false;decide) d2147483858 fun o => ?_
      rw [exec_jal,Core.set_zero,jump_ok _ _ (by change (0x800001ac : Word).getLsbD 0 = false;decide)]
      rfl
    simp only [regs,steps,hkind]
    change DetSteps B img 13 ⟨c,ram⟩ ⟨c.goto 0x800001ac,r12⟩
    exact (.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.single s12)))))))))))) : DetSteps B img 13 ⟨c,ram⟩ ⟨c.goto 0x800001ac,r12⟩)
  · have hp' : c.pc = 0x8000017c := by simpa [start,hkind] using hp
    let r0 := ram
    let r1 := ramWrite r0 (c.get 21+0#32) (c.get 19) .h
    let c1 := c.goto 0x80000180
    let r2 := ramWrite r1 (c.get 21+2#32) (c.get 20) .h
    let c2 := c.goto 0x80000184
    let r3 := ramWrite r2 (c.get 21+4#32) (c.get 8) .h
    let c3 := c.goto 0x80000188
    let r4 := ramWrite r3 (c.get 21+6#32) (c.get 18) .h
    let c4 := c.goto 0x8000018c
    let r5 := ramWrite r4 (c.get 21+8#32) (c.get 10) .b
    let c5 := c.goto 0x80000190
    let r6 := ramWrite r5 (c.get 21+9#32) (c.get 9) .b
    let c6 := c.goto 0x80000194
    let r7 := ramWrite r6 (c.get 21+10#32) (c.get 19) .h
    let c7 := c.goto 0x80000198
    let r8 := ramWrite r7 (c.get 21+12#32) (c.get 20) .h
    let c8 := c.goto 0x8000019c
    let r9 := ramWrite r8 (c.get 21+14#32) (c.get 8) .h
    let c9 := c.goto 0x800001a0
    let r10 := ramWrite r9 (c.get 21+16#32) (c.get 18) .h
    let c10 := c.goto 0x800001a4
    let r11 := ramWrite r10 (c.get 21+18#32) (c.get 10) .b
    let c11 := c.goto 0x800001a8
    let r12 := ramWrite r11 (c.get 21+19#32) (c.get 9) .b
    let c12 := c.goto 0x800001ac
    have s0 : DetStep B img ⟨c,r0⟩ ⟨c1,r1⟩ := by
      have hm : B.inRam (c.get 21+0#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 0) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+0#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 0 hal
      refine detStep_of (by rw [hp'];decide)
        (by rw [hp']; exact d2147484028) fun o => ?_
      rw [exec_store]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+0#32) (v := c.get 19) o ha hm]
      rw [hp']
      rfl
    have s1 : DetStep B img ⟨c1,r1⟩ ⟨c2,r2⟩ := by
      have hm : B.inRam (c.get 21+2#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 2) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+2#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 1 hal
      refine detStep_of (by change (0x80000180 : Word).getLsbD 0 = false;decide)
        (by exact d2147484032) fun o => ?_
      rw [exec_store]
      simp only [c1,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+2#32) (v := c.get 20) o ha hm]
      rfl
    have s2 : DetStep B img ⟨c2,r2⟩ ⟨c3,r3⟩ := by
      have hm : B.inRam (c.get 21+4#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 4) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+4#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 2 hal
      refine detStep_of (by change (0x80000184 : Word).getLsbD 0 = false;decide)
        (by exact d2147484036) fun o => ?_
      rw [exec_store]
      simp only [c2,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+4#32) (v := c.get 8) o ha hm]
      rfl
    have s3 : DetStep B img ⟨c3,r3⟩ ⟨c4,r4⟩ := by
      have hm : B.inRam (c.get 21+6#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 6) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+6#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 3 hal
      refine detStep_of (by change (0x80000188 : Word).getLsbD 0 = false;decide)
        (by exact d2147484040) fun o => ?_
      rw [exec_store]
      simp only [c3,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+6#32) (v := c.get 18) o ha hm]
      rfl
    have s4 : DetStep B img ⟨c4,r4⟩ ⟨c5,r5⟩ := by
      have hm : B.inRam (c.get 21+8#32) 1 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 8) (width := 1) hmem (by decide) (by decide)
      have ha : (c.get 21+8#32).toNat % 1 = 0 := by
        exact Nat.mod_one _
      refine detStep_of (by change (0x8000018c : Word).getLsbD 0 = false;decide)
        (by exact d2147484044) fun o => ?_
      rw [exec_store]
      simp only [c4,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .b) (a := c.get 21+8#32) (v := c.get 10) o ha hm]
      rfl
    have s5 : DetStep B img ⟨c5,r5⟩ ⟨c6,r6⟩ := by
      have hm : B.inRam (c.get 21+9#32) 1 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 9) (width := 1) hmem (by decide) (by decide)
      have ha : (c.get 21+9#32).toNat % 1 = 0 := by
        exact Nat.mod_one _
      refine detStep_of (by change (0x80000190 : Word).getLsbD 0 = false;decide)
        (by exact d2147484048) fun o => ?_
      rw [exec_store]
      simp only [c5,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .b) (a := c.get 21+9#32) (v := c.get 9) o ha hm]
      rfl
    have s6 : DetStep B img ⟨c6,r6⟩ ⟨c7,r7⟩ := by
      have hm : B.inRam (c.get 21+10#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 10) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+10#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 5 hal
      refine detStep_of (by change (0x80000194 : Word).getLsbD 0 = false;decide)
        (by exact d2147484052) fun o => ?_
      rw [exec_store]
      simp only [c6,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+10#32) (v := c.get 19) o ha hm]
      rfl
    have s7 : DetStep B img ⟨c7,r7⟩ ⟨c8,r8⟩ := by
      have hm : B.inRam (c.get 21+12#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 12) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+12#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 6 hal
      refine detStep_of (by change (0x80000198 : Word).getLsbD 0 = false;decide)
        (by exact d2147484056) fun o => ?_
      rw [exec_store]
      simp only [c7,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+12#32) (v := c.get 20) o ha hm]
      rfl
    have s8 : DetStep B img ⟨c8,r8⟩ ⟨c9,r9⟩ := by
      have hm : B.inRam (c.get 21+14#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 14) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+14#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 7 hal
      refine detStep_of (by change (0x8000019c : Word).getLsbD 0 = false;decide)
        (by exact d2147484060) fun o => ?_
      rw [exec_store]
      simp only [c8,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+14#32) (v := c.get 8) o ha hm]
      rfl
    have s9 : DetStep B img ⟨c9,r9⟩ ⟨c10,r10⟩ := by
      have hm : B.inRam (c.get 21+16#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 16) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+16#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 8 hal
      refine detStep_of (by change (0x800001a0 : Word).getLsbD 0 = false;decide)
        (by exact d2147484064) fun o => ?_
      rw [exec_store]
      simp only [c9,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+16#32) (v := c.get 18) o ha hm]
      rfl
    have s10 : DetStep B img ⟨c10,r10⟩ ⟨c11,r11⟩ := by
      have hm : B.inRam (c.get 21+18#32) 1 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 18) (width := 1) hmem (by decide) (by decide)
      have ha : (c.get 21+18#32).toNat % 1 = 0 := by
        exact Nat.mod_one _
      refine detStep_of (by change (0x800001a4 : Word).getLsbD 0 = false;decide)
        (by exact d2147484068) fun o => ?_
      rw [exec_store]
      simp only [c10,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .b) (a := c.get 21+18#32) (v := c.get 10) o ha hm]
      rfl
    have s11 : DetStep B img ⟨c11,r11⟩ ⟨c12,r12⟩ := by
      have hm : B.inRam (c.get 21+19#32) 1 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 19) (width := 1) hmem (by decide) (by decide)
      have ha : (c.get 21+19#32).toNat % 1 = 0 := by
        exact Nat.mod_one _
      refine detStep_of (by change (0x800001a8 : Word).getLsbD 0 = false;decide)
        (by exact d2147484072) fun o => ?_
      rw [exec_store]
      simp only [c11,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .b) (a := c.get 21+19#32) (v := c.get 9) o ha hm]
      rfl
    simp only [regs,steps,hkind]
    change DetSteps B img 12 ⟨c,ram⟩ ⟨c.goto 0x800001ac,r12⟩
    exact (.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.single s11))))))))))) : DetSteps B img 12 ⟨c,ram⟩ ⟨c.goto 0x800001ac,r12⟩)
  · have hp' : c.pc = 0x8000029a := by simpa [start,hkind] using hp
    let r0 := ram
    let r1 := ramWrite r0 (c.get 21+0#32) (c.get 19) .h
    let c1 := c.goto 0x8000029e
    let r2 := ramWrite r1 (c.get 21+2#32) (c.get 20) .h
    let c2 := c.goto 0x800002a2
    let r3 := ramWrite r2 (c.get 21+4#32) (c.get 8) .h
    let c3 := c.goto 0x800002a6
    let r4 := ramWrite r3 (c.get 21+6#32) (c.get 9) .h
    let c4 := c.goto 0x800002aa
    let r5 := ramWrite r4 (c.get 21+8#32) (c.get 10) .b
    let c5 := c.goto 0x800002ae
    let r6 := ramWrite r5 (c.get 21+9#32) (c.get 18) .b
    let c6 := c.goto 0x800002b2
    let r7 := ramWrite r6 (c.get 21+10#32) (c.get 19) .h
    let c7 := c.goto 0x800002b6
    let r8 := ramWrite r7 (c.get 21+12#32) (c.get 20) .h
    let c8 := c.goto 0x800002ba
    let r9 := ramWrite r8 (c.get 21+14#32) (c.get 8) .h
    let c9 := c.goto 0x800002be
    let r10 := ramWrite r9 (c.get 21+16#32) (c.get 9) .h
    let c10 := c.goto 0x800002c2
    let r11 := ramWrite r10 (c.get 21+18#32) (c.get 10) .b
    let c11 := c.goto 0x800002c6
    let r12 := ramWrite r11 (c.get 21+19#32) (c.get 18) .b
    let c12 := c.goto 0x800002ca
    have s0 : DetStep B img ⟨c,r0⟩ ⟨c1,r1⟩ := by
      have hm : B.inRam (c.get 21+0#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 0) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+0#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 0 hal
      refine detStep_of (by rw [hp'];decide)
        (by rw [hp']; exact d2147484314) fun o => ?_
      rw [exec_store]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+0#32) (v := c.get 19) o ha hm]
      rw [hp']
      rfl
    have s1 : DetStep B img ⟨c1,r1⟩ ⟨c2,r2⟩ := by
      have hm : B.inRam (c.get 21+2#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 2) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+2#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 1 hal
      refine detStep_of (by change (0x8000029e : Word).getLsbD 0 = false;decide)
        (by exact d2147484318) fun o => ?_
      rw [exec_store]
      simp only [c1,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+2#32) (v := c.get 20) o ha hm]
      rfl
    have s2 : DetStep B img ⟨c2,r2⟩ ⟨c3,r3⟩ := by
      have hm : B.inRam (c.get 21+4#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 4) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+4#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 2 hal
      refine detStep_of (by change (0x800002a2 : Word).getLsbD 0 = false;decide)
        (by exact d2147484322) fun o => ?_
      rw [exec_store]
      simp only [c2,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+4#32) (v := c.get 8) o ha hm]
      rfl
    have s3 : DetStep B img ⟨c3,r3⟩ ⟨c4,r4⟩ := by
      have hm : B.inRam (c.get 21+6#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 6) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+6#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 3 hal
      refine detStep_of (by change (0x800002a6 : Word).getLsbD 0 = false;decide)
        (by exact d2147484326) fun o => ?_
      rw [exec_store]
      simp only [c3,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+6#32) (v := c.get 9) o ha hm]
      rfl
    have s4 : DetStep B img ⟨c4,r4⟩ ⟨c5,r5⟩ := by
      have hm : B.inRam (c.get 21+8#32) 1 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 8) (width := 1) hmem (by decide) (by decide)
      have ha : (c.get 21+8#32).toNat % 1 = 0 := by
        exact Nat.mod_one _
      refine detStep_of (by change (0x800002aa : Word).getLsbD 0 = false;decide)
        (by exact d2147484330) fun o => ?_
      rw [exec_store]
      simp only [c4,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .b) (a := c.get 21+8#32) (v := c.get 10) o ha hm]
      rfl
    have s5 : DetStep B img ⟨c5,r5⟩ ⟨c6,r6⟩ := by
      have hm : B.inRam (c.get 21+9#32) 1 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 9) (width := 1) hmem (by decide) (by decide)
      have ha : (c.get 21+9#32).toNat % 1 = 0 := by
        exact Nat.mod_one _
      refine detStep_of (by change (0x800002ae : Word).getLsbD 0 = false;decide)
        (by exact d2147484334) fun o => ?_
      rw [exec_store]
      simp only [c5,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .b) (a := c.get 21+9#32) (v := c.get 18) o ha hm]
      rfl
    have s6 : DetStep B img ⟨c6,r6⟩ ⟨c7,r7⟩ := by
      have hm : B.inRam (c.get 21+10#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 10) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+10#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 5 hal
      refine detStep_of (by change (0x800002b2 : Word).getLsbD 0 = false;decide)
        (by exact d2147484338) fun o => ?_
      rw [exec_store]
      simp only [c6,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+10#32) (v := c.get 19) o ha hm]
      rfl
    have s7 : DetStep B img ⟨c7,r7⟩ ⟨c8,r8⟩ := by
      have hm : B.inRam (c.get 21+12#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 12) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+12#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 6 hal
      refine detStep_of (by change (0x800002b6 : Word).getLsbD 0 = false;decide)
        (by exact d2147484342) fun o => ?_
      rw [exec_store]
      simp only [c7,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+12#32) (v := c.get 20) o ha hm]
      rfl
    have s8 : DetStep B img ⟨c8,r8⟩ ⟨c9,r9⟩ := by
      have hm : B.inRam (c.get 21+14#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 14) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+14#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 7 hal
      refine detStep_of (by change (0x800002ba : Word).getLsbD 0 = false;decide)
        (by exact d2147484346) fun o => ?_
      rw [exec_store]
      simp only [c8,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+14#32) (v := c.get 8) o ha hm]
      rfl
    have s9 : DetStep B img ⟨c9,r9⟩ ⟨c10,r10⟩ := by
      have hm : B.inRam (c.get 21+16#32) 2 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 16) (width := 2) hmem (by decide) (by decide)
      have ha : (c.get 21+16#32).toNat % 2 = 0 := by
        exact Memory.half_aligned (c.get 21) 8 hal
      refine detStep_of (by change (0x800002be : Word).getLsbD 0 = false;decide)
        (by exact d2147484350) fun o => ?_
      rw [exec_store]
      simp only [c9,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .h) (a := c.get 21+16#32) (v := c.get 9) o ha hm]
      rfl
    have s10 : DetStep B img ⟨c10,r10⟩ ⟨c11,r11⟩ := by
      have hm : B.inRam (c.get 21+18#32) 1 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 18) (width := 1) hmem (by decide) (by decide)
      have ha : (c.get 21+18#32).toNat % 1 = 0 := by
        exact Nat.mod_one _
      refine detStep_of (by change (0x800002c2 : Word).getLsbD 0 = false;decide)
        (by exact d2147484354) fun o => ?_
      rw [exec_store]
      simp only [c10,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .b) (a := c.get 21+18#32) (v := c.get 10) o ha hm]
      rfl
    have s11 : DetStep B img ⟨c11,r11⟩ ⟨c12,r12⟩ := by
      have hm : B.inRam (c.get 21+19#32) 1 = true :=
        Memory.block_access (B := B) (p := c.get 21) (n := 20) (off := 19) (width := 1) hmem (by decide) (by decide)
      have ha : (c.get 21+19#32).toNat % 1 = 0 := by
        exact Nat.mod_one _
      refine detStep_of (by change (0x800002c6 : Word).getLsbD 0 = false;decide)
        (by exact d2147484358) fun o => ?_
      rw [exec_store]
      simp only [c11,Core.goto_get]
      rw [interp_store_ram (B := B) (img := img) (w := .b) (a := c.get 21+19#32) (v := c.get 18) o ha hm]
      rfl
    have s12 : DetStep B img ⟨c12,r12⟩ ⟨c.goto 0x800001ac,r12⟩ := by
      have ht : c12.pc + 0xfffffee2#32 = 0x800001ac#32 := by
        change 0x800002ca#32 + 0xfffffee2#32 = 0x800001ac#32
        decide +kernel
      refine detStep_of (by change (0x800002ca : Word).getLsbD 0 = false;decide) d2147484362 fun o => ?_
      rw [exec_jal,Core.set_zero,ht,jump_ok c12 0x800001ac#32 (by decide)]
      rfl
    simp only [regs,steps,hkind]
    change DetSteps B img 13 ⟨c,ram⟩ ⟨c.goto 0x800001ac,r12⟩
    exact (.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.single s12)))))))))))) : DetSteps B img 13 ⟨c,ram⟩ ⟨c.goto 0x800001ac,r12⟩)

end E5R.Thermostat.WriteTwo
