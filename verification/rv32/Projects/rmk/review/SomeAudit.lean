/-
  Independent audit of main's Some round against named callee contracts (Deframer/SomeRound.lean,
  `DispatchContract`, `EncodeContract`, `some_pos`, `some_round`) at support-lean4 07a17e5.
  Review evidence only: nothing here is used by main's proofs, and no main module is changed.

  Original e5r code, Apache-2.0.

  Method. `badK_sound` is a small checker for refuting `Lands`: from a concrete machine it follows
  the deterministic run (oracle 0, instructions from a fetch table checked by the kernel against
  the packed ELF, read-only loads from a table checked the same way), and returns `true` only if
  every visited machine fails a given decidable under-approximation of `¬ P` and the run ends in a
  fault. A `Lands` tree must contain that run (`Lands.step` quantifies over every successor and
  forbids faults), so `Lands P` is false there.

  PROVED here:
  * `dispatch_contract_false : ¬ DispatchContract`. A machine satisfying `DispEnv`, with the
    message pointer s9 = msgA (0x8002a580), a valid message kind 0x0202 in the header, and the
    RynkService pointer [0x8002a780] = 0 (not constrained by `DispEnv`), faults inside the real
    dispatch closure at 0x8000026e (`lbu a0, 0x4d(s2)`, address 0x4d) after 37 instructions.
  * `encode_contract_false : ¬ EncodeContract`. `EncEnv` does not separate the `Kept` UART struct
    bytes from encode_frame's 7-byte buffer 0x8002a7b1: with [uPtr] = 0x8002a795 the struct's base
    byte IS buf[0]. encode_frame (207 distinct instructions, through postcard's index_mut and
    serialize) overwrites it, returns to 0x80003f1e with `Kept` broken, and the caller then faults
    (s6 is not constrained by `EncEnv`: `lw a0, 0x2cb(s6)` misaligned).
  * `some_state_faults`: `SomeAt` (plus `h26` and a non-negative header) admits a machine whose real
    execution faults inside dispatch: SomeAt fixes neither s9 nor the RynkService pointer.
    Hence `some_hyps_false : ¬ (DispatchContract ∧ EncodeContract)` via main's own `some_pos`:
    no pair of contracts with these statements can ever be discharged, and `some_round` as stated
    is vacuous. A repaired contract must assume facts that `SomeAt`/`SessInv` must then carry.
-/
import Projects.rmk.Deframer.SomeRound

set_option maxRecDepth 100000

namespace E5R.Rmk.Review3
open E5R E5R.Rmk E5R.RamElf E5R.Rmk.Deframer E5R.Rmk.Deframer.Session E5R.Rmk.Deframer.SessionI
open E5R.Rmk.Deframer.SomeP

/-! ## `interp` with the read-only loads supplied by a function -/

def interpK (B : Board) (rom : Nat → Nat → Option Word) (o : Oracle) :
    Eff → (Word → BitVec 8) → Nat → List Event → Result
  | .done c, ram, _, evs => .ok c ram evs
  | .trap e, _, _, _ => .fault (.trap e)
  | .unsupported why, _, _, _ => .fault (.unsupported why)
  | .choose k, ram, i, evs => interpK B rom o (k ((o i).getLsbD 0)) ram (i+1) evs
  | .pick k, ram, i, evs => interpK B rom o (k (o i)) ram (i+1) evs
  | .load w a atomic k, ram, i, evs =>
    if a.toNat % w.bytes ≠ 0 then .fault .misaligned
    else if B.inRam a w.bytes then interpK B rom o (k (ramRead ram a w)) ram i evs
    else if atomic then .fault (.unsupported "atomic access outside RAM")
    else match rom a.toNat w.bytes with
      | some v => interpK B rom o (k v) ram i evs
      | none => match B.device? a with
        | some d => if d.read && w.bytes = d.width then interpK B rom o (k (devVal w (o i))) ram (i+1) evs
                    else .fault (.unsupported "device read")
        | none => .fault (.unsupported "load from an unmodeled address")
  | .store w a v atomic k, ram, i, evs =>
    if a.toNat % w.bytes ≠ 0 then .fault .misaligned
    else if B.inRam a w.bytes then interpK B rom o k (ramWrite ram a v w) i evs
    else if atomic then .fault (.unsupported "atomic access outside RAM")
    else match B.device? a with
      | some d => if d.write && w.bytes = d.width then interpK B rom o k ram i (evs ++ [⟨a, devVal w v⟩])
                  else .fault (.unsupported "device write")
      | none => .fault (.unsupported "store to an unmodeled address")

theorem interpK_eq (B : Board) (img : List Segment) (rom : Nat → Nat → Option Word)
    (hrom : ∀ a n, rom a n = romRead? img a n false) (o : Oracle) :
    ∀ e ram i evs, interp B img o e ram i evs = interpK B rom o e ram i evs := by
  intro e
  induction e with
  | done c => intro ram i evs; simp only [interp, interpK]
  | trap e => intro ram i evs; simp only [interp, interpK]
  | unsupported w => intro ram i evs; simp only [interp, interpK]
  | choose k ih => intro ram i evs; simp only [interp, interpK, ih]
  | pick k ih => intro ram i evs; simp only [interp, interpK, ih]
  | load w a t k ih => intro ram i evs; simp only [interp, interpK, hrom, ih]; rfl
  | store w a v t k ih => intro ram i evs; simp only [interp, interpK, ih]; rfl

/-! ## Read-only data of the image -/

/-- A `.rodata` byte as the model reads it. -/
def roByte (a : Nat) : Nat := rawByte elf.words (139484 + (a - 0x800210dc))

theorem romByte_ro (a : Nat) (h1 : 0x800210dc ≤ a) (h2 : a < 0x800210dc + 35564) :
    romByte? img a false = some (roByte a) := by
  unfold romByte?
  rw [ro_eq]
  have hlen0 : (elf.slice 4096 135386 ++ List.replicate 0 0).length = 135386 := by simp [slice_length]
  have hlen : (elf.slice 139484 35564 ++ List.replicate 0 0).length = 35564 := by simp [slice_length]
  simp only [List.find?, hlen0, hlen, Segment.byte?]
  simp only [show (0x80000000 ≤ a && decide (a < 0x80000000 + 135386) && (!false || true)) = false by
    simp only [Bool.not_false, Bool.true_or, Bool.and_true, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega]
  simp only [show (0x800210dc ≤ a && decide (a < 0x800210dc + 35564) && (!false || false)) = true by
    simp [h1, h2]]
  simp only [h1, ite_true, List.getElem?_append_left (show a - 0x800210dc < (elf.slice 139484 35564).length by
    rw [slice_length]; omega)]
  exact slice_get _ _ _ _ (by omega)

theorem romReadD_go {byte : Nat → Nat} {lo hi : Nat}
    (hb : ∀ x, lo ≤ x → x < hi → romByte? img x false = some (byte x)) (a : Nat) :
    ∀ n, lo ≤ a → a + n ≤ hi → romRead?.go img a false n = some (rd byte a n)
  | 0, _, _ => rfl
  | n+1, h1, h2 => by
    simp only [romRead?.go]
    rw [hb (a + n) (by omega) (by omega), romReadD_go hb a n h1 (by omega)]
    rfl

theorem romRead_ro (a n : Nat) (h1 : 0x800210dc ≤ a) (h2 : a + n ≤ 0x800210dc + 35564) :
    romRead? img a n false = some (BitVec.ofNat 32 (rd roByte a n)) := by
  unfold romRead?
  rw [romReadD_go (fun x a b => romByte_ro x a b) a n h1 h2]
  rfl

theorem romRead_low (a k : Nat) (h : a + k + 1 ≤ 0x80000000) : romRead? img a (k + 1) false = none := by
  have hb : romByte? img (a + k) false = none := by
    unfold romByte?
    rw [ro_eq]
    have n1 : ¬ 0x80000000 ≤ a + k := by omega
    have n2 : ¬ 0x800210dc ≤ a + k := by omega
    simp [List.find?, n1, n2]
  simp [romRead?, romRead?.go, hb]

/-- Read-only loads: a checked table, nothing below the image, the model elsewhere. -/
def romK (rt : List ((Nat × Nat) × Word)) (a n : Nat) : Option Word :=
  match rt.find? (fun p => p.1.1 == a && p.1.2 == n) with
  | some p => some p.2
  | none => if 0 < n ∧ a + n ≤ 0x80000000 then none else romRead? img a n false

def rtOK (rt : List ((Nat × Nat) × Word)) : Bool :=
  rt.all fun p => decide (0x800210dc ≤ p.1.1) && decide (p.1.1 + p.1.2 ≤ 0x800210dc + 35564) &&
    decide (BitVec.ofNat 32 (rd roByte p.1.1 p.1.2) = p.2)

theorem romK_eq (rt : List ((Nat × Nat) × Word)) (hrt : rtOK rt = true) (a n : Nat) :
    romK rt a n = romRead? img a n false := by
  unfold romK
  split
  · rename_i p hp
    have hm := List.mem_of_find?_eq_some hp
    have hq := List.find?_some hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    have hc := List.all_eq_true.mp hrt p hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    rw [← hq.1, ← hq.2, romRead_ro _ _ hc.1.1 hc.1.2, hc.2]
  · split
    · rename_i h
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      exact (romRead_low a k (by omega)).symm
    · rfl

/-! ## Instruction tables, checked against the packed ELF -/

def tblOK (tbl : List (Word × Instr × Word)) : Bool :=
  tbl.all fun p => decide (0x80000000 ≤ p.1.toNat) && decide (p.1.toNat + 4 ≤ 0x80000000 + 135386) &&
    match fetchT textByte p.1 with
    | some (b, l) => decide (decode b l = some p.2.1) && decide (l = p.2.2)
    | none => false

theorem tblOK_sound (tbl : List (Word × Instr × Word)) (h : tblOK tbl = true) :
    ∀ p ∈ tbl, fetchDecode img p.1 = some p.2 := by
  intro p hp
  have hc := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  split at h3
  · rename_i b l hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
    obtain ⟨hd, rfl⟩ := h3
    exact fetchDecode_of _ h1 h2 hf hd
  · exact absurd h3 (by simp)

/-! ## The refutation checker -/

def badK (rt : List ((Nat × Nat) × Word)) (tbl : List (Word × Instr × Word)) (nP : Machine → Bool) :
    Nat → Machine → Bool
  | 0, _ => false
  | n+1, m => nP m && !m.core.pc.getLsbD 0 &&
    match tbl.find? (fun p => p.1 == m.core.pc) with
    | none => false
    | some p => match interpK B (romK rt) (fun _ => 0) (exec m.core p.2.2 p.2.1) m.ram 0 [] with
      | .fault _ => true
      | .ok c r _ => badK rt tbl nP n ⟨c, r⟩

theorem badK_sound {P : Machine → Prop} (rt : List ((Nat × Nat) × Word)) (tbl : List (Word × Instr × Word))
    (nP : Machine → Bool) (hrt : rtOK rt = true) (htbl : tblOK tbl = true)
    (hP : ∀ m, nP m = true → ¬ P m) : ∀ n m, badK rt tbl nP n m = true → ¬ Lands B img P m := by
  intro n
  induction n with
  | zero => intro m h; simp [badK] at h
  | succ n ih =>
    intro m h hl
    simp only [badK, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hn, hal⟩, h⟩ := h
    split at h
    · exact absurd h (by simp)
    · rename_i p hp
      have hm := List.mem_of_find?_eq_some hp
      have hq : p.1 = m.core.pc := by simpa using List.find?_some hp
      have hd : fetchDecode img m.core.pc = some (p.2.1, p.2.2) := hq ▸ tblOK_sound tbl htbl p hm
      have hs : ∀ o, stepInstr B img m o = interp B img o (exec m.core p.2.2 p.2.1) m.ram 0 [] :=
        fun o => stepInstr_of hal hd
      have hk := interpK_eq B img (romK rt) (romK_eq rt hrt) (fun _ => 0) (exec m.core p.2.2 p.2.1) m.ram 0 []
      cases hl with
      | done hp' => exact hP m hn hp'
      | step _ hf hsucc =>
        split at h
        · rename_i f hfault
          exact hf (fun _ => 0) f (by rw [hs, hk, hfault])
        · rename_i c r e hok
          exact ih ⟨c, r⟩ h (hsucc ⟨c, r⟩ e (.instr _ (by rw [hs, hk, hok])))

/-! ## Concrete machines -/

def memT (t : List (Nat × Nat)) (a : Word) : BitVec 8 :=
  match t.find? (fun p => p.1 == a.toNat) with
  | some p => BitVec.ofNat 8 p.2
  | none => 0

def mkCore (pc : Word) (rs : List (Nat × Word)) : Core where
  pc := pc
  x := fun r => match rs.find? (fun p => p.1 == r.val) with | some p => p.2 | none => 0
  mie_ := false
  mpie := false
  mpp := 3
  mieReg := 0
  mtvec := 0x800000f8
  mepc := 0
  mcause := 0
  mscratch := 0
  resv := false

theorem mkCore_quiet (pc : Word) (rs : List (Nat × Word)) : Quiet (mkCore pc rs) :=
  fun code => by simp [irqEnabled, mkCore]

/-! ### Instruction tables (generated from the model's decoder; checked by `tblOK`) -/

def tblS : List (Word × Instr × Word) := [
  (0x80003e70#32, E5R.Instr.load (E5R.Width.h) true 10 22 0x000000cb#32, 0x00000004#32),
  (0x80003e74#32, E5R.Instr.store (E5R.Width.h) 22 10 0x000002eb#32, 0x00000004#32),
  (0x80003e78#32, E5R.Instr.branch (E5R.BrCond.lt) 10 0 0x00000160#32, 0x00000004#32),
  (0x80003e7c#32, E5R.Instr.load (E5R.Width.w) true 10 22 0x000002c3#32, 0x00000004#32),
  (0x80003e80#32, E5R.Instr.store (E5R.Width.w) 22 10 0x000002f3#32, 0x00000004#32),
  (0x80003e84#32, E5R.Instr.load (E5R.Width.w) true 10 2 0x00000020#32, 0x00000002#32),
  (0x80003e86#32, E5R.Instr.store (E5R.Width.w) 22 10 0x000002f7#32, 0x00000004#32),
  (0x80003e8a#32, E5R.Instr.store (E5R.Width.w) 22 9 0x000002fb#32, 0x00000004#32),
  (0x80003e8e#32, E5R.Instr.store (E5R.Width.b) 22 0 0x000002ff#32, 0x00000004#32),
  (0x80003e92#32, E5R.Instr.opimm (E5R.AluOp.add) 10 22 0x000002f3#32, 0x00000004#32),
  (0x80003e96#32, E5R.Instr.auipc 1 0xffffc000#32, 0x00000004#32),
  (0x80003e9a#32, E5R.Instr.jalr 1 1 0x0000035c#32, 0x00000004#32),
  (0x800001f2#32, E5R.Instr.opimm (E5R.AluOp.add) 2 2 0xfffffc20#32, 0x00000004#32),
  (0x800001f6#32, E5R.Instr.store (E5R.Width.w) 2 1 0x000003dc#32, 0x00000004#32),
  (0x800001fa#32, E5R.Instr.store (E5R.Width.w) 2 8 0x000003d8#32, 0x00000004#32),
  (0x800001fe#32, E5R.Instr.store (E5R.Width.w) 2 9 0x000003d4#32, 0x00000004#32),
  (0x80000202#32, E5R.Instr.store (E5R.Width.w) 2 18 0x000003d0#32, 0x00000004#32),
  (0x80000206#32, E5R.Instr.store (E5R.Width.w) 2 19 0x000003cc#32, 0x00000004#32),
  (0x8000020a#32, E5R.Instr.store (E5R.Width.w) 2 20 0x000003c8#32, 0x00000004#32),
  (0x8000020e#32, E5R.Instr.store (E5R.Width.w) 2 21 0x000003c4#32, 0x00000004#32),
  (0x80000212#32, E5R.Instr.store (E5R.Width.w) 2 22 0x000003c0#32, 0x00000004#32),
  (0x80000216#32, E5R.Instr.store (E5R.Width.w) 2 23 0x000003bc#32, 0x00000004#32),
  (0x8000021a#32, E5R.Instr.store (E5R.Width.w) 2 24 0x000003b8#32, 0x00000004#32),
  (0x8000021e#32, E5R.Instr.store (E5R.Width.w) 2 25 0x000003b4#32, 0x00000004#32),
  (0x80000222#32, E5R.Instr.op (E5R.AluOp.add) 24 0 10, 0x00000002#32),
  (0x80000224#32, E5R.Instr.load (E5R.Width.b) false 10 10 0x0000000c#32, 0x00000004#32),
  (0x80000228#32, E5R.Instr.opimm (E5R.AluOp.sll) 10 10 0x00000002#32, 0x00000002#32),
  (0x8000022a#32, E5R.Instr.lui 11 0x80021000#32, 0x00000004#32),
  (0x8000022e#32, E5R.Instr.opimm (E5R.AluOp.add) 11 11 0x000000dc#32, 0x00000004#32),
  (0x80000232#32, E5R.Instr.op (E5R.AluOp.add) 10 10 11, 0x00000002#32),
  (0x80000234#32, E5R.Instr.load (E5R.Width.w) true 10 10 0x00000000#32, 0x00000002#32),
  (0x80000236#32, E5R.Instr.jalr 0 10 0x00000000#32, 0x00000002#32),
  (0x80000238#32, E5R.Instr.load (E5R.Width.w) true 20 24 0x00000008#32, 0x00000004#32),
  (0x8000023c#32, E5R.Instr.load (E5R.Width.h) false 11 20 0x00000008#32, 0x00000004#32),
  (0x80000240#32, E5R.Instr.load (E5R.Width.w) true 18 24 0x00000000#32, 0x00000004#32),
  (0x80000244#32, E5R.Instr.load (E5R.Width.w) true 19 24 0x00000004#32, 0x00000004#32),
  (0x80000248#32, E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000301#32, 0x00000004#32),
  (0x8000024c#32, E5R.Instr.branch (E5R.BrCond.lt) 10 11 0x000007dc#32, 0x00000004#32),
  (0x80000250#32, E5R.Instr.opimm (E5R.AluOp.add) 10 11 0xfffffefe#32, 0x00000004#32),
  (0x80000254#32, E5R.Instr.opimm (E5R.AluOp.add) 12 0 0x00000006#32, 0x00000002#32),
  (0x80000256#32, E5R.Instr.branch (E5R.BrCond.geu) 12 10 0x00000008#32, 0x00000004#32),
  (0x8000025a#32, E5R.Instr.jal 0 0x00001e90#32, 0x00000004#32),
  (0x800020ea#32, E5R.Instr.opimm (E5R.AluOp.add) 10 11 0xfffffffc#32, 0x00000004#32),
  (0x800020ee#32, E5R.Instr.opimm (E5R.AluOp.add) 12 0 0x00000002#32, 0x00000002#32),
  (0x800020f0#32, E5R.Instr.branch (E5R.BrCond.ltu) 10 12 0x000003a0#32, 0x00000004#32),
  (0x800020f4#32, E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000202#32, 0x00000004#32),
  (0x800020f8#32, E5R.Instr.branch (E5R.BrCond.ne) 11 10 0x000003a6#32, 0x00000004#32),
  (0x800020fc#32, E5R.Instr.jal 0 0xffffe172#32, 0x00000004#32),
  (0x8000026e#32, E5R.Instr.load (E5R.Width.b) false 10 18 0x0000004d#32, 0x00000004#32)]

def tblE : List (Word × Instr × Word) := [
  (0x80008d5c#32, E5R.Instr.opimm (E5R.AluOp.add) 2 2 0xffffffb0#32, 0x00000002#32),
  (0x80008d5e#32, E5R.Instr.store (E5R.Width.w) 2 1 0x0000004c#32, 0x00000002#32),
  (0x80008d60#32, E5R.Instr.store (E5R.Width.w) 2 8 0x00000048#32, 0x00000002#32),
  (0x80008d62#32, E5R.Instr.store (E5R.Width.w) 2 9 0x00000044#32, 0x00000002#32),
  (0x80008d64#32, E5R.Instr.store (E5R.Width.w) 2 18 0x00000040#32, 0x00000002#32),
  (0x80008d66#32, E5R.Instr.store (E5R.Width.w) 2 19 0x0000003c#32, 0x00000002#32),
  (0x80008d68#32, E5R.Instr.store (E5R.Width.w) 2 20 0x00000038#32, 0x00000002#32),
  (0x80008d6a#32, E5R.Instr.store (E5R.Width.w) 2 21 0x00000034#32, 0x00000002#32),
  (0x80008d6c#32, E5R.Instr.op (E5R.AluOp.add) 21 0 10, 0x00000002#32),
  (0x80008d6e#32, E5R.Instr.branch (E5R.BrCond.eq) 12 0 0x000001d2#32, 0x00000004#32),
  (0x80008d72#32, E5R.Instr.op (E5R.AluOp.add) 20 0 14, 0x00000002#32),
  (0x80008d74#32, E5R.Instr.op (E5R.AluOp.add) 18 0 15, 0x00000002#32),
  (0x80008d76#32, E5R.Instr.op (E5R.AluOp.add) 14 11 12, 0x00000004#32),
  (0x80008d7a#32, E5R.Instr.store (E5R.Width.b) 11 0 0x00000000#32, 0x00000004#32),
  (0x80008d7e#32, E5R.Instr.opimm (E5R.AluOp.add) 10 11 0x00000001#32, 0x00000004#32),
  (0x80008d82#32, E5R.Instr.opimm (E5R.AluOp.add) 19 2 0x00000014#32, 0x00000004#32),
  (0x80008d86#32, E5R.Instr.opimm (E5R.AluOp.and) 15 13 0x000000ff#32, 0x00000004#32),
  (0x80008d8a#32, E5R.Instr.store (E5R.Width.w) 2 0 0x0000000c#32, 0x00000002#32),
  (0x80008d8c#32, E5R.Instr.store (E5R.Width.w) 2 11 0x00000014#32, 0x00000002#32),
  (0x80008d8e#32, E5R.Instr.store (E5R.Width.w) 2 10 0x00000018#32, 0x00000002#32),
  (0x80008d90#32, E5R.Instr.store (E5R.Width.w) 2 14 0x0000001c#32, 0x00000002#32),
  (0x80008d92#32, E5R.Instr.branch (E5R.BrCond.eq) 15 0 0x0000005c#32, 0x00000002#32),
  (0x80008dee#32, E5R.Instr.opimm (E5R.AluOp.add) 8 0 0x00000001#32, 0x00000002#32),
  (0x80008df0#32, E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000101#32, 0x00000004#32),
  (0x80008df4#32, E5R.Instr.store (E5R.Width.w) 2 8 0x0000000c#32, 0x00000002#32),
  (0x80008df6#32, E5R.Instr.store (E5R.Width.h) 2 10 0x00000010#32, 0x00000004#32),
  (0x80008dfa#32, E5R.Instr.lui 12 0x80025000#32, 0x00000004#32),
  (0x80008dfe#32, E5R.Instr.opimm (E5R.AluOp.add) 12 12 0xfffffc24#32, 0x00000004#32),
  (0x80008e02#32, E5R.Instr.op (E5R.AluOp.add) 10 0 19, 0x00000002#32),
  (0x80008e04#32, E5R.Instr.opimm (E5R.AluOp.add) 11 0 0x00000000#32, 0x00000002#32),
  (0x80008e06#32, E5R.Instr.op (E5R.AluOp.add) 9 0 13, 0x00000002#32),
  (0x80008e08#32, E5R.Instr.auipc 1 0x00015000#32, 0x00000004#32),
  (0x80008e0c#32, E5R.Instr.jalr 1 1 0x000001dc#32, 0x00000004#32),
  (0x8001dfe4#32, E5R.Instr.load (E5R.Width.w) true 13 10 0x00000000#32, 0x00000002#32),
  (0x8001dfe6#32, E5R.Instr.load (E5R.Width.w) true 10 10 0x00000008#32, 0x00000002#32),
  (0x8001dfe8#32, E5R.Instr.op (E5R.AluOp.sub) 10 10 13, 0x00000002#32),
  (0x8001dfea#32, E5R.Instr.branch (E5R.BrCond.geu) 11 10 0x0000000a#32, 0x00000004#32),
  (0x8001dfee#32, E5R.Instr.op (E5R.AluOp.add) 10 13 11, 0x00000004#32),
  (0x8001dff2#32, E5R.Instr.jalr 0 1 0x00000000#32, 0x00000002#32),
  (0x80008e10#32, E5R.Instr.store (E5R.Width.b) 10 8 0x00000000#32, 0x00000004#32),
  (0x80008e14#32, E5R.Instr.load (E5R.Width.w) true 10 2 0x00000018#32, 0x00000002#32),
  (0x80008e16#32, E5R.Instr.load (E5R.Width.w) true 11 2 0x0000001c#32, 0x00000002#32),
  (0x80008e18#32, E5R.Instr.branch (E5R.BrCond.eq) 10 11 0x00000128#32, 0x00000004#32),
  (0x80008e1c#32, E5R.Instr.store (E5R.Width.b) 10 0 0x00000000#32, 0x00000004#32),
  (0x80008e20#32, E5R.Instr.opimm (E5R.AluOp.sll) 13 9 0x00000010#32, 0x00000004#32),
  (0x80008e24#32, E5R.Instr.opimm (E5R.AluOp.srl) 9 13 0x00000018#32, 0x00000004#32),
  (0x80008e28#32, E5R.Instr.opimm (E5R.AluOp.add) 11 10 0x00000001#32, 0x00000004#32),
  (0x80008e2c#32, E5R.Instr.store (E5R.Width.w) 2 11 0x00000018#32, 0x00000002#32),
  (0x80008e2e#32, E5R.Instr.branch (E5R.BrCond.ne) 9 0 0xffffff86#32, 0x00000002#32),
  (0x80008e30#32, E5R.Instr.load (E5R.Width.w) true 11 2 0x0000000c#32, 0x00000002#32),
  (0x80008e32#32, E5R.Instr.load (E5R.Width.b) false 10 2 0x00000011#32, 0x00000004#32),
  (0x80008e36#32, E5R.Instr.load (E5R.Width.b) false 8 2 0x00000010#32, 0x00000004#32),
  (0x80008e3a#32, E5R.Instr.opimm (E5R.AluOp.add) 12 0 0x00000101#32, 0x00000004#32),
  (0x80008e3e#32, E5R.Instr.op (E5R.AluOp.add) 10 10 11, 0x00000002#32),
  (0x80008e40#32, E5R.Instr.store (E5R.Width.w) 2 10 0x0000000c#32, 0x00000002#32),
  (0x80008e42#32, E5R.Instr.store (E5R.Width.h) 2 12 0x00000010#32, 0x00000004#32),
  (0x80008e46#32, E5R.Instr.lui 12 0x80025000#32, 0x00000004#32),
  (0x80008e4a#32, E5R.Instr.opimm (E5R.AluOp.add) 12 12 0xfffffc24#32, 0x00000004#32),
  (0x80008e4e#32, E5R.Instr.op (E5R.AluOp.add) 10 0 19, 0x00000002#32),
  (0x80008e50#32, E5R.Instr.auipc 1 0x00015000#32, 0x00000004#32),
  (0x80008e54#32, E5R.Instr.jalr 1 1 0x00000194#32, 0x00000004#32),
  (0x80008e58#32, E5R.Instr.store (E5R.Width.b) 10 8 0x00000000#32, 0x00000004#32),
  (0x80008e5c#32, E5R.Instr.load (E5R.Width.w) true 10 2 0x00000018#32, 0x00000002#32),
  (0x80008e5e#32, E5R.Instr.load (E5R.Width.w) true 11 2 0x0000001c#32, 0x00000002#32),
  (0x80008e60#32, E5R.Instr.branch (E5R.BrCond.eq) 10 11 0x000000e0#32, 0x00000004#32),
  (0x80008e64#32, E5R.Instr.store (E5R.Width.b) 10 0 0x00000000#32, 0x00000004#32),
  (0x80008e68#32, E5R.Instr.opimm (E5R.AluOp.add) 10 10 0x00000001#32, 0x00000002#32),
  (0x80008e6a#32, E5R.Instr.opimm (E5R.AluOp.and) 11 20 0x000000ff#32, 0x00000004#32),
  (0x80008e6e#32, E5R.Instr.store (E5R.Width.w) 2 10 0x00000018#32, 0x00000002#32),
  (0x80008e70#32, E5R.Instr.branch (E5R.BrCond.eq) 11 0 0x0000007c#32, 0x00000002#32),
  (0x80008eec#32, E5R.Instr.load (E5R.Width.w) true 11 2 0x0000000c#32, 0x00000002#32),
  (0x80008eee#32, E5R.Instr.load (E5R.Width.b) false 10 2 0x00000011#32, 0x00000004#32),
  (0x80008ef2#32, E5R.Instr.load (E5R.Width.b) false 8 2 0x00000010#32, 0x00000004#32),
  (0x80008ef6#32, E5R.Instr.opimm (E5R.AluOp.add) 12 0 0x00000101#32, 0x00000004#32),
  (0x80008efa#32, E5R.Instr.op (E5R.AluOp.add) 10 10 11, 0x00000002#32),
  (0x80008efc#32, E5R.Instr.store (E5R.Width.w) 2 10 0x0000000c#32, 0x00000002#32),
  (0x80008efe#32, E5R.Instr.store (E5R.Width.h) 2 12 0x00000010#32, 0x00000004#32),
  (0x80008f02#32, E5R.Instr.lui 12 0x80025000#32, 0x00000004#32),
  (0x80008f06#32, E5R.Instr.opimm (E5R.AluOp.add) 12 12 0xfffffc24#32, 0x00000004#32),
  (0x80008f0a#32, E5R.Instr.op (E5R.AluOp.add) 10 0 19, 0x00000002#32),
  (0x80008f0c#32, E5R.Instr.auipc 1 0x00015000#32, 0x00000004#32),
  (0x80008f10#32, E5R.Instr.jalr 1 1 0x000000d8#32, 0x00000004#32),
  (0x80008f14#32, E5R.Instr.store (E5R.Width.b) 10 8 0x00000000#32, 0x00000004#32),
  (0x80008f18#32, E5R.Instr.load (E5R.Width.w) true 10 2 0x00000018#32, 0x00000002#32),
  (0x80008f1a#32, E5R.Instr.load (E5R.Width.w) true 11 2 0x0000001c#32, 0x00000002#32),
  (0x80008f1c#32, E5R.Instr.branch (E5R.BrCond.eq) 10 11 0x00000024#32, 0x00000004#32),
  (0x80008f20#32, E5R.Instr.store (E5R.Width.b) 10 0 0x00000000#32, 0x00000004#32),
  (0x80008f24#32, E5R.Instr.opimm (E5R.AluOp.add) 10 10 0x00000001#32, 0x00000002#32),
  (0x80008f26#32, E5R.Instr.store (E5R.Width.w) 2 10 0x00000018#32, 0x00000002#32),
  (0x80008f28#32, E5R.Instr.opimm (E5R.AluOp.add) 11 2 0x0000000c#32, 0x00000002#32),
  (0x80008f2a#32, E5R.Instr.op (E5R.AluOp.add) 10 0 18, 0x00000002#32),
  (0x80008f2c#32, E5R.Instr.auipc 1 0x00009000#32, 0x00000004#32),
  (0x80008f30#32, E5R.Instr.jalr 1 1 0xfffffb1a#32, 0x00000004#32),
  (0x80011a46#32, E5R.Instr.opimm (E5R.AluOp.add) 2 2 0xfffffff0#32, 0x00000002#32),
  (0x80011a48#32, E5R.Instr.store (E5R.Width.w) 2 1 0x0000000c#32, 0x00000002#32),
  (0x80011a4a#32, E5R.Instr.store (E5R.Width.w) 2 8 0x00000008#32, 0x00000002#32),
  (0x80011a4c#32, E5R.Instr.store (E5R.Width.w) 2 9 0x00000004#32, 0x00000002#32),
  (0x80011a4e#32, E5R.Instr.load (E5R.Width.b) false 13 10 0x00000000#32, 0x00000004#32),
  (0x80011a52#32, E5R.Instr.opimm (E5R.AluOp.add) 12 0 0x000000ff#32, 0x00000004#32),
  (0x80011a56#32, E5R.Instr.op (E5R.AluOp.add) 8 0 11, 0x00000002#32),
  (0x80011a58#32, E5R.Instr.branch (E5R.BrCond.eq) 13 12 0x00000032#32, 0x00000004#32),
  (0x80011a5c#32, E5R.Instr.load (E5R.Width.b) false 11 8 0x00000004#32, 0x00000004#32),
  (0x80011a60#32, E5R.Instr.load (E5R.Width.b) false 13 8 0x00000005#32, 0x00000004#32),
  (0x80011a64#32, E5R.Instr.opimm (E5R.AluOp.add) 11 11 0x00000001#32, 0x00000002#32),
  (0x80011a66#32, E5R.Instr.opimm (E5R.AluOp.add) 13 13 0x00000001#32, 0x00000002#32),
  (0x80011a68#32, E5R.Instr.opimm (E5R.AluOp.and) 14 11 0x000000ff#32, 0x00000004#32),
  (0x80011a6c#32, E5R.Instr.store (E5R.Width.b) 8 11 0x00000004#32, 0x00000004#32),
  (0x80011a70#32, E5R.Instr.store (E5R.Width.b) 8 13 0x00000005#32, 0x00000004#32),
  (0x80011a74#32, E5R.Instr.branch (E5R.BrCond.eq) 14 12 0x00000066#32, 0x00000004#32),
  (0x80011a78#32, E5R.Instr.load (E5R.Width.w) true 12 8 0x0000000c#32, 0x00000002#32),
  (0x80011a7a#32, E5R.Instr.load (E5R.Width.w) true 11 8 0x00000010#32, 0x00000002#32),
  (0x80011a7c#32, E5R.Instr.branch (E5R.BrCond.eq) 12 11 0x00000052#32, 0x00000004#32),
  (0x80011a80#32, E5R.Instr.opimm (E5R.AluOp.add) 11 0 0x00000001#32, 0x00000002#32),
  (0x80011a82#32, E5R.Instr.store (E5R.Width.b) 12 11 0x00000000#32, 0x00000004#32),
  (0x80011a86#32, E5R.Instr.opimm (E5R.AluOp.add) 12 12 0x00000001#32, 0x00000002#32),
  (0x80011a88#32, E5R.Instr.jal 0 0x000000a4#32, 0x00000002#32),
  (0x80011b2c#32, E5R.Instr.store (E5R.Width.w) 8 12 0x0000000c#32, 0x00000002#32),
  (0x80011b2e#32, E5R.Instr.op (E5R.AluOp.add) 11 0 8, 0x00000002#32),
  (0x80011b30#32, E5R.Instr.load (E5R.Width.w) true 1 2 0x0000000c#32, 0x00000002#32),
  (0x80011b32#32, E5R.Instr.load (E5R.Width.w) true 8 2 0x00000008#32, 0x00000002#32),
  (0x80011b34#32, E5R.Instr.load (E5R.Width.w) true 9 2 0x00000004#32, 0x00000002#32),
  (0x80011b36#32, E5R.Instr.opimm (E5R.AluOp.add) 2 2 0x00000010#32, 0x00000002#32),
  (0x80011b38#32, E5R.Instr.auipc 6 0x00002000#32, 0x00000004#32),
  (0x80011b3c#32, E5R.Instr.jalr 0 6 0x00000540#32, 0x00000004#32),
  (0x80014078#32, E5R.Instr.opimm (E5R.AluOp.add) 2 2 0xfffffff0#32, 0x00000002#32),
  (0x8001407a#32, E5R.Instr.store (E5R.Width.w) 2 1 0x0000000c#32, 0x00000002#32),
  (0x8001407c#32, E5R.Instr.store (E5R.Width.w) 2 8 0x00000008#32, 0x00000002#32),
  (0x8001407e#32, E5R.Instr.store (E5R.Width.w) 2 9 0x00000004#32, 0x00000002#32),
  (0x80014080#32, E5R.Instr.load (E5R.Width.b) false 10 10 0x00000000#32, 0x00000004#32),
  (0x80014084#32, E5R.Instr.opimm (E5R.AluOp.sll) 10 10 0x00000002#32, 0x00000002#32),
  (0x80014086#32, E5R.Instr.lui 12 0x80026000#32, 0x00000004#32),
  (0x8001408a#32, E5R.Instr.opimm (E5R.AluOp.add) 12 12 0x00000410#32, 0x00000004#32),
  (0x8001408e#32, E5R.Instr.op (E5R.AluOp.add) 10 10 12, 0x00000002#32),
  (0x80014090#32, E5R.Instr.load (E5R.Width.w) true 10 10 0x00000000#32, 0x00000002#32),
  (0x80014092#32, E5R.Instr.op (E5R.AluOp.add) 8 0 11, 0x00000002#32),
  (0x80014094#32, E5R.Instr.jalr 0 10 0x00000000#32, 0x00000002#32),
  (0x80014096#32, E5R.Instr.load (E5R.Width.w) true 11 8 0x00000000#32, 0x00000002#32),
  (0x80014098#32, E5R.Instr.load (E5R.Width.b) false 12 8 0x00000005#32, 0x00000004#32),
  (0x8001409c#32, E5R.Instr.load (E5R.Width.b) false 9 8 0x00000004#32, 0x00000004#32),
  (0x800140a0#32, E5R.Instr.opimm (E5R.AluOp.add) 10 8 0x00000008#32, 0x00000004#32),
  (0x800140a4#32, E5R.Instr.opimm (E5R.AluOp.add) 13 0 0x00000101#32, 0x00000004#32),
  (0x800140a8#32, E5R.Instr.op (E5R.AluOp.add) 12 12 11, 0x00000002#32),
  (0x800140aa#32, E5R.Instr.store (E5R.Width.w) 8 12 0x00000000#32, 0x00000002#32),
  (0x800140ac#32, E5R.Instr.store (E5R.Width.h) 8 13 0x00000004#32, 0x00000004#32),
  (0x800140b0#32, E5R.Instr.lui 12 0x80026000#32, 0x00000004#32),
  (0x800140b4#32, E5R.Instr.opimm (E5R.AluOp.add) 12 12 0x00000650#32, 0x00000004#32),
  (0x800140b8#32, E5R.Instr.auipc 1 0x0000a000#32, 0x00000004#32),
  (0x800140bc#32, E5R.Instr.jalr 1 1 0xffffff2c#32, 0x00000004#32),
  (0x800140c0#32, E5R.Instr.store (E5R.Width.b) 10 9 0x00000000#32, 0x00000004#32),
  (0x800140c4#32, E5R.Instr.load (E5R.Width.w) true 10 8 0x0000000c#32, 0x00000002#32),
  (0x800140c6#32, E5R.Instr.load (E5R.Width.w) true 11 8 0x00000010#32, 0x00000002#32),
  (0x800140c8#32, E5R.Instr.branch (E5R.BrCond.eq) 10 11 0x00000276#32, 0x00000004#32),
  (0x800140cc#32, E5R.Instr.store (E5R.Width.b) 10 0 0x00000000#32, 0x00000004#32),
  (0x800140d0#32, E5R.Instr.opimm (E5R.AluOp.add) 10 10 0x00000001#32, 0x00000002#32),
  (0x800140d2#32, E5R.Instr.store (E5R.Width.w) 8 10 0x0000000c#32, 0x00000002#32),
  (0x800140d4#32, E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x000000ff#32, 0x00000004#32),
  (0x800140d8#32, E5R.Instr.load (E5R.Width.w) true 1 2 0x0000000c#32, 0x00000002#32),
  (0x800140da#32, E5R.Instr.load (E5R.Width.w) true 8 2 0x00000008#32, 0x00000002#32),
  (0x800140dc#32, E5R.Instr.load (E5R.Width.w) true 9 2 0x00000004#32, 0x00000002#32),
  (0x800140de#32, E5R.Instr.opimm (E5R.AluOp.add) 2 2 0x00000010#32, 0x00000002#32),
  (0x800140e0#32, E5R.Instr.jalr 0 1 0x00000000#32, 0x00000002#32),
  (0x80008f34#32, E5R.Instr.opimm (E5R.AluOp.and) 10 10 0x000000ff#32, 0x00000004#32),
  (0x80008f38#32, E5R.Instr.opimm (E5R.AluOp.add) 11 0 0x000000ff#32, 0x00000004#32),
  (0x80008f3c#32, E5R.Instr.branch (E5R.BrCond.eq) 10 11 0x0000006a#32, 0x00000004#32),
  (0x80008fa6#32, E5R.Instr.load (E5R.Width.w) true 10 2 0x0000001c#32, 0x00000002#32),
  (0x80008fa8#32, E5R.Instr.store (E5R.Width.w) 2 10 0x00000030#32, 0x00000002#32),
  (0x80008faa#32, E5R.Instr.load (E5R.Width.w) true 11 2 0x0000000c#32, 0x00000002#32),
  (0x80008fac#32, E5R.Instr.load (E5R.Width.w) true 8 2 0x00000010#32, 0x00000002#32),
  (0x80008fae#32, E5R.Instr.load (E5R.Width.w) true 10 2 0x00000014#32, 0x00000002#32),
  (0x80008fb0#32, E5R.Instr.load (E5R.Width.w) true 12 2 0x00000018#32, 0x00000002#32),
  (0x80008fb2#32, E5R.Instr.store (E5R.Width.w) 2 11 0x00000020#32, 0x00000002#32),
  (0x80008fb4#32, E5R.Instr.store (E5R.Width.w) 2 8 0x00000024#32, 0x00000002#32),
  (0x80008fb6#32, E5R.Instr.store (E5R.Width.w) 2 10 0x00000028#32, 0x00000002#32),
  (0x80008fb8#32, E5R.Instr.store (E5R.Width.w) 2 12 0x0000002c#32, 0x00000002#32),
  (0x80008fba#32, E5R.Instr.opimm (E5R.AluOp.add) 10 2 0x00000028#32, 0x00000002#32),
  (0x80008fbc#32, E5R.Instr.lui 12 0x80025000#32, 0x00000004#32),
  (0x80008fc0#32, E5R.Instr.opimm (E5R.AluOp.add) 12 12 0x0000026c#32, 0x00000004#32),
  (0x80008fc4#32, E5R.Instr.auipc 1 0x00015000#32, 0x00000004#32),
  (0x80008fc8#32, E5R.Instr.jalr 1 1 0x00000020#32, 0x00000004#32),
  (0x80008fcc#32, E5R.Instr.store (E5R.Width.b) 10 8 0x00000000#32, 0x00000004#32),
  (0x80008fd0#32, E5R.Instr.load (E5R.Width.w) true 11 2 0x0000002c#32, 0x00000002#32),
  (0x80008fd2#32, E5R.Instr.load (E5R.Width.w) true 10 2 0x00000030#32, 0x00000002#32),
  (0x80008fd4#32, E5R.Instr.branch (E5R.BrCond.eq) 11 10 0xffffff6c#32, 0x00000004#32),
  (0x80008fd8#32, E5R.Instr.store (E5R.Width.b) 11 0 0x00000000#32, 0x00000004#32),
  (0x80008fdc#32, E5R.Instr.load (E5R.Width.w) true 12 2 0x00000028#32, 0x00000002#32),
  (0x80008fde#32, E5R.Instr.branch (E5R.BrCond.eq) 12 0 0xffffff62#32, 0x00000002#32),
  (0x80008fe0#32, E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000000#32, 0x00000002#32),
  (0x80008fe2#32, E5R.Instr.op (E5R.AluOp.sub) 11 11 12, 0x00000002#32),
  (0x80008fe4#32, E5R.Instr.opimm (E5R.AluOp.add) 11 11 0x00000001#32, 0x00000002#32),
  (0x80008fe6#32, E5R.Instr.store (E5R.Width.w) 21 11 0x00000004#32, 0x00000004#32),
  (0x80008fea#32, E5R.Instr.jal 0 0xffffff5e#32, 0x00000002#32),
  (0x80008f48#32, E5R.Instr.store (E5R.Width.b) 21 10 0x00000000#32, 0x00000004#32),
  (0x80008f4c#32, E5R.Instr.load (E5R.Width.w) true 1 2 0x0000004c#32, 0x00000002#32),
  (0x80008f4e#32, E5R.Instr.load (E5R.Width.w) true 8 2 0x00000048#32, 0x00000002#32),
  (0x80008f50#32, E5R.Instr.load (E5R.Width.w) true 9 2 0x00000044#32, 0x00000002#32),
  (0x80008f52#32, E5R.Instr.load (E5R.Width.w) true 18 2 0x00000040#32, 0x00000002#32),
  (0x80008f54#32, E5R.Instr.load (E5R.Width.w) true 19 2 0x0000003c#32, 0x00000002#32),
  (0x80008f56#32, E5R.Instr.load (E5R.Width.w) true 20 2 0x00000038#32, 0x00000002#32),
  (0x80008f58#32, E5R.Instr.load (E5R.Width.w) true 21 2 0x00000034#32, 0x00000002#32),
  (0x80008f5a#32, E5R.Instr.opimm (E5R.AluOp.add) 2 2 0x00000050#32, 0x00000002#32),
  (0x80008f5c#32, E5R.Instr.jalr 0 1 0x00000000#32, 0x00000002#32),
  (0x80003f1e#32, E5R.Instr.load (E5R.Width.b) false 10 2 0x00000040#32, 0x00000004#32),
  (0x80003f22#32, E5R.Instr.load (E5R.Width.w) true 11 2 0x00000044#32, 0x00000002#32),
  (0x80003f24#32, E5R.Instr.opimm (E5R.AluOp.add) 10 10 0xffffffff#32, 0x00000002#32),
  (0x80003f26#32, E5R.Instr.op (E5R.AluOp.and) 11 11 10, 0x00000002#32),
  (0x80003f28#32, E5R.Instr.branch (E5R.BrCond.ltu) 9 11 0x000002e8#32, 0x00000004#32),
  (0x80003f2c#32, E5R.Instr.load (E5R.Width.w) true 10 22 0x000002cb#32, 0x00000004#32)]

/-! ## Witnesses -/

def rtS : List ((Nat × Nat) × Word) := [((0x800210dc, 4), 0x80000238#32)]
def rtE : List ((Nat × Nat) × Word) := [((0x80026310, 4), 0x80025655#32)]

/-- Dispatch entry: s9 = msgA with message kind 0x0202 in its header, the future at 0x8002a7b0
    built as the caller builds it, and the RynkService pointer word [0x8002a780] = 0. -/
def mD : Machine :=
  ⟨mkCore 0x800001f2 [(1, 0x80003e9e), (2, 0x80fffe10), (9, 0x8002a580), (10, 0x8002a7b0), (22, s6v), (23, s7v)],
   memT [(0x8002a588, 2), (0x8002a589, 2), (0x8002a7b8, 0x80), (0x8002a7b9, 0xa5), (0x8002a7ba, 2), (0x8002a7bb, 0x80)]⟩

theorem dispEnv_D : DispEnv mD :=
  ⟨rfl, mkCore_quiet _ _, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

/-- **`DispatchContract` is false**: the real dispatch closure faults from `mD`. -/
theorem dispatch_contract_false : ¬ DispatchContract := fun hD =>
  badK_sound rtS tblS (fun m => m.core.pc != 0x80003e9e) (by decide +kernel) (by decide +kernel)
    (fun m hn hp => by simp [hp.pc] at hn) 300 mD (by decide +kernel) (hD mD dispEnv_D)

/-- The observed loop layout (as in SessAudit) plus a message at msgA: data = bufA, len 3, cap 3,
    header 0x0202 (non-negative); s9 = msgA; the RynkService pointer [0x8002a780] = 0. -/
def tS : List (Nat × Nat) :=
  [(0x8002a784, 0xc0), (0x8002a785, 0xa1), (0x8002a786, 0x02), (0x8002a787, 0x80),
   (0x8002a1df, 0x10), (0x8002a1e0, 1),
   (0x80fffe34, 0xc9), (0x80fffe35, 0xa7), (0x80fffe36, 0x02), (0x80fffe37, 0x80),
   (0x8002a580, 0x90), (0x8002a581, 0xa5), (0x8002a582, 0x02), (0x8002a583, 0x80),
   (0x8002a584, 3), (0x8002a58c, 3), (0x8002a588, 2), (0x8002a589, 2)]

def mS : Machine :=
  ⟨mkCore 0x80003e70 [(2, 0x80fffe10), (9, 0x8002a580), (22, s6v), (23, s7v), (26, 0x8002a7f0)], memT tS⟩

theorem extras_S : Extras mS := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, by decide, by decide, ?_⟩
  · intro k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl <;>
      (refine ⟨?_, by decide⟩; unfold SW; decide)
  · intro k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> decide

theorem someAt_S : SomeAt mS :=
  ⟨rfl, mkCore_quiet _ _, by decide, by decide, by decide, by decide,
    ⟨by decide, by decide, by decide, by decide, by decide⟩,
    ⟨by unfold consumed word; decide, by unfold filled word; decide⟩, by decide, by decide, extras_S⟩

def nPS (m : Machine) : Bool :=
  m.core.pc != 0x80003e1a && m.core.pc != 0x80004204 && m.core.pc != 0x80003fa6 && m.core.pc != 0x8000429e

theorem nPS_ok (m : Machine) (h : nPS m = true) : ¬ SomeQ m := by
  unfold nPS at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  unfold SomeQ
  rintro (⟨hp, -⟩ | hp | hp | hp) <;> simp_all

/-- **`SomeAt` admits a real fault**: with h26 and a non-negative header, the actual code from
    `mS` faults inside dispatch, so no `Lands` statement holds there. -/
theorem some_state_faults : SomeAt mS ∧ mS.core.get 26 = 0x8002a7f0 ∧ (mS.ram 0x8002a589).toNat < 0x80 ∧
    ¬ Lands B img SomeQ mS :=
  ⟨someAt_S, by decide, by decide,
    badK_sound rtS tblS nPS (by decide +kernel) (by decide +kernel) nPS_ok 300 mS (by decide +kernel)⟩

/-- **The two contracts cannot hold together** (via main's `some_pos`), so `some_round` as stated is
    vacuous: its hypotheses are false. -/
theorem some_hyps_false : ¬ (DispatchContract ∧ EncodeContract) := fun ⟨hD, hE⟩ =>
  some_state_faults.2.2.2 (some_pos hD hE mS someAt_S some_state_faults.2.1 some_state_faults.2.2.1)

/-- encode_frame entry with [uPtr] = 0x8002a795, so `Kept` contains buf[0] = 0x8002a7b1 (0x55);
    s1 = 7 and s6 = 0 for the caller after the return. -/
def mE : Machine :=
  ⟨mkCore 0x80008d5c [(1, 0x80003f1e), (2, 0x80fffe10), (9, 7), (10, 0x80fffe50), (11, 0x8002a7b1), (12, 7),
     (15, 0x80ffff50)],
   memT [(0x8002a784, 0x95), (0x8002a785, 0xa7), (0x8002a786, 2), (0x8002a787, 0x80), (0x8002a7b1, 0x55)]⟩

theorem encEnv_E : EncEnv mE :=
  ⟨rfl, mkCore_quiet _ _, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem kept_E : Kept mE 0x8002a7b1 := .inr (.inr ⟨0, by decide, by decide⟩)

def nPE (m : Machine) : Bool := m.core.pc != 0x80003f1e || m.ram 0x8002a7b1 != 0x55

theorem nPE_ok (m : Machine) (h : nPE m = true) : ¬ (CallPost 0x80003f1e mE m ∧ EncRes mE m) := by
  rintro ⟨hp, -⟩
  have h1 := hp.pc
  have h2 := hp.kept _ kept_E
  have h3 : mE.ram 0x8002a7b1 = 0x55 := by decide
  unfold nPE at h
  simp [h1] at h
  exact h (h2.trans h3)

/-- **`EncodeContract` is false**: encode_frame overwrites a `Kept` byte that `EncEnv` lets alias
    its buffer. -/
theorem encode_contract_false : ¬ EncodeContract := fun hE =>
  badK_sound rtE tblE nPE (by decide +kernel) (by decide +kernel) nPE_ok 300 mE (by decide +kernel)
    (hE mE encEnv_E)

/-- Control: with the real UART struct pointer (0x8002a1c0, outside the buffer) the same run is NOT
    refuted: at the return the struct's base byte is unchanged, so the checker stops there. The
    refutation needs the alias. -/
def mE' : Machine :=
  ⟨mE.core, memT [(0x8002a784, 0xc0), (0x8002a785, 0xa1), (0x8002a786, 2), (0x8002a787, 0x80), (0x8002a7b1, 0x55),
    (0x8002a1dc, 0x33)]⟩

def nPE' (m : Machine) : Bool := m.core.pc != 0x80003f1e || m.ram 0x8002a1dc != 0x33

theorem encode_control : badK rtE tblE nPE' 300 mE' = false := by decide +kernel

end E5R.Rmk.Review3
