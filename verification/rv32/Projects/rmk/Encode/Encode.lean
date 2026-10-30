/-
  `encode_frame` (0x80008d5c) on the pinned RMK image, PROVED for every input of its contract,
  including its callees: postcard's `index_mut` (0x8001dfe4), `Result<(), RynkError>::serialize`
  (0x80011a46) and `RynkError::serialize` (0x80014078, jump table 0x80026410). No callee is
  assumed.

  Original e5r code, Apache-2.0.

  The caller is the session's Some path (0x80003f1a, `jalr` to encode_frame; returns to 0x80003f1e).
  It encodes a 7-byte COBS frame into the buffer 0x8002a7b1:
  * the header halfword (a3) and a third byte (a4);
  * the response `Result<(), RynkError>` whose byte is at a5 = sp+0x140.
  The result `Result<usize, _>` goes to a0 = sp+0x40.

  `EncPre` is what the code needs; every field is true at the real call site:
  * sp headroom: the callee frames reach sp-0x60;
  * the response byte is a RynkError discriminant (0..8) or 0xff (Ok). Any other value makes
    `RynkError::serialize` jump through its table into unrelated data.

  `EncPost` is a write-set frame, which does not depend on the caller's layout:
  * outside the output buffer, the result slot and the callee stack, RAM is unchanged;
  * the callee-saved registers and sp are unchanged;
  * the result tag is 1 (error), or 0 with a length ≤ 7.

  The proof (`encode_spec`) is one kernel evaluation of the symbolic executor (Encode/Sym.lean) per
  response value. Every branch on data, i.e. the header and third byte being zero or not, is
  explored both ways, and every sp in the range is covered at once.
-/
import Projects.rmk.Encode.Table

set_option maxRecDepth 100000

namespace E5R.Rmk.Encode
open E5R E5R.Rmk E5R.RamElf E5R.Rmk.Sym

/-! ## The contract -/

/-- encode_frame's possible writes, for a caller at `sp`: the 7-byte frame buffer, the 8-byte
    result slot at sp+0x40, and the callee stack below sp (0x50 for encode_frame, 0x10 for
    serialize). -/
def EncW (sp x : Word) : Prop :=
  (0x8002a7b1 ≤ x.toNat ∧ x.toNat < 0x8002a7b8) ∨
  (sp.toNat + 0x40 ≤ x.toNat ∧ x.toNat < sp.toNat + 0x48) ∨
  (sp.toNat ≤ x.toNat + 0x60 ∧ x.toNat < sp.toNat)

/-- Registers encode_frame preserves: sp, gp, tp, s0..s11. -/
def calleeSaved : List Nat := [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- The result: tag 1 (error), or tag 0 with a frame length ≤ 7. -/
def EncRes (m₀ m : Machine) : Prop :=
  (m.ram (m₀.core.get 2 + 0x00000040#32)).toNat = 1 ∨
    ((m.ram (m₀.core.get 2 + 0x00000040#32)).toNat = 0 ∧
      (ramRead m.ram (m₀.core.get 2 + 0x00000044#32) .w).toNat ≤ 7)

/-- The call at 0x80003f1a, as the caller sets it up. -/
structure EncPre (m : Machine) : Prop where
  pc : m.core.pc = 0x80008d5c
  quiet : Quiet m.core
  ra : m.core.get 1 = 0x80003f1e
  out : m.core.get 10 = m.core.get 2 + 0x00000040#32
  buf : m.core.get 11 = 0x8002a7b1
  cap : m.core.get 12 = 7
  arg : m.core.get 15 = m.core.get 2 + 0x00000140#32
  spAl : (m.core.get 2).toNat % 4 = 0
  /-- headroom for the callee frames (down to sp-0x60) above the session's static cells, and the
      caller frame up to sp+0x148 in RAM -/
  sp : 0x8002a854 ≤ (m.core.get 2).toNat ∧ (m.core.get 2).toNat + 0x148 ≤ 0x81000000
  /-- the response byte: a RynkError discriminant, or 0xff (Ok) -/
  resp : (m.ram (m.core.get 2 + 0x00000140#32)).toNat ≤ 8 ∨ (m.ram (m.core.get 2 + 0x00000140#32)).toNat = 0xff

structure EncPost (m₀ m : Machine) : Prop where
  pc : m.core.pc = 0x80003f1e
  quiet : Quiet m.core
  /-- ra is restored too (the caller's `CallPost` treats it as preserved) -/
  ra : m.core.get 1 = 0x80003f1e
  saved : ∀ r : Reg, r.val ∈ calleeSaved → m.core.get r = m₀.core.get r
  frame : ∀ x, ¬ EncW (m₀.core.get 2) x → m.ram x = m₀.ram x
  res : EncRes m₀ m

/-! ## Read-only data -/

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

def rtOK (rt : Rom) : Bool :=
  rt.all fun p => decide (0x800210dc ≤ p.1.toNat) && decide (p.1.toNat + p.2.1.bytes ≤ 0x800210dc + 35564) &&
    decide (BitVec.ofNat 32 (rd roByte p.1.toNat p.2.1.bytes) = p.2.2)

theorem rtOK_sound (rt : Rom) (h : rtOK rt = true) :
    ∀ p ∈ rt, romRead? img p.1.toNat p.2.1.bytes false = some p.2.2 := by
  intro p hp
  have hc := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [romRead_ro _ _ hc.1.1 hc.1.2, hc.2]

/-- RynkError::serialize's jump table (0x80026410, one word per discriminant 0..8). -/
def encRom : Rom :=
  [(0x80026410, .w, 0x80014096), (0x80026414, .w, 0x80014192), (0x80026418, .w, 0x8001410e),
   (0x8002641c, .w, 0x8001413a), (0x80026420, .w, 0x800140e2), (0x80026424, .w, 0x800141be),
   (0x80026428, .w, 0x800141ea), (0x8002642c, .w, 0x80014166), (0x80026430, .w, 0x80014216)]

theorem encRom_ok : rtOK encRom = true := by decide +kernel

/-! ## Fetch table -/

def tblOK (tbl : Tbl) : Bool :=
  tbl.all fun p => decide (0x80000000 ≤ p.1.toNat) && decide (p.1.toNat + 4 ≤ 0x80000000 + 135386) &&
    match fetchT textByte p.1 with
    | some (b, l) => decide (decode b l = some p.2.1) && decide (l = p.2.2)
    | none => false

theorem tblOK_sound (tbl : Tbl) (h : tblOK tbl = true) : ∀ p ∈ tbl, fetchDecode img p.1 = some p.2 := by
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

theorem encTbl_ok : tblOK encTbl = true := by decide +kernel

/-! ## The symbolic entry state and the leaf test -/

def encE : Env := ⟨0x8002a854, 0x81000000 - 0x148⟩

def A40 : SE := mkLin (some 2, 0x00000040#32)
def A44 : SE := mkLin (some 2, 0x00000044#32)
def A140 : SE := mkLin (some 2, 0x00000140#32)

/-- The response byte as the (only) initial cell of symbolic memory. -/
def initW (r : Nat) : Wr := (A140, .b, .c (BitVec.ofNat 32 r))

def initR : Reg → SE := fun q =>
  if q.val = 1 then .c 0x80003f1e
  else if q.val = 10 then A40
  else if q.val = 11 then .c 0x8002a7b1
  else if q.val = 12 then .c 7
  else if q.val = 15 then A140
  else .reg q.val

def init (r : Nat) : AS := ⟨0x80008d5c, initR, [initW r]⟩

/-- A write inside `EncW`. -/
def inW (E : Env) (a : SE) (w : Width) : Bool :=
  match nform E a w.bytes with
  | some (true, k) => decide ((-0x60 ≤ k ∧ k + w.bytes ≤ 0) ∨ (0x40 ≤ k ∧ k + w.bytes ≤ 0x48))
  | some (false, k) => decide (0x8002a7b1 ≤ k ∧ k + w.bytes ≤ 0x8002a7b8)
  | none => false

def resOK (E : Env) (ws : List Wr) : Bool :=
  match rdW E ws A40 .b with
  | some (.c t) =>
    t.toNat == 1 ||
      (t.toNat == 0 && match rdW E ws A44 .w with
        | some (.c l) => decide (l.toNat ≤ 7)
        | _ => false)
  | _ => false

def savedOK (s : AS) : Bool :=
  calleeSaved.all fun q => if h : q < 32 then s.get ⟨q, h⟩ == .reg q else false

def leafE (r : Nat) (s : AS) : Bool :=
  s.pc == 0x80003f1e && s.get 1 == .c 0x80003f1e && savedOK s && s.mem.getLast? == some (initW r) &&
    s.mem.dropLast.all (fun p => inW encE p.1 p.2.1) && resOK encE s.mem

/-- The response values the contract admits. -/
def respVals : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 0xff]

/-- **The kernel run**: from every admitted response value, every symbolic path of encode_frame
    returns to 0x80003f1e within the frame, with the callee-saved registers restored and the
    result in range. -/
theorem enc_check : respVals.all (fun r => check encE encTbl encRom (leafE r) 600 (init r)) = true := by
  decide +kernel

end E5R.Rmk.Encode
