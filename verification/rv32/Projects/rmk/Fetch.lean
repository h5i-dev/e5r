/-
  Instruction fetch from the pinned RMK image (QEMU virt), made cheap for
  the kernel.

  Original e5r code, Apache-2.0.

  The model's image is `(RamElf.imageOf 0x80000000 0x1000000 elf).ro`, the
  read-only segments the independent reader (Theories/RamElf.lean) makes
  from the packed ELF file. Deciding one `fetchDecode` on it directly makes
  the kernel run the reader and build the 135 KB segment list every time
  (60 s, 8 GB per instruction). Here the reader is run once (`roShape`, a
  Boolean the kernel decides), general lemmas about `File.slice` turn a
  fetch inside `.text` into reads of the packed words (`rawByte`), and each
  instruction fact is then a small kernel computation.

  Nothing here is assumed about the bytes: `ro_eq` is derived from the
  reader's own output, and `fetchDecode_text` is an equation about the
  model's `fetchDecode` on that image.
-/
import Projects.rmk.Elf
import Theories.Board.QemuVirtRv32
import Theories.Logic

set_option maxRecDepth 100000

namespace E5R.Rmk
open E5R E5R.RamElf

abbrev elf := Image.elf
abbrev img : List Segment := (imageOf 0x80000000 0x1000000 elf).ro
/-- Model RAM starts after the read-only segments (main: rwBase 0x80029bc8). -/
abbrev B : Board := QemuVirtRv32.board 0x80029bc8

/-- Byte `j` of packed words, read the way `File.slice` reads it. -/
def rawByte (ws : List Nat) (j : Nat) : Nat := ws.getD (j / 64) 0 / 256 ^ (j % 64) % 256

/-! ## `File.slice` -/

theorem unpackN_length : ∀ n x, (unpackN n x).length = n
  | 0, _ => rfl
  | n+1, x => by simp [unpackN, unpackN_length n]

theorem unpackN_get : ∀ n x k, k < n → (unpackN n x)[k]? = some (x / 256 ^ k % 256)
  | 0, _, k, h => absurd h (Nat.not_lt_zero _)
  | n+1, x, 0, _ => by simp [unpackN]
  | n+1, x, k+1, h => by
    simp only [unpackN, List.getElem?_cons_succ]
    rw [unpackN_get n (x / 256) k (by omega), Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

theorem go_length : ∀ (ws : List Nat) (k n : Nat), k ≤ 64 → (File.slice.go ws k n).length = n
  | _, _, 0, _ => by simp [File.slice.go]
  | [], _, n+1, _ => by simp [File.slice.go]
  | w :: ws, k, n+1, hk => by
    simp only [File.slice.go]
    have hl : ((unpackN 64 w).drop k).length = 64 - k := by simp [unpackN_length]
    split
    · rename_i h; rw [List.length_take]; omega
    · rename_i h; rw [List.length_append, go_length ws 0 _ (by omega)]; omega

theorem go_get : ∀ (ws : List Nat) (k n i : Nat), k < 64 → i < n →
    (File.slice.go ws k n)[i]? = some (rawByte ws (k + i))
  | _, _, 0, i, _, hi => absurd hi (Nat.not_lt_zero _)
  | [], k, n+1, i, _, hi => by
    simp only [File.slice.go, List.getElem?_replicate, rawByte, List.getD_nil, Nat.zero_div, Nat.zero_mod]
    simp [hi]
  | w :: ws, k, n+1, i, hk, hi => by
    simp only [File.slice.go]
    have hl : ((unpackN 64 w).drop k).length = 64 - k := by simp [unpackN_length]
    have here : ∀ i, i < 64 - k → ((unpackN 64 w).drop k)[i]? = some (rawByte (w :: ws) (k + i)) := by
      intro i hi'
      rw [List.getElem?_drop, unpackN_get 64 w (k + i) (by omega)]
      simp only [rawByte]
      rw [show (k + i) / 64 = 0 by omega, show (k + i) % 64 = k + i by omega]; rfl
    split
    · rename_i h
      rw [List.getElem?_take_of_lt hi]; exact here i (by omega)
    · rename_i h
      by_cases hi' : i < 64 - k
      · rw [List.getElem?_append_left (by omega)]; exact here i hi'
      · rw [List.getElem?_append_right (by omega), hl, go_get ws 0 _ _ (by omega) (by omega)]
        simp only [rawByte]
        rw [show (k + i) / 64 = (0 + (i - (64 - k))) / 64 + 1 by omega,
          show (k + i) % 64 = (0 + (i - (64 - k))) % 64 by omega]
        rfl

theorem slice_length (f : File) (off n : Nat) : (f.slice off n).length = n :=
  go_length _ _ _ (by omega)

theorem slice_get (f : File) (off n i : Nat) (hi : i < n) :
    (f.slice off n)[i]? = some (rawByte f.words (off + i)) := by
  unfold File.slice
  rw [go_get _ _ _ _ (by omega) hi]
  simp only [rawByte, List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [show off / 64 + (off % 64 + i) / 64 = (off + i) / 64 by omega,
    show (off % 64 + i) % 64 = (off + i) % 64 by omega]

/-! ## The image's read-only segments -/

/-- The reader's read-only loads, as (address, file offset, file size, memory size, exec). -/
def roShape : Bool :=
  match check 0x80000000 0x1000000 elf with
  | .ok (_, ls, _) => (ls.filter (!·.write)).map (fun l => (l.vaddr, l.off, l.filesz, l.memsz, l.exec)) ==
      [(0x80000000, 4096, 135386, 135386, true), (0x800210dc, 139484, 35564, 35564, false)]
  | .error _ => false

/-- The reader accepts the pinned file, with `.text` and `.rodata` read-only (kernel, ~30 s). -/
theorem roShape_ok : roShape = true := by decide +kernel

theorem ro_eq : img = [⟨0x80000000, elf.slice 4096 135386 ++ List.replicate 0 0, true⟩,
    ⟨0x800210dc, elf.slice 139484 35564 ++ List.replicate 0 0, false⟩] := by
  have h := roShape_ok
  unfold roShape at h
  show (imageOf 0x80000000 0x1000000 elf).ro = _
  unfold imageOf
  split at h
  · rename_i e ls r hc
    rw [hc]
    simp only
    generalize ls.filter (!·.write) = ro at h ⊢
    have h' := beq_iff_eq.mp h
    rcases ro with _ | ⟨l0, _ | ⟨l1, _ | ⟨l2, rest⟩⟩⟩
    · simp at h'
    · simp at h'
    · simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at h'
      obtain ⟨⟨a0, o0, f0, m0, x0⟩, a1, o1, f1, m1, x1⟩ := h'
      simp [a0, o0, f0, m0, x0, a1, o1, f1, m1, x1]
    · simp at h'
  · cases h

/-- A byte of `.text` as the model fetches it. -/
theorem romByte_text (a : Nat) (h1 : 0x80000000 ≤ a) (h2 : a < 0x80000000 + 135386) :
    romByte? img a true = some (rawByte elf.words (4096 + (a - 0x80000000))) := by
  unfold romByte?
  rw [ro_eq]
  have hlen : (elf.slice 4096 135386 ++ List.replicate 0 0).length = 135386 := by
    simp [slice_length]
  simp only [List.find?, hlen, Segment.byte?]
  simp only [show (0x80000000 ≤ a && decide (a < 0x80000000 + 135386) && (!true || true)) = true by
    simp [h1, h2]]
  simp only [h1, ite_true, List.getElem?_append_left (show a - 0x80000000 < (elf.slice 4096 135386).length by
    rw [slice_length]; omega)]
  exact slice_get _ _ _ _ (by omega)

/-! ## Fetch, for an abstract byte source

The lemmas below take the byte source as a variable `byte`, so the kernel
never has to unfold the packed file while checking them; only the
per-instruction facts (`fetchDecode_of`) evaluate it, by `decide +kernel`. -/

/-- The text byte at address `a`. -/
def textByte (a : Nat) : Nat := rawByte elf.words (4096 + (a - 0x80000000))

/-- Little-endian value of `n` bytes from `a`. -/
def rd (byte : Nat → Nat) (a : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => rd byte a k + byte (a + k) * 256 ^ k

theorem romRead_go {byte : Nat → Nat} {lo hi : Nat}
    (hb : ∀ x, lo ≤ x → x < hi → romByte? img x true = some (byte x)) (a : Nat) :
    ∀ n, lo ≤ a → a + n ≤ hi → romRead?.go img a true n = some (rd byte a n)
  | 0, _, _ => rfl
  | n+1, h1, h2 => by
    simp only [romRead?.go]
    rw [hb (a + n) (by omega) (by omega), romRead_go hb a n h1 (by omega)]
    rfl

/-- The model's fetch from a byte source. -/
def fetchT (byte : Nat → Nat) (pc : Word) : Option (Word × Word) :=
  let lo := BitVec.ofNat 32 (rd byte pc.toNat 2)
  if lo &&& 3 ≠ 3 then some (lo, 2)
  else some ((BitVec.ofNat 32 (rd byte (pc.toNat + 2) 2) <<< 16) ||| lo, 4)

theorem fetch_eq {byte : Nat → Nat} {lo hi : Nat}
    (hb : ∀ x, lo ≤ x → x < hi → romByte? img x true = some (byte x))
    (pc : Word) (h1 : lo ≤ pc.toNat) (h2 : pc.toNat + 4 ≤ hi) :
    fetch img pc = fetchT byte pc := by
  unfold fetch fetchT romRead?
  rw [romRead_go hb _ 2 h1 (by omega), romRead_go hb _ 2 (by omega) (by omega)]
  rfl

theorem fetchDecode_eq {byte : Nat → Nat} {lo hi : Nat}
    (hb : ∀ x, lo ≤ x → x < hi → romByte? img x true = some (byte x))
    (pc : Word) (h1 : lo ≤ pc.toNat) (h2 : pc.toNat + 4 ≤ hi) {bits len : Word} {i : Instr}
    (hf : fetchT byte pc = some (bits, len)) (hd : decode bits len = some i) :
    fetchDecode img pc = some (i, len) := by
  unfold fetchDecode
  rw [fetch_eq hb pc h1 h2, hf]
  simp [hd]

/-- **An instruction of `.text`**: `fetchDecode` on the model's image at
    `pc`, from the packed file. The two last arguments are evaluated by the
    kernel (`decide +kernel`) for a concrete `pc`. -/
theorem fetchDecode_of (pc : Word) (h1 : 0x80000000 ≤ pc.toNat)
    (h2 : pc.toNat + 4 ≤ 0x80000000 + 135386) {bits len : Word} {i : Instr}
    (hf : fetchT textByte pc = some (bits, len)) (hd : decode bits len = some i) :
    fetchDecode img pc = some (i, len) :=
  fetchDecode_eq (byte := textByte) (fun x a b => romByte_text x a b) pc h1 h2 hf hd

end E5R.Rmk
