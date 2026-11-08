import Projects.thermostat.Fields

set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.Scratch
open E5R E5R.Thermostat

theorem unsigned_half_nat (ram : Word → BitVec 8) (p : Word) :
    (extend .h false (ramRead ram p .h)).toNat = (ram p).toNat + 256*(ram (p+1#32)).toNat := by
  have h0 := (ram p).isLt
  have h1 := (ram (p+1#32)).isLt
  simp only [extend,ramRead,BitVec.toNat_and,BitVec.toNat_ofNat]
  change (((ram p).toNat + 256*(ram (p+1#32)).toNat) % 4294967296 &&& 65535) = _
  rw [show (65535 : Nat) = 2^16-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem unsigned_half_bound (ram : Word → BitVec 8) (p : Word) :
    (extend .h false (ramRead ram p .h)).toNat < 65536 := by
  rw [unsigned_half_nat]
  have h0 := (ram p).isLt
  have h1 := (ram (p+1#32)).isLt
  omega

theorem pack_nat (hi lo : Word) (hh : hi.toNat < 65536) (hl : lo.toNat < 65536) :
    ((hi <<< 16) ||| lo).toNat = lo.toNat + 65536*hi.toNat := by
  rw [BitVec.toNat_or,BitVec.toNat_shiftLeft]
  have hb : hi.toNat <<< 16 < 4294967296 := by rw [Nat.shiftLeft_eq];omega
  rw [Nat.mod_eq_of_lt hb,← Nat.shiftLeft_add_eq_or_of_lt hl hi.toNat,Nat.shiftLeft_eq]
  omega

/-- The emitted shift/or packing is exactly a four-byte load, for arbitrary bytes. -/
theorem pack_word (ram : Word → BitVec 8) (p : Word) :
    (extend .h false (ramRead ram (p+2#32) .h) <<< 16) ||| extend .h false (ramRead ram p .h) =
      ramRead ram p .w := by
  apply BitVec.eq_of_toNat_eq
  rw [pack_nat _ _ (unsigned_half_bound ram (p+2#32)) (unsigned_half_bound ram p),
    unsigned_half_nat,unsigned_half_nat]
  simp only [ramRead,BitVec.toNat_ofNat]
  have h0 := (ram p).isLt
  have h1 := (ram (p+1#32)).isLt
  have h2 := (ram (p+2#32)).isLt
  have h3 := (ram (p+3#32)).isLt
  simp [BitVec.add_assoc] at *
  omega

theorem word_byte (ram : Word → BitVec 8) (p : Word) (i : Fin 4) :
    byteOf (ramRead ram p .w) i.val = ram (p+BitVec.ofNat 32 i.val) := by
  have h0 := (ram p).isLt
  have h1 := (ram (p+1#32)).isLt
  have h2 := (ram (p+2#32)).isLt
  have h3 := (ram (p+3#32)).isLt
  have hi := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases hc with h|h|h|h
  all_goals
    apply BitVec.eq_of_toNat_eq
    simp [h,byteOf,ramRead] at *
    omega

def copyWords (readRam ram : Word → BitVec 8) (src dst : Word) : Word → BitVec 8 :=
  let r1 := ramWrite ram (dst+0#32) (ramRead readRam (src+0#32) .w) .w
  let r2 := ramWrite r1 (dst+4#32) (ramRead readRam (src+4#32) .w) .w
  ramWrite r2 (dst+8#32) (extend .h true (ramRead readRam (src+8#32) .h)) .h

theorem copy_bytes (readRam ram : Word → BitVec 8) (src dst : Word) (i : Fin 10) :
    copyWords readRam ram src dst (dst+BitVec.ofNat 32 i.val) = readRam (src+BitVec.ofNat 32 i.val) := by
  have hi := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
      i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 := by omega
  rcases hc with h|h|h|h|h|h|h|h|h|h
  all_goals simp [h,copyWords,ramWrite,ramPut,BitVec.add_assoc,BitVec.self_eq_add_right,BitVec.add_right_inj,
    word_byte readRam src ⟨0,by decide⟩,word_byte readRam src ⟨1,by decide⟩,
    word_byte readRam src ⟨2,by decide⟩,word_byte readRam src ⟨3,by decide⟩,
    word_byte readRam (src+4#32) ⟨0,by decide⟩,word_byte readRam (src+4#32) ⟨1,by decide⟩,
    word_byte readRam (src+4#32) ⟨2,by decide⟩,word_byte readRam (src+4#32) ⟨3,by decide⟩,
    Memory.load_half_byte0,Memory.load_half_byte1]

def patched (s : Spec.Snapshot) (idx : BitVec 8) (on : Bool) : Spec.Snapshot :=
  {s with relays := fun r => if r.val = idx.toNat then on else s.relays r}

theorem patch_snapshot (ram : Word → BitVec 8) (p : Word) (s : Spec.Snapshot) (idx : BitVec 8) (on : Bool)
    (hs : Encoding.SnapshotAt ram p s) (hi : idx.toNat < 4) :
    Encoding.SnapshotAt (ramPut ram (p+BitVec.ofNat 32 idx.toNat) (Encoding.boolByte on)) p (patched s idx on) := by
  intro i
  have hthree : (3 : Fin 4).val = 3 := rfl
  have hx := i.isLt
  have hc : idx.toNat = 0 ∨ idx.toNat = 1 ∨ idx.toNat = 2 ∨ idx.toNat = 3 := by omega
  have hd : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
    i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 := by omega
  rcases hc with hk|hk|hk|hk
  all_goals
    rcases hd with hj|hj|hj|hj|hj|hj|hj|hj|hj|hj
    all_goals
      have he := hs i
      simp [hk,hj,patched,Encoding.snapshotByte,ramPut,BitVec.add_assoc,BitVec.add_right_inj,BitVec.self_eq_add_right,hthree] at he ⊢
      all_goals exact he

theorem copy_snapshot (readRam ram : Word → BitVec 8) (src dst : Word) (s : Spec.Snapshot)
    (hs : Encoding.SnapshotAt readRam src s) : Encoding.SnapshotAt (copyWords readRam ram src dst) dst s := by
  intro i
  exact (copy_bytes readRam ram src dst i).trans (hs i)

theorem copy_frame (readRam ram : Word → BitVec 8) (src dst x : Word)
    (hx : ∀ i : Fin 10, x ≠ dst+BitVec.ofNat 32 i.val) : copyWords readRam ram src dst x = ram x := by
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
  simp [copyWords,ramWrite,ramPut,BitVec.add_assoc] at *
  simp_all

end E5R.Thermostat.Scratch
