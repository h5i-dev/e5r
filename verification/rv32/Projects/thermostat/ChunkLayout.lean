import Projects.thermostat.HttpRequestSpec
import Projects.thermostat.StoreBytes
import Projects.thermostat.Memory
namespace E5R.Thermostat.ChunkLayout
open E5R E5R.Thermostat HttpRequestSpec

def words (s : CState) (i : Fin 6) : Word :=
  if i.val=0 then BitVec.ofNat 32 s.size
  else if i.val=2 then BitVec.ofNat 32 s.digits
  else if i.val=4 then BitVec.ofNat 32 s.total else 0#32

/-- Actual RV32 layout: three u64 fields followed by the phase byte.
    Seven padding bytes remain unconstrained. -/
def At (ram : Word → BitVec 8) (p : Word) (s : CState) : Prop :=
  (∀ i : Fin 6, ramRead ram (p+BitVec.ofNat 32 (4*i.val)) .w=words s i) ∧
  ram (p+24#32)=BitVec.ofNat 8 s.phase

def outTag : COut → BitVec 8
  | .nothing => 0#8
  | .data => 1#8
  | .done => 2#8
  | .reject _ => 3#8

/-- The enum occupies four bytes after the 32-byte state; the status is
    meaningful only in the Reject variant. -/
def OutAt (ram : Word → BitVec 8) (p : Word) (o : COut) : Prop :=
  ram (p+32#32)=outTag o ∧ ram (p+33#32)=0#8 ∧
  match o with
  | .reject status => ram (p+34#32)=byteOf (BitVec.ofNat 32 status) 0 ∧
      ram (p+35#32)=byteOf (BitVec.ofNat 32 status) 1
  | _ => True

theorem offsets_ne (p : Word) (a b i j : Nat) (ha : a+i<128) (hb : b+j<128)
    (hne : a+i≠b+j) : p+BitVec.ofNat 32 a+BitVec.ofNat 32 i ≠
      p+BitVec.ofNat 32 b+BitVec.ofNat 32 j := by
  intro h
  simp only [BitVec.add_assoc,←BitVec.ofNat_add,BitVec.add_right_inj] at h
  have hh := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at hh
  omega

theorem read_away (ram : Word → BitVec 8) (p v : Word) (a b : Nat) (w : Width)
    (ha : a+4≤128) (hb : b+w.bytes≤128) (hs : a+4≤b ∨ b+w.bytes≤a) :
    ramRead (ramWrite ram (p+BitVec.ofNat 32 b) v w) (p+BitVec.ofNat 32 a) .w=
      ramRead ram (p+BitVec.ofNat 32 a) .w := by
  apply ramRead_w_congr
  intro i hi
  apply StoreBytes.frame
  intro j
  exact offsets_ne p a b i j.val (by omega) (by have := j.isLt;omega) (by have := j.isLt;omega)

theorem byte_away (ram : Word → BitVec 8) (p v : Word) (a b : Nat) (w : Width)
    (ha : a<128) (hb : b+w.bytes≤128) (hs : a<b ∨ b+w.bytes≤a) :
    ramWrite ram (p+BitVec.ofNat 32 b) v w (p+BitVec.ofNat 32 a)=ram (p+BitVec.ofNat 32 a) := by
  apply StoreBytes.frame
  intro j
  simpa only [BitVec.add_zero] using offsets_ne p a b 0 j.val ha (by have := j.isLt;omega) (by have := j.isLt;omega)

end E5R.Thermostat.ChunkLayout
