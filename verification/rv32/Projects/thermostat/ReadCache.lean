import Projects.thermostat.Marshal
namespace E5R.Thermostat.ReadCache
open E5R E5R.Thermostat

/-- The inlined Read handler uses three stack words and three registers. -/
def byte (c : Core) (ram : Word → BitVec 8) (i : Fin 10) : BitVec 8 :=
  match i.val with
  | 0 => byteOf (c.get 18) 0
  | 1 => byteOf (ramRead ram 0x80ffeb98#32 .w) 0
  | 2 => byteOf (ramRead ram 0x80ffeba4#32 .w) 0
  | 3 => byteOf (ramRead ram 0x80ffeba4#32 .w) 1
  | 4 => byteOf (ramRead ram 0x80ffeb9c#32 .w) 0
  | 5 => byteOf (ramRead ram 0x80ffeb9c#32 .w) 1
  | 6 => byteOf (c.get 27) 0
  | 7 => byteOf (c.get 27) 1
  | 8 => byteOf (c.get 21) 0
  | _ => byteOf (c.get 21) 1

def At (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot) : Prop :=
  ∀ i : Fin 10, byte c ram i = Encoding.snapshotByte s i

theorem half0 (ram : Word → BitVec 8) (a : Word) :
    byteOf (extend .h false (ramRead ram a .h)) 0 = ram a := by
  apply BitVec.eq_of_toNat_eq
  have h0 := (ram a).isLt
  have h1 := (ram (a+1)).isLt
  simp only [byteOf,extend,ramRead,BitVec.toNat_and,BitVec.toNat_ofNat]
  change (((ram a).toNat+256*(ram (a+1)).toNat)%4294967296 &&& 65535)/1%256 = (ram a).toNat
  rw [show (65535 : Nat) = 2^16-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem half1 (ram : Word → BitVec 8) (a : Word) :
    byteOf (extend .h false (ramRead ram a .h)) 1 = ram (a+1) := by
  apply BitVec.eq_of_toNat_eq
  have h0 := (ram a).isLt
  have h1 := (ram (a+1)).isLt
  simp only [byteOf,extend,ramRead,BitVec.toNat_and,BitVec.toNat_ofNat]
  change (((ram a).toNat+256*(ram (a+1)).toNat)%4294967296 &&& 65535)/256%256 = (ram (a+1)).toNat
  rw [show (65535 : Nat) = 2^16-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem preserve (c d : Core) (ram ram' : Word → BitVec 8) (s : Spec.Snapshot)
    (hc : At c ram s) (h18 : d.get 18 = c.get 18) (h21 : d.get 21 = c.get 21)
    (h27 : d.get 27 = c.get 27)
    (hw8 : ramRead ram' 0x80ffeb98#32 .w = ramRead ram 0x80ffeb98#32 .w)
    (hw20 : ramRead ram' 0x80ffeba4#32 .w = ramRead ram 0x80ffeba4#32 .w)
    (hw12 : ramRead ram' 0x80ffeb9c#32 .w = ramRead ram 0x80ffeb9c#32 .w) : At d ram' s := by
  intro i
  have hh : byte d ram' i = byte c ram i := by
    unfold byte
    split <;> simp_all
  exact hh.trans (hc i)

end E5R.Thermostat.ReadCache
