import Projects.thermostat.Encoding
namespace E5R.Thermostat.ReplyCache
open E5R E5R.Thermostat

/-- The caller saves a reply across apply in five registers and one stack word. -/
def byte (c : Core) (ram : Word → BitVec 8) (sp : Word) (i : Fin 10) : BitVec 8 :=
  match i.val with
  | 0 => byteOf (c.get 21) 0
  | 1 => byteOf (c.get 24) 0
  | 2 => byteOf (ramRead ram (sp+4#32) .w) 0
  | 3 => byteOf (ramRead ram (sp+4#32) .w) 1
  | 4 => byteOf (c.get 26) 0
  | 5 => byteOf (c.get 26) 1
  | 6 => byteOf (c.get 27) 0
  | 7 => byteOf (c.get 27) 1
  | 8 => byteOf (c.get 25) 0
  | _ => byteOf (c.get 25) 1

def At (c : Core) (ram : Word → BitVec 8) (sp : Word) (s : Spec.Snapshot) : Prop :=
  ∀ i : Fin 10, byte c ram sp i = Encoding.snapshotByte s i

theorem preserve (c d : Core) (ram ram' : Word → BitVec 8) (sp : Word) (s : Spec.Snapshot)
    (hc : At c ram sp s) (h21 : d.get 21 = c.get 21) (h24 : d.get 24 = c.get 24)
    (h25 : d.get 25 = c.get 25) (h26 : d.get 26 = c.get 26) (h27 : d.get 27 = c.get 27)
    (hw : ramRead ram' (sp+4#32) .w = ramRead ram (sp+4#32) .w) : At d ram' sp s := by
  intro i
  have hi := i.isLt
  have he : byte d ram' sp i = byte c ram sp i := by
    unfold byte
    split <;> simp_all
  exact he.trans (hc i)
end E5R.Thermostat.ReplyCache
