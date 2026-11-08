import Projects.thermostat.Encoding
namespace E5R.Thermostat.AppState
open E5R E5R.Thermostat

/-- The live main App object, including immutable authentication metadata.
    Only a committed snapshot is described; intermediate write stores are not
    required to satisfy the snapshot invariant. -/
structure At (ram : Word → BitVec 8) (s : Spec.Snapshot) : Prop where
  state : Encoding.SnapshotAt ram 0x80ffebc0#32 s
  available : ramRead ram 0x80ffebbc#32 .w = 0#32
  keyPtr : ramRead ram 0x80ffebcc#32 .w = 0x80005b7c#32
  keyLen : ramRead ram 0x80ffebd0#32 .w = 7#32
  principal : ram 0x80ffebd4#32 = 1#8

theorem preserve (ram ram' : Word → BitVec 8) (s : Spec.Snapshot) (h : At ram s)
    (hf : ∀ i : Fin 25, ram' (0x80ffebbc#32+BitVec.ofNat 32 i.val) = ram (0x80ffebbc#32+BitVec.ofNat 32 i.val)) :
    At ram' s := by
  have hw (off : Nat) (ho : off+4 ≤ 25) :
      ramRead ram' (0x80ffebbc#32+BitVec.ofNat 32 off) .w = ramRead ram (0x80ffebbc#32+BitVec.ofNat 32 off) .w := by
    apply ramRead_w_congr
    intro k hk
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hf ⟨off+k,by omega⟩
  constructor
  · intro i
    have hi := i.isLt
    have hh := hf ⟨4+i.val,by omega⟩
    have he : 0x80ffebbc#32+BitVec.ofNat 32 (4+i.val) = 0x80ffebc0#32+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [he] at hh
    exact hh.trans (h.state i)
  · exact (hw 0 (by decide)).trans h.available
  · exact (hw 16 (by decide)).trans h.keyPtr
  · exact (hw 20 (by decide)).trans h.keyLen
  · exact (hf ⟨24,by decide⟩).trans h.principal
end E5R.Thermostat.AppState
