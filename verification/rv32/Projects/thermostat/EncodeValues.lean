import Projects.thermostat.FormatSource
import Projects.thermostat.JsonProgram
import Projects.thermostat.Fields
namespace E5R.Thermostat.EncodeValues
open E5R E5R.Thermostat

def values (reply tuple : Word) (s : Spec.Snapshot) (i : Fin 8) : FormatValue.Value := match i.val with
  | 0 => .signed (reply+4#32) s.setpoint
  | 1 => .signed (reply+6#32) s.temp
  | 2 => .boolean (reply+8#32) s.heater
  | 3 => .boolean reply (s.relays 0)
  | 4 => .boolean (reply+1#32) (s.relays 1)
  | 5 => .boolean (reply+2#32) (s.relays 2)
  | 6 => .boolean (reply+3#32) (s.relays 3)
  | _ => .mode tuple s.mode

theorem bytes (reply tuple : Word) (s : Spec.Snapshot) (i : Fin 8) :
    FormatValue.bytes (values reply tuple s i) = JsonProgram.argument s i := by
  have hi := i.isLt
  have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 ∨ i.val=6 ∨ i.val=7 := by omega
  rcases hc with h0|h0|h0|h0|h0|h0|h0|h0 <;> simp only [values,JsonProgram.argument,h0] <;> rfl

theorem sources {B ram reply tuple s}
    (hr : Memory.Block B reply 10) (ha : reply.toNat%2=0) (hs : Encoding.SnapshotAt ram reply s)
    (ht : Memory.Block B tuple 8) (hat : tuple.toNat%4=0)
    (hp : ramRead ram tuple .w = ModeLiterals.pointer s.mode)
    (hl : ramRead ram (tuple+4#32) .w = BitVec.ofNat 32 (ReplyJson.mode s.mode).length) :
    ∀ i : Fin 8, FormatSource.At B ram (values reply tuple s i) := by
  have hbool (k : Fin 10) (v : Bool) (hv : Encoding.snapshotByte s k = Encoding.boolByte v) :
      ReadBytes.Byte B img ram (reply+BitVec.ofNat 32 k.val) (Encoding.boolByte v) :=
    .ram (Memory.block_access hr (by decide) (by have := k.isLt;omega)) ((hs k).trans hv)
  intro i
  have hi := i.isLt
  have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 ∨ i.val=6 ∨ i.val=7 := by omega
  rcases hc with h0|h0|h0|h0|h0|h0|h0|h0
  · simp only [values,h0]
    exact .signed _ _ (Memory.sub_block hr (off := 4) (m := 2) (by decide) (by decide))
      (Memory.half_aligned reply 2 ha) (Fields.setpoint ram reply s hs)
  · simp only [values,h0]
    exact .signed _ _ (Memory.sub_block hr (off := 6) (m := 2) (by decide) (by decide))
      (Memory.half_aligned reply 3 ha) (Fields.temp ram reply s hs)
  · simp only [values,h0]
    exact .boolean _ _ (hbool ⟨8,by decide⟩ s.heater rfl)
  · simp only [values,h0]
    apply FormatSource.At.boolean
    simpa only [BitVec.add_zero] using hbool ⟨0,by decide⟩ (s.relays 0) rfl
  · simp only [values,h0]
    exact .boolean _ _ (hbool ⟨1,by decide⟩ (s.relays 1) rfl)
  · simp only [values,h0]
    exact .boolean _ _ (hbool ⟨2,by decide⟩ (s.relays 2) rfl)
  · simp only [values,h0]
    exact .boolean _ _ (hbool ⟨3,by decide⟩ (s.relays 3) rfl)
  · simp only [values,h0]
    exact .mode _ _ ht hat hp hl
end E5R.Thermostat.EncodeValues
