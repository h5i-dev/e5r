import Theories.Logic
import Projects.thermostat.Spec

namespace E5R.Thermostat.Encoding
open E5R

/-- This ELF's bool/Mode/Command tags and Snapshot byte representation.
    These are explicit ABI preconditions, not an assumption about all rustc versions. -/
def boolByte (b : Bool) : BitVec 8 := if b then 1 else 0

def modeByte : Spec.Mode → BitVec 8
  | .off => 0 | .heat => 1 | .auto => 2

def commandTag : Spec.Command → BitVec 8
  | .setpoint _ => 0 | .reportTemp _ => 1 | .relay _ _ => 2 | .mode _ => 3 | .read => 4

def shortByte (v : BitVec 16) (high : Bool) : BitVec 8 :=
  BitVec.ofNat 8 (v.toNat / if high then 256 else 1)

def snapshotByte (s : Spec.Snapshot) (i : Fin 10) : BitVec 8 :=
  match i.val with
  | 0 => boolByte (s.relays 0)
  | 1 => boolByte (s.relays 1)
  | 2 => boolByte (s.relays 2)
  | 3 => boolByte (s.relays 3)
  | 4 => shortByte s.setpoint false
  | 5 => shortByte s.setpoint true
  | 6 => shortByte s.temp false
  | 7 => shortByte s.temp true
  | 8 => boolByte s.heater
  | _ => modeByte s.mode

def SnapshotAt (ram : Word → BitVec 8) (p : Word) (s : Spec.Snapshot) : Prop :=
  ∀ i : Fin 10, ram (p + BitVec.ofNat 32 i.val) = snapshotByte s i

def OptionAt (ram : Word → BitVec 8) (p : Word) : Option Spec.Snapshot → Prop
  | none => ram p = 2#8
  | some s => SnapshotAt ram p s

theorem option_some_tag {ram p s} (h : OptionAt ram p (some s)) : ram p ≠ 2#8 := by
  have h0 := h ⟨0, by decide⟩
  change ram (p+0#32) = boolByte (s.relays 0) at h0
  rw [BitVec.add_zero] at h0
  rw [h0]
  cases s.relays 0 <;> decide

theorem read_tag (cmd : Spec.Command) :
    (if commandTag cmd = 4#8 then (1 : Word) else 0) = if Spec.readOnly cmd then 1 else 0 := by
  cases cmd <;> simp [commandTag, Spec.readOnly]

def tagFin : Spec.Command → Fin 5
 | .setpoint _ => ⟨0,by decide⟩ | .reportTemp _ => ⟨1,by decide⟩
 | .relay _ _ => ⟨2,by decide⟩ | .mode _ => ⟨3,by decide⟩ | .read => ⟨4,by decide⟩

theorem tag_fin (cmd : Spec.Command) : commandTag cmd = BitVec.ofNat 8 (tagFin cmd).val := by
  cases cmd <;> rfl

/-- Padding and inactive payload bytes are intentionally not constrained. -/
def commandByte (cmd : Spec.Command) (i : Fin 4) : Option (BitVec 8) := match i.val with
 | 0 => some (commandTag cmd)
 | 1 => match cmd with
   | .relay idx _ => some idx | .mode m => some (modeByte m) | _ => none
 | 2 => match cmd with
   | .setpoint dc | .reportTemp dc => some (shortByte dc false)
   | .relay _ on => some (boolByte on) | _ => none
 | 3 => match cmd with
   | .setpoint dc | .reportTemp dc => some (shortByte dc true) | _ => none
 | _ => none

def CommandAt (ram : Word → BitVec 8) (p : Word) (cmd : Spec.Command) : Prop :=
  ∀ i : Fin 4, ∀ b : BitVec 8, commandByte cmd i = some b → ram (p+BitVec.ofNat 32 i.val) = b

theorem command_tag {ram p cmd} (h : CommandAt ram p cmd) : ram p = commandTag cmd := by
  have ht := h ⟨0,by decide⟩ (commandTag cmd) rfl
  simpa only [BitVec.add_zero] using ht

theorem command_preserve (ram ram' : Word → BitVec 8) (p : Word) (cmd : Spec.Command)
    (h : CommandAt ram p cmd)
    (hf : ∀ i : Fin 4, ram' (p+BitVec.ofNat 32 i.val) = ram (p+BitVec.ofNat 32 i.val)) :
    CommandAt ram' p cmd := by
  intro i b hb
  rw [hf i]
  exact h i b hb

end E5R.Thermostat.Encoding
