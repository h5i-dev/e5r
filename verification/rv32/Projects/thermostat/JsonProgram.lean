import Projects.thermostat.ReplyJson
namespace E5R.Thermostat.JsonProgram
open E5R E5R.Thermostat

def literal (i : Fin 9) : List (BitVec 8) := match i.val with
  | 0 => WireSpec.ascii "{\"setpoint_dc\":"
  | 1 => WireSpec.ascii ",\"temp_dc\":"
  | 2 => WireSpec.ascii ",\"heater\":"
  | 3 => WireSpec.ascii ",\"relays\":["
  | 4 => WireSpec.ascii ","
  | 5 => WireSpec.ascii ","
  | 6 => WireSpec.ascii ","
  | 7 => WireSpec.ascii "],\"mode\":\""
  | _ => WireSpec.ascii "\"}"

def argument (s : Spec.Snapshot) (i : Fin 8) : List (BitVec 8) := match i.val with
  | 0 => ReplyJson.signed s.setpoint | 1 => ReplyJson.signed s.temp
  | 2 => ReplyJson.boolean s.heater | 3 => ReplyJson.boolean (s.relays 0)
  | 4 => ReplyJson.boolean (s.relays 1) | 5 => ReplyJson.boolean (s.relays 2)
  | 6 => ReplyJson.boolean (s.relays 3) | _ => ReplyJson.mode s.mode

def render (s : Spec.Snapshot) : List (BitVec 8) :=
  [literal 0,argument s 0,literal 1,argument s 1,literal 2,argument s 2,literal 3,argument s 3,
   literal 4,argument s 4,literal 5,argument s 5,literal 6,argument s 6,literal 7,argument s 7,literal 8].flatten

def encodedLiteral (i : Fin 9) : List (BitVec 8) := BitVec.ofNat 8 (literal i).length::literal i

def descriptor : List (BitVec 8) :=
  encodedLiteral 0++[192#8]++encodedLiteral 1++[192#8]++encodedLiteral 2++[192#8]++
  encodedLiteral 3++[192#8]++encodedLiteral 4++[192#8]++encodedLiteral 5++[192#8]++
  encodedLiteral 6++[192#8]++encodedLiteral 7++[192#8]++encodedLiteral 8++[0#8]

theorem render_snapshot (s : Spec.Snapshot) : render s = ReplyJson.snapshot s := by
  simp only [render,literal,argument,ReplyJson.snapshot,show (0 : Fin 9).val = 0 from rfl,show (1 : Fin 9).val = 1 from rfl,show (2 : Fin 9).val = 2 from rfl,show (3 : Fin 9).val = 3 from rfl,show (4 : Fin 9).val = 4 from rfl,show (5 : Fin 9).val = 5 from rfl,show (6 : Fin 9).val = 6 from rfl,show (7 : Fin 9).val = 7 from rfl,show (8 : Fin 9).val = 8 from rfl,show (0 : Fin 8).val = 0 from rfl,show (1 : Fin 8).val = 1 from rfl,show (2 : Fin 8).val = 2 from rfl,show (3 : Fin 8).val = 3 from rfl,show (4 : Fin 8).val = 4 from rfl,show (5 : Fin 8).val = 5 from rfl,show (6 : Fin 8).val = 6 from rfl,show (7 : Fin 8).val = 7 from rfl,List.flatten_cons,List.flatten_nil,List.append_assoc,List.append_nil]

theorem literal_lengths : ∀ i : Fin 9, 0 < (literal i).length ∧ (literal i).length < 16 := by decide +kernel

theorem descriptor_length : descriptor.length = 80 := by decide +kernel
end E5R.Thermostat.JsonProgram
