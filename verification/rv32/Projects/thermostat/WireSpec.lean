import Projects.thermostat.TrimMath
import Projects.thermostat.Encoding
namespace E5R.Thermostat.WireSpec
open E5R E5R.Thermostat

deriving instance DecidableEq for Spec.Command
deriving instance DecidableEq for Except

def ascii (s : String) : List (BitVec 8) := s.toList.map (fun c => BitVec.ofNat 8 c.toNat)

/-- Independent unsigned parameter grammar from the original Request API.
    Accumulation is unbounded Nat followed by the explicit u32 range check. -/
def parseU32 (bs : List (BitVec 8)) : Option Word :=
  if 1 ≤ bs.length ∧ bs.length ≤ 10 ∧ bs.all DecimalSpec.digit = true then
    let n := DecimalSpec.number bs 0
    if n ≤ 4294967295 then some (BitVec.ofNat 32 n) else none
  else none

def number (mk : BitVec 16 → Spec.Command) (body : List (BitVec 8)) : Except Nat Spec.Command :=
  match DecimalSpec.parse body with
  | some n => .ok (mk n)
  | none => .error 400

def relay (param : Option (List (BitVec 8))) (body : List (BitVec 8)) : Except Nat Spec.Command :=
  match param.bind parseU32 with
  | none => .error 404
  | some n =>
    if n.toNat < 256 then
      if body = ascii "on" then .ok (.relay (n.setWidth 8) true)
      else if body = ascii "off" then .ok (.relay (n.setWidth 8) false)
      else .error 400
    else .error 404

/-- The Wire decoder uses the raw path and trims only the body. Fallback uses
    the first router parameter; path matching itself is a separate obligation. -/
def decode (path body : List (BitVec 8)) (firstParam : Option (List (BitVec 8))) : Except Nat Spec.Command :=
  let body := TrimMath.trim body
  if path = ascii "/state" then .ok .read
  else if path = ascii "/setpoint" then number Spec.Command.setpoint body
  else if path = ascii "/temp" then number Spec.Command.reportTemp body
  else if path = ascii "/mode" then
    if body = ascii "off" then .ok (.mode .off)
    else if body = ascii "heat" then .ok (.mode .heat)
    else if body = ascii "auto" then .ok (.mode .auto)
    else .error 400
  else relay firstParam body

/-- ABI predicates constrain only live Rust enum bytes. Inactive payload bytes
    may hold prior temporaries and are not silently forced to zero. -/
def CommandWord (w : Word) (cmd : Spec.Command) : Prop :=
  ∀ i : Fin 4, ∀ b : BitVec 8, Encoding.commandByte cmd i = some b → byteOf w i.val = b

def ResultWord (w : Word) : Except Nat Spec.Command → Prop
  | .ok cmd => CommandWord w cmd
  | .error status => byteOf w 0 = 255#8 ∧ (w >>> 16).toNat = status

theorem read_body_independent (body : List (BitVec 8)) (param : Option (List (BitVec 8))) :
    decode (ascii "/state") body param = .ok .read := by simp [decode]

theorem parameter_max : parseU32 (ascii "4294967295") = some (0xffffffff#32) := by decide +kernel
theorem parameter_overflow : parseU32 (ascii "4294967296") = none := by decide +kernel
theorem parameter_no_plus : parseU32 (ascii "+1") = none := by decide +kernel
theorem parameter_ten_zeroes : parseU32 (ascii "0000000000") = some (0#32) := by decide +kernel
theorem parameter_eleven_zeroes : parseU32 (ascii "00000000000") = none := by decide +kernel
theorem setpoint_trim : decode (ascii "/setpoint") (ascii " 215\r\n") none = .ok (.setpoint 215#16) := by decide +kernel
theorem temp_low : decode (ascii "/temp") (ascii "-32768") none = .ok (.reportTemp 32768#16) := by decide +kernel
theorem relay_u8 : decode (ascii "/relay/255") (ascii "on") (some (ascii "255")) = .ok (.relay 255#8 true) := by decide +kernel
theorem relay_overflow : decode (ascii "/relay/256") (ascii "on") (some (ascii "256")) = .error 404 := by decide +kernel
theorem mode_bad_case : decode (ascii "/mode") (ascii "Auto") none = .error 400 := by decide +kernel
end E5R.Thermostat.WireSpec
