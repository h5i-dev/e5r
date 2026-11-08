import Projects.thermostat.ReplyJson
import Projects.thermostat.ModeLiterals
namespace E5R.Thermostat.FormatValue
open E5R E5R.Thermostat

inductive Value where
  | signed (ptr : Word) (value : BitVec 16)
  | boolean (ptr : Word) (value : Bool)
  | mode (ptr : Word) (value : Spec.Mode)

def pointer : Value → Word
  | .signed p _ | .boolean p _ | .mode p _ => p

def entry : Value → Word
  | .signed _ _ => 0x80004e5e#32
  | .boolean _ _ => 0x80005112#32
  | .mode _ _ => 0x8000228c#32

def bytes : Value → List (BitVec 8)
  | .signed _ v => ReplyJson.signed v
  | .boolean _ b => ReplyJson.boolean b
  | .mode _ m => ReplyJson.mode m
end E5R.Thermostat.FormatValue

namespace E5R.Thermostat.FormatValue
open E5R

theorem entry_even (v : Value) : entry v &&& ~~~1 = entry v := by cases v <;> simp only [entry] <;> decide +kernel
end E5R.Thermostat.FormatValue

namespace E5R.Thermostat.FormatValue

def size : Value → Nat
  | .signed _ _ => 2 | .boolean _ _ => 1 | .mode _ _ => 8
end E5R.Thermostat.FormatValue
