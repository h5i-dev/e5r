import Projects.thermostat.ResponseHeadSpec
import Theories.Logic
namespace E5R.Thermostat.ResponseHeadBodyMath
open E5R E5R.Thermostat

def boolWord (b : Bool) : Word := if b then 1#32 else 0#32

def not204 (status : Nat) : Word := alu .sltu (0 : Word) (BitVec.ofNat 32 status+0xffffff34#32)
def not304 (status : Nat) : Word := alu .sltu (0 : Word) (BitVec.ofNat 32 status+0xfffffed0#32)
def computed (status : Nat) : Word :=
  (not204 status &&& not304 status) &&& ((alu .sltu (BitVec.ofNat 32 status) 200#32) ^^^ 1#32)

theorem value (status : Nat) (hs : status≤599) : computed status=boolWord (ResponseHeadSpec.hasBody status) := by
  have h : ∀ n : Fin 600, computed n.val=boolWord (ResponseHeadSpec.hasBody n.val) := by decide +kernel
  exact h ⟨status,by omega⟩

theorem equal_zero (b : Bool) : taken .eq (boolWord b) (0 : Word)=(!b) := by cases b <;> decide +kernel
theorem not_equal_zero (b : Bool) : taken .ne (boolWord b) (0 : Word)=b := by cases b <;> decide +kernel

theorem ct_name_len (b : Bool) : (boolWord b) <<< 4=(if b then 16#32 else 0#32) := by cases b <;> decide +kernel

theorem crlf_len (b : Bool) : (boolWord b) <<< 1=(if b then 2#32 else 0#32) := by cases b <;> decide +kernel

theorem connection_len (b : Bool) : ((0 : Word)-(boolWord b)) &&& 19#32=(if b then 19#32 else 0#32) := by
  cases b <;> decide +kernel
end E5R.Thermostat.ResponseHeadBodyMath
