import Projects.thermostat.ResponseHeadSpec
import Projects.thermostat.HttpDecDigitsSpec
namespace E5R.Thermostat.ResponseHeadPrefixSpec
open E5R E5R.Thermostat

def bytes (status : Nat) := WireSpec.ascii "HTTP/1.1 " ++ ReplyJson.decimal status ++ WireSpec.ascii " "
def listing (status : Nat) : List (BitVec 8) := [72#8,84#8,84#8,80#8,47#8,49#8,46#8,49#8,32#8,
  DecimalDigits.digit (status/100),DecimalDigits.digit ((status/10)%10),DecimalDigits.digit (status%10),32#8]

theorem expanded (status : Nat) (hlo : 100≤status) (hhi : status≤599) : bytes status=listing status := by
  rw [bytes,HttpDecDigitsSpec.cases status (by omega),if_neg (show ¬status<10 by omega),if_neg (show ¬status<100 by omega)]
  rfl

theorem length (status : Nat) (hlo : 100≤status) (hhi : status≤599) : (bytes status).length=13 := by
  rw [expanded status hlo hhi]
  rfl
end E5R.Thermostat.ResponseHeadPrefixSpec
