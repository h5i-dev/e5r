import Projects.thermostat.MainRequestBuildFrame
import Projects.thermostat.MainRequestStoreWords
import Projects.thermostat.MainRequestPayloadStored
set_option autoImplicit false
namespace E5R.Thermostat.MainRequestMemory
open E5R E5R.Thermostat HttpRequestSpec

def body (ram : Word → BitVec 8) (sp rx : Word) (head : Head) (amount : Nat) (method : Word) :=
  MainRequestPrefixCore.body ram sp rx head.len (head.len+amount) method

def metadata (ram : Word → BitVec 8) (sp rx : Word) (head : Head) (amount : Nat) (method path pathLen query queryLen : Word) :=
  MainRequestPrefixCore.metadata ram sp rx head.len (head.len+amount) method path pathLen query queryLen 1#32 0#32 (BitVec.ofNat 32 amount)
    (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2)

def copied (ram : Word → BitVec 8) (sp rx : Word) (head : Head) (amount : Nat) (method path pathLen query queryLen : Word) :=
  MainRequestHeadCopy.memory (metadata ram sp rx head amount method path pathLen query queryLen) sp

def after (ram : Word → BitVec 8) (sp rx : Word) (head : Head) (amount : Nat) (method path pathLen query queryLen : Word) :=
  MainRequestTailCore.memory (copied ram sp rx head amount method path pathLen query queryLen) sp (BitVec.ofNat 32 head.minor) rx (BitVec.ofNat 32 (head.len+amount))

/-- A definitional notation change for the exact instruction-derived RAM map. -/
theorem actual (ram : Word → BitVec 8) (sp rx : Word) (head : Head) (amount : Nat) (method path pathLen query queryLen : Word) :
    after ram sp rx head amount method path pathLen query queryLen=
      MainRequestBuildCore.memory ram sp rx head.len (head.len+amount) (head.len+amount) method path pathLen query queryLen 1#32 0#32 (BitVec.ofNat 32 amount)
        (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2) (BitVec.ofNat 32 head.minor) := rfl
end E5R.Thermostat.MainRequestMemory
