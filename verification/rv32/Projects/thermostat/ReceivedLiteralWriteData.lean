import Projects.thermostat.ReceivedLiteralWriteCycle
import Projects.thermostat.MainInitWitness
import Projects.thermostat.MainChunkStreamingWitness
import Projects.thermostat.Blocking
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.ReceivedLiteralWriteWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
inductive Case where | setpoint | temp | mode | range | noAuth | malformed deriving DecidableEq

def kind : Case → RouteLiteralInfo.Kind
  | .setpoint | .range => .setpoint | .temp | .noAuth => .temp | .mode | .malformed => .mode

def command : Case → String
  | .setpoint | .range => "PUT /setpoint" | .temp | .noAuth => "POST /temp" | .mode | .malformed => "PUT /mode"

def authorized : Case → Bool | .noAuth => false | _ => true

def headBytes (which : Case) : List (BitVec 8) := WireSpec.ascii (command which++" HTTP/1.1\r\nHost: x\r\n"++
  (if authorized which then "Authorization: Bearer dev-key\r\n" else "")++"Transfer-Encoding: chunked\r\n\r\n")
def body : Case → List (BitVec 8)
  | .setpoint => WireSpec.ascii "250" | .range => WireSpec.ascii "49" | .temp | .noAuth => WireSpec.ascii "350"
  | .mode => WireSpec.ascii "heat" | .malformed => WireSpec.ascii "x"
def encoded : Case → List (BitVec 8)
  | .setpoint => WireSpec.ascii "3\r\n250\r\n0\r\n\r\n" | .range => WireSpec.ascii "2\r\n49\r\n0\r\n\r\n"
  | .temp | .noAuth => WireSpec.ascii "3\r\n350\r\n0\r\n\r\n" | .mode => WireSpec.ascii "4\r\nheat\r\n0\r\n\r\n"
  | .malformed => WireSpec.ascii "1\r\nx\r\n0\r\n\r\n"
def head : Case → Head
  | .setpoint | .range => ⟨(0,3),(4,13),1,[⟨24,28,30,31⟩,⟨33,46,48,62⟩,⟨64,81,83,90⟩],94,.chunked⟩
  | .temp => ⟨(0,4),(5,10),1,[⟨21,25,27,28⟩,⟨30,43,45,59⟩,⟨61,78,80,87⟩],91,.chunked⟩
  | .mode | .malformed => ⟨(0,3),(4,9),1,[⟨20,24,26,27⟩,⟨29,42,44,58⟩,⟨60,77,79,86⟩],90,.chunked⟩
  | .noAuth => ⟨(0,4),(5,10),1,[⟨21,25,27,28⟩,⟨30,47,49,56⟩],60,.chunked⟩

-- This certificate checks the generated fixture fields against the pure parser.
theorem parsed (which : Case) : HttpRequestBytes.parse (headBytes which) 1024 1024=.done (head which) := by
  cases which <;> decide +kernel

def wire (which : Case) (k : Nat) := (headBytes which++encoded which)[k]?.getD 0#8
def plan (which : Case) : ChunkReceivePlan.Plan := ⟨fun _ => [],fun _ => 129#32,fun k => BitVec.ofNat 32 (wire which k).toNat⟩
def response (which : Case) := ReceivedLiteralWriteCycle.reply (kind which) Spec.initial (headBytes which) (body which) (head which)
def hs (which : Case) (close : Bool) : List UartTxLoop.Slot := List.replicate
  (ResponseHeadSpec.bytes (response which).status (response which).mime (response which).payload.length close).length
  ⟨[],96#32,(by intro x hx;cases hx),(by decide)⟩
def bs (which : Case) : List UartTxLoop.Slot := List.replicate (response which).payload.length
  ⟨[],96#32,(by intro x hx;cases hx),(by decide)⟩

end E5R.Thermostat.ReceivedLiteralWriteWitness
