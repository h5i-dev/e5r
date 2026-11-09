import Projects.thermostat.ApiReplySpec
set_option autoImplicit false
namespace E5R.Thermostat.LoopSpec
open E5R E5R.Thermostat ApiRequestSpec
/-- Input count is the number already completed within this actual serve. -/
def close (r : Fixed11) (served : Nat) : Bool := MainCloseSpec.mustClose 1 (served+1) r.bytes
  (r.head.headers.map HttpRequestBytes.entry)
def nextCount (r : Fixed11) (served : Nat) : Nat := if close r served then 0 else served+1
def bytes (r : Fixed11) (s : Spec.Snapshot) (served : Nat) : ApiRequestSpec.Bytes :=
  let reply := r.reply s
  ResponseHeadSpec.bytes reply.status reply.mime reply.payload.length (close r served)++reply.payload
end E5R.Thermostat.LoopSpec
