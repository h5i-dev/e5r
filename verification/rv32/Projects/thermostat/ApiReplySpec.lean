import Projects.thermostat.ApiRouting
import Projects.thermostat.MainCloseSpec
set_option autoImplicit false
namespace E5R.Thermostat.ApiReplySpec
open E5R E5R.Thermostat ApiRequestSpec

def close (r : Fixed11) : Bool := MainCloseSpec.mustClose 1 1 r.bytes
  (r.head.headers.map HttpRequestBytes.entry)

def bytes (r : Fixed11) (s : Spec.Snapshot) : ApiRequestSpec.Bytes :=
  let reply := r.reply s
  ResponseHeadSpec.bytes reply.status reply.mime reply.payload.length (close r)++reply.payload

theorem temp (s : Spec.Snapshot) (raw body : ApiRequestSpec.Bytes) (entries : List HeaderSpec.Entry) :
    ApiWriteHttpSpec.run s (WireSpec.ascii "/temp") none raw body entries=TempHttpSpec.run s raw body entries := by
  unfold ApiWriteHttpSpec.run TempHttpSpec.run
  rw [TempHttpSpec.decode]
  cases AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") with
  | false => rfl
  | true =>
    cases DecimalSpec.parse (TrimMath.trim body) <;> rfl

theorem write_inv (s : Spec.Snapshot) (path : ApiRequestSpec.Bytes) (first : Option ApiRequestSpec.Bytes)
    (raw body : ApiRequestSpec.Bytes) (entries : List HeaderSpec.Entry) (inv : Spec.Inv s) :
    Spec.Inv (ApiWriteHttpSpec.run s path first raw body entries).state := by
  unfold ApiWriteHttpSpec.run
  split
  next allowed =>
    cases decoded : WireSpec.decode path body first with
    | error status => exact inv
    | ok cmd =>
      dsimp only
      cases outcome : Spec.transition true s cmd with
      | error err => exact inv
      | ok result =>
        have committed := Spec.commit_inv true s cmd inv
        rw [outcome] at committed
        exact committed
  next denied => exact inv

theorem invariant (r : Fixed11) (s : Spec.Snapshot) (inv : Spec.Inv s) : Spec.Inv (r.reply s).state := by
  unfold Fixed11.reply
  cases r.route with
  | state => exact inv
  | setpoint | temp | mode | relay segment => exact write_inv _ _ _ _ _ _ inv

end E5R.Thermostat.ApiReplySpec
