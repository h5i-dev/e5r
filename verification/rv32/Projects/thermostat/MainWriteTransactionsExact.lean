import Projects.thermostat.MainWriteTransactions
import Projects.thermostat.MainWriteSuccessQuiet
import Projects.thermostat.MainWriteErrorQuiet
import Projects.thermostat.MainWriteRoundExact
import Projects.thermostat.MainWriteSuccess
import Projects.thermostat.MainWriteError
import Projects.thermostat.MainWriteRound
namespace E5R.Thermostat.MainWriteTransactions
open E5R E5R.Thermostat

theorem success_exact (c : Core) (ram : Word → BitVec 8) (req rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (state : Spec.Snapshot) (cmd : Spec.Command) (res : Spec.Success)
    (hp : c.pc=0x8000195a#32) (h2 : c.get 2=0x80ffeb90#32) (h8 : c.get 8=0x80fff814#32)
    (h18 : c.get 18=1#32) (h22 : c.get 22=1#32) (h24 : c.get 24=0x80fffa2c#32)
    (hm : Memory.Block B 0x80ff0000#32 65536) (happ : AppState.At ram state) (hi : Spec.Inv state)
    (h : MainWriteInput.Ready ram req rawPtr pathPtr bodyPtr raw path body entries first state)
    (hallow : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key")=true)
    (hdecode : WireSpec.decode path body first=.ok cmd) (hres : Spec.transition true state cmd=.ok res)
    (close : Bool) (hcap : ramRead ram 0x80fff9fc#32 .w=832#32)
    (htx : ramRead ram (0x80fff814#32+64#32) .w=0x80fff414#32)
    (htxc : ramRead ram (0x80fff814#32+68#32) .w=1024#32)
    (hclose : ram 0x80fff878#32=(if close then 1#8 else 0#8))
    (hs bs : List UartTxLoop.Slot) (hhs : hs.length=(ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot res.reply).length close).length) (hbs : bs.length=(ResponseHeadSpec.body 200 (MainMethod.head (ram 0x80fff9f4#32)) (ReplyJson.snapshot res.reply)).length) :
    ∃ d k after, k≤212*entries.length+18*body.length+7050+UartWriteAll.time (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot res.reply).length close) hs+UartWriteAll.time (ResponseHeadSpec.body 200 (MainMethod.head (ram 0x80fff9f4#32)) (ReplyJson.snapshot res.reply)) bs ∧
      Observed.Steps B img k ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
        (UartTxLoop.events (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot res.reply).length close)++UartTxLoop.events (ResponseHeadSpec.body 200 (MainMethod.head (ram 0x80fff9f4#32)) (ReplyJson.snapshot res.reply))) ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧ d.get 2=0x80ffeb90#32 ∧ d.get 8=0x80fff814#32 ∧ d.sameCsr c ∧
      AppState.At after (Spec.commit state (.ok res)) ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧ d.get 24=0xfffffffe#32 ∧ d.get 21=0xffffffff#32 ∧
      ViewFrame.Region ram after 0x80ffec14#32 2048 := by
  obtain ⟨a,n,ra,bn,ta,post⟩ := MainWriteSuccess.contract_quiet c ram req rawPtr pathPtr bodyPtr raw path body entries first state cmd res
    hp h2 h8 h18 h22 h24 hm happ hi h hallow hdecode hres
  obtain ⟨d,k,after,bk,tk,pd,d2,d8,kd,app,inv,d24,d21,rx⟩ := MainWriteRound.contract_exact c a ram ra n (Spec.commit state (.ok res)) (ReplyJson.snapshot res.reply) 200 close ta post
    hm (Nat.le_trans (JsonCapacity.snapshot_length res.reply) (by decide)) (by decide) (by decide) hcap htx htxc hclose hs bs hhs hbs
  · exact ⟨d,k,after,by omega,tk,pd,d2,d8,kd,app,inv,d24,d21,rx⟩

theorem error_exact (c : Core) (ram : Word → BitVec 8) (req rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (state : Spec.Snapshot) (cmd : Spec.Command) (err : Spec.Error)
    (hp : c.pc=0x8000195a#32) (h2 : c.get 2=0x80ffeb90#32) (h8 : c.get 8=0x80fff814#32)
    (h18 : c.get 18=1#32) (h22 : c.get 22=1#32) (h24 : c.get 24=0x80fffa2c#32)
    (hm : Memory.Block B 0x80ff0000#32 65536) (happ : AppState.At ram state) (hi : Spec.Inv state)
    (h : MainWriteInput.Ready ram req rawPtr pathPtr bodyPtr raw path body entries first state)
    (hallow : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key")=true)
    (hdecode : WireSpec.decode path body first=.ok cmd) (hres : Spec.transition true state cmd=.error err)
    (close : Bool) (hcap : ramRead ram 0x80fff9fc#32 .w=832#32)
    (htx : ramRead ram (0x80fff814#32+64#32) .w=0x80fff414#32)
    (htxc : ramRead ram (0x80fff814#32+68#32) .w=1024#32)
    (hclose : ram 0x80fff878#32=(if close then 1#8 else 0#8))
    (hs bs : List UartTxLoop.Slot) (hhs : hs.length=(ResponseHeadSpec.bytes (ErrorLiterals.status err).toNat (WireSpec.ascii "application/json") (ReplyJson.errorBody err).length close).length) (hbs : bs.length=(ResponseHeadSpec.body (ErrorLiterals.status err).toNat (MainMethod.head (ram 0x80fff9f4#32)) (ReplyJson.errorBody err)).length) :
    ∃ d k after, k≤212*entries.length+18*body.length+3320+UartWriteAll.time (ResponseHeadSpec.bytes (ErrorLiterals.status err).toNat (WireSpec.ascii "application/json") (ReplyJson.errorBody err).length close) hs+UartWriteAll.time (ResponseHeadSpec.body (ErrorLiterals.status err).toNat (MainMethod.head (ram 0x80fff9f4#32)) (ReplyJson.errorBody err)) bs ∧
      Observed.Steps B img k ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
        (UartTxLoop.events (ResponseHeadSpec.bytes (ErrorLiterals.status err).toNat (WireSpec.ascii "application/json") (ReplyJson.errorBody err).length close)++UartTxLoop.events (ResponseHeadSpec.body (ErrorLiterals.status err).toNat (MainMethod.head (ram 0x80fff9f4#32)) (ReplyJson.errorBody err))) ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧ d.get 2=0x80ffeb90#32 ∧ d.get 8=0x80fff814#32 ∧ d.sameCsr c ∧
      AppState.At after (Spec.commit state (.error err)) ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧ d.get 24=0xfffffffe#32 ∧ d.get 21=0xffffffff#32 ∧
      ViewFrame.Region ram after 0x80ffec14#32 2048 := by
  obtain ⟨a,n,ra,bn,ta,post⟩ := MainWriteError.contract_quiet c ram req rawPtr pathPtr bodyPtr raw path body entries first state cmd err
    hp h2 h8 h18 h22 h24 hm happ hi h hallow hdecode hres
  obtain ⟨d,k,after,bk,tk,pd,d2,d8,kd,app,inv,d24,d21,rx⟩ := MainWriteRound.contract_exact c a ram ra n (Spec.commit state (.error err)) (ReplyJson.errorBody err) (ErrorLiterals.status err).toNat close ta post
    hm (by cases err <;> decide +kernel) (by cases err <;> decide +kernel) (by cases err <;> decide +kernel) hcap htx htxc hclose hs bs hhs hbs
  · exact ⟨d,k,after,by omega,tk,pd,d2,d8,kd,app,inv,d24,d21,rx⟩
end E5R.Thermostat.MainWriteTransactions
