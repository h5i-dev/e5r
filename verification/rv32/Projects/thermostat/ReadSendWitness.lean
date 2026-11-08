import Projects.thermostat.ReadSend
import Projects.thermostat.ReadWitness
import Projects.thermostat.UartWriteWitness
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ReadSendWitness
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def core : Core := ((ReadWitness.freeCore.set 20 832#32).set 24 0x80fff4d4#32).set 22 1#32

def ram (close head : Bool) (a : Word) : BitVec 8 :=
  if a=0x80ffebcc#32 then 124#8 else if a=0x80ffebcd#32 then 91#8 else if a=0x80ffebcf#32 then 128#8
  else if a=0x80ffebd0#32 then 7#8 else if a=0x80ffebd4#32 then 1#8
  else if a=0x80fff9fc#32 then 64#8 else if a=0x80fff9fd#32 then 3#8
  else if a=0x80fff854#32 then 20#8 else if a=0x80fff855#32 then 244#8 else if a=0x80fff856#32 then 255#8
  else if a=0x80fff857#32 then 128#8 else if a=0x80fff859#32 then 4#8
  else if a=0x80fff878#32 then if close then 1#8 else 0#8
  else if a=0x80fff9f4#32 then if head then 1#8 else 0#8
  else ReadWitness.freeRam a

theorem pre (close head : Bool) : ReadAcquire.Pre B core (ram close head) Spec.initial := by
  cases close <;> cases head <;> refine ⟨rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_⟩
  all_goals first
    | (unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
    | (change ∀ i : Fin 10, ram _ _ (0x80ffebc0#32+BitVec.ofNat 32 i.val)=Encoding.snapshotByte Spec.initial i;decide +kernel)
    | (change ∀ i : Fin 4, ∀ b, Encoding.commandByte .read i=some b → ram _ _ (0x80fffb10#32+BitVec.ofNat 32 i.val)=b;decide +kernel)
    | decide +kernel

theorem app (close head : Bool) : AppState.At (ram close head) Spec.initial := by
  cases close <;> cases head <;> refine ⟨?_,?_,?_,?_,?_⟩
  all_goals first
    | (change ∀ i : Fin 10, ram _ _ (0x80ffebc0#32+BitVec.ofNat 32 i.val)=Encoding.snapshotByte Spec.initial i;decide +kernel)
    | decide +kernel

theorem capacity (close head : Bool) : ramRead (ram close head) 0x80fff9fc#32 .w=832#32 := by
  cases close <;> cases head <;> decide +kernel

theorem tx_pointer (close head : Bool) : ramRead (ram close head) (0x80fff814#32+64#32) .w=0x80fff414#32 := by
  cases close <;> cases head <;> decide +kernel

theorem tx_capacity (close head : Bool) : ramRead (ram close head) (0x80fff814#32+68#32) .w=1024#32 := by
  cases close <;> cases head <;> decide +kernel

theorem close_byte (close head : Bool) : ram close head 0x80fff878#32=(if close then 1#8 else 0#8) := by
  cases close <;> cases head <;> decide +kernel

theorem head_byte (close head : Bool) : MainMethod.head (ram close head 0x80fff9f4#32)=head := by
  cases close <;> cases head <;> decide +kernel

def headerSlots (close : Bool) := List.replicate
  (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot Spec.initial).length close).length UartWriteWitness.slot1

def bodySlots (head : Bool) := List.replicate
  (ResponseHeadSpec.body 200 head (ReplyJson.snapshot Spec.initial)).length UartWriteWitness.slot1

/-- A satisfiable actual main-buffer Read-to-UART transaction, including one
    not-ready poll per transmitted byte and the persisted App/borrow invariant. -/
theorem execution (close head : Bool) : ∃ d n after reads events,
    Observed.Steps B img n ⟨core,ram close head⟩ ⟨d,after⟩ reads events ∧ d.pc=0x80001784#32 ∧
      d.get 2=0x80ffeb90#32 ∧ d.get 8=0x80fff814#32 ∧ AppState.At after Spec.initial ∧
      Engine.InvariantAt after 0x80ffebbc#32 ∧ ramRead after 0x80ffebbc#32 .w=0#32 ∧
      Observed.output events=ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot Spec.initial).length close++
        ResponseHeadSpec.body 200 head (ReplyJson.snapshot Spec.initial) ∧
      ramRead after 0x80fffd3c#32 .w=ResponseHeadBodyMath.boolWord close := by
  obtain ⟨d,n,after,prefixReads,_,td,pd,sp,fp,_,ha,hi,_,hc,_⟩ := ReadSend.contract core (ram close head) Spec.initial close
    (pre close head) Spec.initial_inv (app close head)
    (by change Memory.Block B 0x80ff0000#32 65536;unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
    rfl rfl rfl (capacity close head) (tx_pointer close head) (tx_capacity close head) (close_byte close head)
    (headerSlots close) (bodySlots head) (by exact List.length_replicate) (by rw [head_byte];exact List.length_replicate)
  rw [head_byte] at td
  have projection := Send.projection 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot Spec.initial) close head (headerSlots close) (bodySlots head)
  exact ⟨d,n,after,_,_,td,pd,sp,fp,ha,hi,ha.available,projection.2,hc⟩

theorem initial_json : ReplyJson.snapshot Spec.initial=WireSpec.ascii
    "{\"setpoint_dc\":200,\"temp_dc\":200,\"heater\":false,\"relays\":[false,false,false,false],\"mode\":\"off\"}" := by decide +kernel

theorem get_packet : ∃ d n after reads events,
    Observed.Steps B img n ⟨core,ram false false⟩ ⟨d,after⟩ reads events ∧ d.pc=0x80001784#32 ∧
      Engine.InvariantAt after 0x80ffebbc#32 ∧ ramRead after 0x80ffebbc#32 .w=0#32 ∧
      Observed.output events=WireSpec.ascii "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: 96\r\n\r\n"++
        WireSpec.ascii "{\"setpoint_dc\":200,\"temp_dc\":200,\"heater\":false,\"relays\":[false,false,false,false],\"mode\":\"off\"}" := by
  obtain ⟨d,n,after,reads,events,td,pd,_,_,_,hi,hb,ho,_⟩ := execution false false
  refine ⟨d,n,after,reads,events,td,pd,hi,hb,?_⟩
  rw [show ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot Spec.initial).length false=
    WireSpec.ascii "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: 96\r\n\r\n" by decide +kernel] at ho
  rw [show ResponseHeadSpec.body 200 false (ReplyJson.snapshot Spec.initial)=ReplyJson.snapshot Spec.initial by rfl,initial_json] at ho
  exact ho

theorem head_packet : ∃ d n after reads events,
    Observed.Steps B img n ⟨core,ram false true⟩ ⟨d,after⟩ reads events ∧ d.pc=0x80001784#32 ∧
      Engine.InvariantAt after 0x80ffebbc#32 ∧ ramRead after 0x80ffebbc#32 .w=0#32 ∧
      Observed.output events=WireSpec.ascii "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: 96\r\n\r\n" := by
  obtain ⟨d,n,after,reads,events,td,pd,_,_,_,hi,hb,ho,_⟩ := execution false true
  refine ⟨d,n,after,reads,events,td,pd,hi,hb,?_⟩
  rw [ResponseHeadSpec.head_empty,List.append_nil] at ho
  rw [show ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot Spec.initial).length false=
    WireSpec.ascii "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: 96\r\n\r\n" by decide +kernel] at ho
  exact ho
end E5R.Thermostat.ReadSendWitness
