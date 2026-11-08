import Projects.thermostat.MainWriteReply
import Projects.thermostat.MainWriteResponseQuiet
import Projects.thermostat.MainWriteResponse
import Projects.thermostat.MainSend
import Projects.thermostat.MainCompletion
import Projects.thermostat.ObservedDet
namespace E5R.Thermostat.MainWriteReply
open E5R E5R.Thermostat

theorem contract_exact (c : Core) (ram : Word → BitVec 8) (state : Spec.Snapshot) (io : Word)
    (payload : List (BitVec 8)) (status : Nat) (close : Bool)
    (hp : c.pc=0x8000196c#32) (h2 : c.get 2=0x80ffeb90#32) (h8 : c.get 8=0x80fff814#32)
    (h18 : c.get 18=1#32) (h22 : c.get 22=1#32) (hm : Memory.Block B 0x80ff0000#32 65536)
    (happ : AppState.At ram state) (hi : Spec.Inv state) (hbody : payload.length≤832) (hlo : 200≤status) (hst : status≤599)
    (hv : BodyMemory.At ram 0x80fffd38#32 0x800056a8#32 16#32 (BitVec.ofNat 32 payload.length) (BitVec.ofNat 32 status))
    (hb : Bytes.Span B ram 0x80fff4d4#32 payload)
    (hcap : ramRead ram 0x80fff9fc#32 .w=832#32)
    (htx : ramRead ram (0x80fff814#32+64#32) .w=0x80fff414#32)
    (htxc : ramRead ram (0x80fff814#32+68#32) .w=1024#32)
    (hio : ramRead ram (0x80fff814#32+72#32) .w=io)
    (hclose : ram 0x80fff878#32=(if close then 1#8 else 0#8))
    (hs bs : List UartTxLoop.Slot) (hhs : hs.length=(ResponseHeadSpec.bytes status (WireSpec.ascii "application/json") payload.length close).length)
    (hbs : bs.length=(ResponseHeadSpec.body status (MainMethod.head (ram 0x80fff9f4#32)) payload).length) :
    ∃ d n after, n≤2449+UartWriteAll.time (ResponseHeadSpec.bytes status (WireSpec.ascii "application/json") payload.length close) hs+
        UartWriteAll.time (ResponseHeadSpec.body status (MainMethod.head (ram 0x80fff9f4#32)) payload) bs ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
        (UartTxLoop.events (ResponseHeadSpec.bytes status (WireSpec.ascii "application/json") payload.length close)++
          UartTxLoop.events (ResponseHeadSpec.body status (MainMethod.head (ram 0x80fff9f4#32)) payload)) ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧ d.get 2=0x80ffeb90#32 ∧ d.get 8=0x80fff814#32 ∧ d.sameCsr c ∧
      AppState.At after state ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧ d.get 24=0xfffffffe#32 ∧ d.get 21=0xffffffff#32 ∧
      ViewFrame.Region ram after 0x80ffec14#32 2048 := by
  obtain ⟨a,ra,ta,pa,a2,a8,a9,a24,ka,happA,_,bytes,desc,rxA⟩ := MainWriteResponse.contract_quiet c ram state io payload status close
    hp h2 h8 h18 h22 hm happ hi hbody hst hv hb hcap htx htxc hio hclose
  obtain ⟨b,nb,rb,bn,tb,pb,fb,kb,happB,invB,tagB,closeB,rxB⟩ := MainSend.contract a ra io 0x800056a8#32 status
    (WireSpec.ascii "application/json") payload close (MainMethod.head (ram 0x80fff9f4#32)) state hi happA
    pa a2 a9 hm hbody hlo hst (by decide) ResponseHeadSpec.json_field desc bytes (ResponseLiterals.json _)
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide)) hs bs hhs hbs
  have b2 := (fb 2 (by decide) (by decide)).trans a2
  have b8 := (fb 8 (by decide) (by decide)).trans a8
  have b24 := (fb 24 (by decide) (by decide)).trans a24
  have fpblock : Memory.Block B 0x80fff814#32 1324 := by
    have h := Memory.sub_block hm (off := 63508) (m := 1324) (by decide) (by decide)
    rw [show 0x80ff0000#32+BitVec.ofNat 32 63508=0x80fff814#32 by decide +kernel] at h;exact h
  have tag : ramRead rb (0x80fff814#32+1316#32) .w=0xffffffff#32 := by
    rw [show 0x80fff814#32+1316#32=0x80fffd38#32 by decide +kernel];exact tagB
  have flag : ramRead rb (0x80fff814#32+1320#32) .w=ResponseHeadBodyMath.boolWord close := by
    rw [show 0x80fff814#32+1320#32=0x80fffd3c#32 by decide +kernel];exact closeB
  obtain ⟨d,td,pd,_,d21,fd,kd⟩ := MainCompletion.contract B b rb 0x80fff814#32 close b8 b24 fpblock (by decide) tag flag pb
  have tpre := ta.observed
  refine ⟨d,35+nb+8,rb,by omega,?_,pd,?_,?_,(kd.trans kb).trans ka,happB,invB,?_,d21,?_⟩
  · simpa only [List.append_nil,List.nil_append] using (tpre.trans tb).trans td.observed
  · exact (fd 2 (by decide) (by decide)).trans b2
  · exact (fd 8 (by decide) (by decide)).trans b8
  · exact (fd 24 (by decide) (by decide)).trans b24
  · intro i;exact (rxB i).trans (rxA i)
end E5R.Thermostat.MainWriteReply
