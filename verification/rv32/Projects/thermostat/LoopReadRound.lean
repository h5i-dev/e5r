import Projects.thermostat.LoopReadSend
import Projects.thermostat.ReadRound
import Projects.thermostat.ReadSendExact
import Projects.thermostat.ReadSend
import Projects.thermostat.MainCompletion
namespace E5R.Thermostat.LoopReadRound
open ReadRound
open E5R E5R.Thermostat

/-- The actual main result dispatch completes a Read response, choosing the
    reset-loop entry on close and the buffer-compaction entry on keep-alive. -/
theorem contract_exact (c : Core) (ram : Word → BitVec 8) (state : Spec.Snapshot) (close : Bool)
    (h : ReadAcquire.Pre B c ram state) (hi : Spec.Inv state) (happ : AppState.At ram state)
    (hm : Memory.Block B 0x80ff0000#32 65536)
    (h24 : c.get 24=0x80fff4d4#32) (h20 : c.get 20=832#32) (h22 : c.get 22=1#32)
    (hcap : ramRead ram 0x80fff9fc#32 .w=832#32)
    (htx : ramRead ram (0x80fff814#32+64#32) .w=0x80fff414#32)
    (htxcap : ramRead ram (0x80fff814#32+68#32) .w=1024#32)
    (hclose : ram 0x80fff878#32=(if close then 1#8 else 0#8))
    (hs bs : List UartTxLoop.Slot)
    (hhs : hs.length=(ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot state).length close).length)
    (hbs : bs.length=(ResponseHeadSpec.body 200 (MainMethod.head (ram 0x80fff9f4#32)) (ReplyJson.snapshot state)).length) :
    ∃ d n after,
      n≤6552+UartWriteAll.time (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot state).length close) hs+
        UartWriteAll.time (ResponseHeadSpec.body 200 (MainMethod.head (ram 0x80fff9f4#32)) (ReplyJson.snapshot state)) bs ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
        (UartTxLoop.events (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot state).length close)++
          UartTxLoop.events (ResponseHeadSpec.body 200 (MainMethod.head (ram 0x80fff9f4#32)) (ReplyJson.snapshot state))) ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧ d.get 2=0x80ffeb90#32 ∧ d.get 8=0x80fff814#32 ∧ d.sameCsr c ∧
      AppState.At after state ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧
      ramRead after 0x80fffd38#32 .w=0xffffffff#32 ∧ ramRead after 0x80fffd3c#32 .w=ResponseHeadBodyMath.boolWord close ∧ d.get 24=0xfffffffe#32 ∧ d.get 21=0xffffffff#32 ∧
      ViewFrame.Region ram after 0x80fff814#32 96 ∧ ViewFrame.Region ram after 0x80ffeba0#32 4 ∧
      ViewFrame.Region ram after 0x80ffebd8#32 60 ∧ d.get 19=c.get 19 ∧ d.get 22=1#32 ∧ d.get 18=2#32 ∧ d.get 23=c.get 23 ∧ d.get 26=c.get 26 := by
  obtain ⟨a,na,ra,ba,ta,pa,a2,a8,ka,happAfter,hinv,hresult,hclosed,a24,low,capFrame,routes,a19,a22,a18,a23,a26⟩ := LoopReadSend.contract_exact c ram state close h hi happ hm
    h24 h20 h22 hcap htx htxcap hclose hs bs hhs hbs
  have hfp : Memory.Block B 0x80fff814#32 1324 := by
    have hb := Memory.sub_block hm (off := 63508) (m := 1324) (by decide) (by decide)
    rw [show 0x80ff0000#32+BitVec.ofNat 32 63508=0x80fff814#32 by decide +kernel] at hb
    exact hb
  have tag : ramRead ra (0x80fff814#32+1316#32) .w=0xffffffff#32 := by
    rw [show 0x80fff814#32+1316#32=0x80fffd38#32 by decide +kernel]
    exact hresult
  have flag : ramRead ra (0x80fff814#32+1320#32) .w=ResponseHeadBodyMath.boolWord close := by
    rw [show 0x80fff814#32+1320#32=0x80fffd3c#32 by decide +kernel]
    exact hclosed
  obtain ⟨d,td,pd,d10,d21,fd,kd⟩ := MainCompletion.contract B a ra 0x80fff814#32 close a8 a24 hfp (by decide) tag flag pa
  refine ⟨d,na+8,ra,by omega,?_,pd,?_,?_,kd.trans ka,happAfter,hinv,hresult,hclosed,?_,d21,low,capFrame,routes,?_,?_,?_,?_,?_⟩
  · simpa only [List.append_nil] using ta.trans td.observed
  · exact (fd 2 (by decide) (by decide)).trans a2
  · exact (fd 8 (by decide) (by decide)).trans a8
  · exact (fd 24 (by decide) (by decide)).trans a24
  · exact (fd 19 (by decide) (by decide)).trans a19
  · exact (fd 22 (by decide) (by decide)).trans a22
  · exact (fd 18 (by decide) (by decide)).trans a18
  · exact (fd 23 (by decide) (by decide)).trans a23
  · exact (fd 26 (by decide) (by decide)).trans a26
end E5R.Thermostat.LoopReadRound
