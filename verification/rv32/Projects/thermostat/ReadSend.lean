import Projects.thermostat.ReadResponseFull
import Projects.thermostat.MainSend
import Projects.thermostat.ObservedDet
namespace E5R.Thermostat.ReadSend
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

/-- Separate real Read acquisition/transaction/JSON/common response stores,
    actual main send call, both UART writes and return to main. Input parsing
    is upstream. The legacy deterministic prefix retains an existential read
    log; it is not silently asserted to have no ignored device reads. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (state : Spec.Snapshot) (close : Bool)
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
    ∃ d n after prefixReads,
      n≤6544+UartWriteAll.time (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot state).length close) hs+
        UartWriteAll.time (ResponseHeadSpec.body 200 (MainMethod.head (ram 0x80fff9f4#32)) (ReplyJson.snapshot state)) bs ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (prefixReads++(UartTxLoop.reads hs++UartTxLoop.reads bs))
        (UartTxLoop.events (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot state).length close)++
          UartTxLoop.events (ResponseHeadSpec.body 200 (MainMethod.head (ram 0x80fff9f4#32)) (ReplyJson.snapshot state))) ∧
      d.pc=0x80001784#32 ∧ d.get 2=0x80ffeb90#32 ∧ d.get 8=0x80fff814#32 ∧ d.sameCsr c ∧
      AppState.At after state ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧
      ramRead after 0x80fffd38#32 .w=0xffffffff#32 ∧ ramRead after 0x80fffd3c#32 .w=ResponseHeadBodyMath.boolWord close ∧ d.get 24=0xfffffffe#32 := by
  let io := ramRead ram (0x80fff814#32+72#32) .w
  obtain ⟨a,na,ra,ba,ta,pa,a2,a8,ka,_,hbytes,hstate,hborrow,_,a9,hdesc,hkeys,a24⟩ := ReadResponseFull.contract_inv c ram 0x80fff4d4#32 832 state
    0x80fff414#32 io close htx htxcap rfl hclose h hi hm h24 h20 h22 (by decide) (by decide)
    (by change Memory.Block B 0x80fff4d4#32 832;unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
    (by decide) hcap
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
  have appRead : AppState.At ra state := by
    refine ⟨hstate,hborrow,?_,?_,?_⟩
    · have hh := ViewFrame.word hkeys 0 (by decide)
      simpa only [BitVec.add_zero] using hh.trans happ.keyPtr
    · have hh := ViewFrame.word hkeys 4 (by decide)
      rw [show 0x80ffebcc#32+4#32=0x80ffebd0#32 by decide +kernel] at hh
      exact hh.trans happ.keyLen
    · have hh := hkeys ⟨8,by decide⟩
      rw [show 0x80ffebcc#32+8#32=0x80ffebd4#32 by decide +kernel] at hh
      exact hh.trans happ.principal
  have hl : (ReplyJson.snapshot state).length≤832 := Nat.le_trans (JsonCapacity.snapshot_length state) (by decide)
  obtain ⟨d,nd,after,bd,td,pd,fd,kd,happAfter,hinv,hresult,hclosed,_⟩ := MainSend.contract a ra io 0x800056a8#32 200
    (WireSpec.ascii "application/json") (ReplyJson.snapshot state) close (MainMethod.head (ram 0x80fff9f4#32)) state hi appRead
    pa a2 a9 hm hl (by decide) (by decide) (by decide) ResponseHeadSpec.json_field hdesc hbytes (ResponseLiterals.json _)
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide)) hs bs hhs hbs
  obtain ⟨prefixReads,tpre⟩ := ObservedDet.complete ta
  refine ⟨d,na+nd,after,prefixReads,by omega,?_,pd,?_,?_,kd.trans ka,happAfter,hinv,hresult,hclosed,(fd 24 (by decide) (by decide)).trans a24⟩
  · simpa only [List.nil_append] using tpre.trans td
  · exact (fd 2 (by decide) (by decide)).trans a2
  · exact (fd 8 (by decide) (by decide)).trans a8
end E5R.Thermostat.ReadSend
