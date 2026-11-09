import Projects.thermostat.LoopWriteReturn
import Projects.thermostat.LoopResponseReply
import Projects.thermostat.MainWriteReturnJoin
import Projects.thermostat.MainResponseExtractedReply
import Projects.thermostat.MainStatusResponse
set_option autoImplicit false
namespace E5R.Thermostat.LoopStatusReturn
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
abbrev sp : Word := 0x80ffeb90#32
abbrev fp : Word := 0x80fff814#32

/-- Actual empty-MIME/body status return from any of the four real call sites,
    with actualx18=2, pointer1, zero lengths and no Content-Type header. -/
theorem contract_exact (kind : Fin 4) (c : Core) (ram : Word → BitVec 8) (state : Spec.Snapshot) (io : Word) (status : Nat) (close : Bool)
    (hp : c.pc=MainWriteReturnJoin.entry kind) (h2 : c.get 2=sp) (h8 : c.get 8=fp) (h18 : c.get 18=2#32) (h22 : c.get 22=1#32)
    (hm : Memory.Block B 0x80ff0000#32 65536) (happ : AppState.At ram state) (hi : Spec.Inv state) (hlo : 200≤status) (hst : status≤599)
    (hv : StatusMemory.At ram 0x80fffd38#32 (BitVec.ofNat 32 status))
    (hcap : ramRead ram 0x80fff9fc#32 .w=832#32) (htx : ramRead ram (fp+64#32) .w=0x80fff414#32)
    (htxc : ramRead ram (fp+68#32) .w=1024#32) (hio : ramRead ram (fp+72#32) .w=io) (hclose : ram 0x80fff878#32=Encoding.boolByte close)
    (hs : List UartTxLoop.Slot) (hhs : hs.length=(ResponseHeadSpec.bytes status [] 0 close).length) :
    ∃ d n after, n≤2450+UartWriteAll.time (ResponseHeadSpec.bytes status [] 0 close) hs+UartWriteAll.time [] [] ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs) (UartTxLoop.events (ResponseHeadSpec.bytes status [] 0 close)) ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧ d.get 2=sp ∧ d.get 8=fp ∧ d.sameCsr c ∧
      AppState.At after state ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧ ViewFrame.Region ram after 0x80ffec14#32 2048 ∧
      ViewFrame.Region ram after fp 96 ∧ ViewFrame.Region ram after 0x80ffeba0#32 4 ∧
      ViewFrame.Region ram after 0x80ffebd8#32 60 ∧ d.get 19=c.get 19 ∧ d.get 22=c.get 22 ∧ d.get 18=c.get 18 ∧ d.get 23=c.get 23 ∧ d.get 26=c.get 26 ∧ d.get 21=0xffffffff#32 := by
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block hm (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have small : (BitVec.ofNat 32 status).toNat<65536 := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : status<2^32)]
    omega
  obtain ⟨a,na,mid,ba,ta,pa,a2,a8,a22,a12,a11,a20,a10,a13,a9,a24,ac,live,a19,a18,a23,a26⟩ :=
    LoopWriteReturn.extract kind c ram 1#32 0#32 0#32 (BitVec.ofNat 32 status) hp h2 h8 h18 h22 stack (MainStatusResponse.as_body hv) small
  have region (off size : Nat) (bound : off+size≤3780) : ViewFrame.Region ram mid (sp+BitVec.ofNat 32 off) size := by
    intro i
    have byte := live ⟨off+i.val,by have := i.isLt;omega⟩
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using byte
  have word (off : Nat) (bound : off+4≤532) : ramRead mid (fp+BitVec.ofNat 32 off) .w=ramRead ram (fp+BitVec.ofNat 32 off) .w := by
    have frame : ViewFrame.Region ram mid fp 532 := by simpa only [show sp+3204#32=fp by decide +kernel] using region 3204 532 (by decide)
    exact ViewFrame.word frame off bound
  have app := AppState.preserve ram mid state happ (by
    simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using region 44 25 (by decide))
  have cap : ramRead mid 0x80fff9fc#32 .w=832#32 := by
    have atWord := word 488 (by decide)
    simpa only [show fp+BitVec.ofNat 32 (488 : Nat)=0x80fff9fc#32 by decide +kernel] using atWord.trans hcap
  have flag : mid 0x80fff878#32=Encoding.boolByte close := by
    have byte := region 3304 1 (by decide) ⟨0,by decide⟩
    simpa only [BitVec.add_zero,show sp+3304#32=0x80fff878#32 by decide +kernel] using byte.trans hclose
  have emptyBody : ResponseHeadSpec.body status (MainMethod.head (mid 0x80fff9f4#32)) []=[] := by simp only [ResponseHeadSpec.body,ite_self]
  obtain ⟨d,nb,after,bb,tb,pd,d2,d8,dc,appAfter,inv,_,d21,rx,low,capFrame,routes,d19,d22,d18,d23,d26⟩ := LoopResponseReply.contract_exact false a mid state io [] status close
    pa a2 a8 a22 hm app hi (by decide) hlo hst a12 a11 a20 a10 a13 a9 a24 (Bytes.empty B mid _) cap
    ((word 64 (by decide)).trans htx) ((word 68 (by decide)).trans htxc) ((word 72 (by decide)).trans hio) flag hs [] hhs (by rw [emptyBody];rfl)
  rw [emptyBody,show MainResponseExtractedReply.mime false=[] from rfl] at bb tb
  simp only [List.length_nil] at bb tb
  refine ⟨d,na+nb,after,by omega,?_,pd,d2,d8,dc.trans ac,appAfter,inv,?_,?_,?_,?_,?_,?_,?_,?_,?_,d21⟩
  · simpa only [UartTxLoop.reads,List.flatMap_nil,UartTxLoop.events,List.map_nil,List.append_nil,List.nil_append] using ta.observed.trans tb
  · intro i
    have byte := region 132 2048 (by decide) i
    have equal : mid (0x80ffec14#32+BitVec.ofNat 32 i.val)=ram (0x80ffec14#32+BitVec.ofNat 32 i.val) := by
      simpa only [show sp+132#32=0x80ffec14#32 by decide +kernel] using byte
    exact (rx i).trans equal
  · intro i
    have byte := region 3204 96 (by decide) i
    exact (low i).trans (by simpa only [show sp+3204#32=fp by decide +kernel] using byte)
  · intro i
    have byte := region 16 4 (by decide) i
    exact (capFrame i).trans (by simpa only [show sp+16#32=0x80ffeba0#32 by decide +kernel] using byte)
  · intro i
    have byte := region 72 60 (by decide) i
    exact (routes i).trans (by simpa only [show sp+72#32=0x80ffebd8#32 by decide +kernel] using byte)
  · exact d19.trans a19
  · exact d22.trans (a22.trans h22.symm)
  · exact d18.trans a18
  · exact d23.trans a23
  · exact d26.trans a26
end E5R.Thermostat.LoopStatusReturn
