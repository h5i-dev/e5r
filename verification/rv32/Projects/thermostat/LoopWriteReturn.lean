import Projects.thermostat.MainWriteReturnJoin
import Projects.thermostat.LoopResponseReply
namespace E5R.Thermostat.LoopWriteReturn
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
abbrev sp : Word := 0x80ffeb90#32
abbrev fp : Word := 0x80fff814#32

def entry (kind : Fin 4) : Word :=
  if kind=0 then 0x80001628#32 else if kind=1 then 0x80001604#32 else if kind=2 then 0x800015e0#32 else 0x8000196c#32

/-- The four actual return sites converge without assuming the old x18=1. -/
theorem extract (kind : Fin 4) (c : Core) (ram : Word → BitVec 8) (ct len used status : Word)
    (hp : c.pc=entry kind) (h2 : c.get 2=sp) (h8 : c.get 8=fp) (h18 : c.get 18=2#32) (h22 : c.get 22=1#32)
    (hm : Memory.Block B sp 5232) (hv : BodyMemory.At ram 0x80fffd38#32 ct len used status) (hst : status.toNat<65536) :
    ∃ d n after, n≤13 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧ d.pc=0x80001710#32 ∧
      d.get 2=sp ∧ d.get 8=fp ∧ d.get 22=1#32 ∧ d.get 12=ct ∧ d.get 11=len ∧ d.get 20=used ∧ d.get 10=status ∧
      d.get 13=0#32 ∧ d.get 9=0x80fff878#32 ∧ d.get 24=0xfffffffe#32 ∧ d.sameCsr c ∧ ViewFrame.Region ram after sp 3780 ∧ d.get 19=c.get 19 ∧ d.get 18=c.get 18 ∧ d.get 23=c.get 23 ∧ d.get 26=c.get 26 := by
  have flag : ram 0x80fffd46#32=0#8 := BodyResponseView.extra hv
  have ctWord : ramRead ram 0x80fffd38#32 .w=ct := by
    simpa only [Nat.mul_zero,BitVec.add_zero,ite_true] using BodyResponseView.word hv ⟨0,by decide⟩
  have lenWord : ramRead ram 0x80fffd3c#32 .w=len := by
    simpa only [show (4*1 : Nat)=4 by decide,show 0x80fffd38#32+4#32=0x80fffd3c#32 by decide +kernel,
      show (1 : Nat)≠0 by decide,ite_false,ite_true] using BodyResponseView.word hv ⟨1,by decide⟩
  have usedWord : ramRead ram 0x80fffd40#32 .w=used := by
    simpa only [show (4*2 : Nat)=8 by decide,show 0x80fffd38#32+8#32=0x80fffd40#32 by decide +kernel,
      show (2 : Nat)≠0 by decide,show (2 : Nat)≠1 by decide,ite_false] using BodyResponseView.word hv ⟨2,by decide⟩
  have statusHalf : extend .h false (ramRead ram 0x80fffd44#32 .h)=status := by
    simpa only [show 0x80fffd38#32+12#32=0x80fffd44#32 by decide +kernel] using BodyResponseView.half hv hst
  have kinds : kind=0 ∨ kind=1 ∨ kind=2 ∨ kind=3 := by omega
  rcases kinds with rfl|rfl|rfl|rfl
  · obtain ⟨d,steps,pd,d13,d12,d11,d20,d10,d6,d9,d24,keep,csr⟩ := MainSetpointReturn.contract B c ram ct len used status h2 h8 h18 h22 hm ctWord lenWord usedWord statusHalf flag hp
    refine ⟨d,13,MainSetpointReturn.memory ram ct len used status,by decide,steps,pd,?_,?_,?_,d12,d11,d20,d10,d13,d9,d24,csr,?_,?_,?_,?_,?_⟩
    · exact (keep 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2
    · exact (keep 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8
    · exact (keep 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22
    · simpa only [BitVec.add_zero] using MainSetpointReturn.frame ram ct len used status 0 3780 (by decide) (Or.inl (by decide))
    · exact keep 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · obtain ⟨d,steps,pd,d13,d12,d11,d20,d10,d6,d9,d24,keep,csr⟩ := MainTempReturn.contract B c ram ct len used status h2 h8 h18 h22 hm ctWord lenWord usedWord statusHalf flag hp
    refine ⟨d,13,MainTempReturn.memory ram ct len used status,by decide,steps,pd,?_,?_,?_,d12,d11,d20,d10,d13,d9,d24,csr,?_,?_,?_,?_,?_⟩
    · exact (keep 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2
    · exact (keep 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8
    · exact (keep 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22
    · simpa only [BitVec.add_zero] using MainTempReturn.frame ram ct len used status 0 3780 (by decide) (Or.inl (by decide))
    · exact keep 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · obtain ⟨d,steps,pd,d13,d12,d11,d20,d10,d6,d9,d24,keep,csr⟩ := MainModeReturn.contract B c ram ct len used status h2 h8 h18 h22 hm ctWord lenWord usedWord statusHalf flag hp
    refine ⟨d,12,MainModeReturn.memory ram ct len used status,by decide,steps,pd,?_,?_,?_,d12,d11,d20,d10,d13,d9,d24,csr,?_,?_,?_,?_,?_⟩
    · exact (keep 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2
    · exact (keep 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8
    · exact (keep 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22
    · simpa only [BitVec.add_zero] using MainModeReturn.frame ram ct len used status 0 3780 (by decide) (Or.inl (by decide))
    · exact keep 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · obtain ⟨d,steps,pd,d13,d9,d12,d11,d20,d10,d6,d24,keep,csr⟩ := MainRelayReturn.contract B c ram ct len used status h2 h8 h18 h22 hm ctWord lenWord usedWord statusHalf flag hp
    refine ⟨d,12,ram,by decide,steps,pd,?_,?_,?_,d12,d11,d20,d10,d13,d9,d24,csr,?_,?_,?_,?_,?_⟩
    · exact (keep 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2
    · exact (keep 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8
    · exact (keep 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22
    · intro i;rfl
    · exact keep 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Complete exact JSON HTTP/UART response from each real call-return PC.
    The actual caller/routing/handler must establish its BodyMemory/payload. -/
theorem contract_exact (kind : Fin 4) (c : Core) (ram : Word → BitVec 8) (state : Spec.Snapshot) (io : Word)
    (payload : List (BitVec 8)) (status : Nat) (close : Bool)
    (hp : c.pc=entry kind) (h2 : c.get 2=sp) (h8 : c.get 8=fp) (h18 : c.get 18=2#32) (h22 : c.get 22=1#32)
    (hm : Memory.Block B 0x80ff0000#32 65536) (happ : AppState.At ram state) (hi : Spec.Inv state)
    (hbody : payload.length≤832) (hlo : 200≤status) (hst : status≤599)
    (hv : BodyMemory.At ram 0x80fffd38#32 0x800056a8#32 16#32 (BitVec.ofNat 32 payload.length) (BitVec.ofNat 32 status))
    (hb : Bytes.Span B ram 0x80fff4d4#32 payload)
    (hcap : ramRead ram 0x80fff9fc#32 .w=832#32)
    (htx : ramRead ram (fp+64#32) .w=0x80fff414#32) (htxc : ramRead ram (fp+68#32) .w=1024#32)
    (hio : ramRead ram (fp+72#32) .w=io) (hclose : ram 0x80fff878#32=Encoding.boolByte close)
    (hs bs : List UartTxLoop.Slot) (hhs : hs.length=(ResponseHeadSpec.bytes status (WireSpec.ascii "application/json") payload.length close).length)
    (hbs : bs.length=(ResponseHeadSpec.body status (MainMethod.head (ram 0x80fff9f4#32)) payload).length) :
    ∃ d n after, n≤2450+UartWriteAll.time (ResponseHeadSpec.bytes status (WireSpec.ascii "application/json") payload.length close) hs+
        UartWriteAll.time (ResponseHeadSpec.body status (MainMethod.head (ram 0x80fff9f4#32)) payload) bs ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
        (UartTxLoop.events (ResponseHeadSpec.bytes status (WireSpec.ascii "application/json") payload.length close)++
          UartTxLoop.events (ResponseHeadSpec.body status (MainMethod.head (ram 0x80fff9f4#32)) payload)) ∧
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
  obtain ⟨a,na,mid,ba,ta,pa,a2,a8,a22,a12,a11,a20,a10,a13,a9,a24,ac,live,a19,a18,a23,a26⟩ := extract kind c ram _ _ _ _ hp h2 h8 h18 h22 stack hv small
  have region (off size : Nat) (bound : off+size≤3780) : ViewFrame.Region ram mid (sp+BitVec.ofNat 32 off) size := by
    intro i
    have byte := live ⟨off+i.val,by have := i.isLt;omega⟩
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using byte
  have word (off : Nat) (bound : off+4≤532) : ramRead mid (fp+BitVec.ofNat 32 off) .w=ramRead ram (fp+BitVec.ofNat 32 off) .w := by
    have frame : ViewFrame.Region ram mid fp 532 := by simpa only [show sp+3204#32=fp by decide +kernel] using region 3204 532 (by decide)
    exact ViewFrame.word frame off bound
  have app := AppState.preserve ram mid state happ (by
    simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using region 44 25 (by decide))
  have body : Bytes.Span B mid 0x80fff4d4#32 payload := ViewFrame.span hb (by
    simpa only [show sp+2372#32=0x80fff4d4#32 by decide +kernel] using region 2372 payload.length (by omega))
  have cap : ramRead mid 0x80fff9fc#32 .w=832#32 := by
    have atWord := word 488 (by decide)
    simpa only [show fp+BitVec.ofNat 32 (488 : Nat)=0x80fff9fc#32 by decide +kernel] using atWord.trans hcap
  have flag : mid 0x80fff878#32=Encoding.boolByte close := by
    have byte := region 3304 1 (by decide) ⟨0,by decide⟩
    simpa only [BitVec.add_zero,show sp+3304#32=0x80fff878#32 by decide +kernel] using byte.trans hclose
  have method : mid 0x80fff9f4#32=ram 0x80fff9f4#32 := by
    have byte := region 3684 1 (by decide) ⟨0,by decide⟩
    simpa only [BitVec.add_zero,show sp+3684#32=0x80fff9f4#32 by decide +kernel] using byte
  obtain ⟨d,nb,after,bb,tb,pd,d2,d8,dc,appAfter,inv,_,d21,rx,low,capFrame,routes,d19,d22,d18,d23,d26⟩ := LoopResponseReply.contract_exact true a mid state io payload status close
    pa a2 a8 a22 hm app hi hbody hlo hst a12 a11 a20 a10 a13 a9 a24 body cap
    ((word 64 (by decide)).trans htx) ((word 68 (by decide)).trans htxc) ((word 72 (by decide)).trans hio) flag hs bs hhs (by rw [method];exact hbs)
  rw [method] at bb tb
  simp only [MainResponseExtractedReply.mime,ite_true] at bb tb
  refine ⟨d,na+nb,after,by omega,?_,pd,d2,d8,dc.trans ac,appAfter,inv,?_,?_,?_,?_,?_,?_,?_,?_,?_,d21⟩
  · simpa only [List.nil_append,MainResponseExtractedReply.mime,ite_true] using ta.observed.trans tb
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
end E5R.Thermostat.LoopWriteReturn
