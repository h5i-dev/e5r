import Projects.thermostat.LoopReadResponse
import Projects.thermostat.StackLoopReadPath
set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.StackLoopReadResponse
open E5R E5R.Thermostat LoopReadResponse
abbrev B := StackBoard.board
theorem contract_inv_quiet (c : Core) (ram : Word → BitVec 8) (dst : Word) (cap : Nat) (s : Spec.Snapshot)
    (tx io : Word) (close : Bool)
    (htx : ramRead ram (0x80fff814#32+64#32) .w=tx)
    (htxcap : ramRead ram (0x80fff814#32+68#32) .w=1024#32)
    (hio : ramRead ram (0x80fff814#32+72#32) .w=io)
    (hcloseByte : ram 0x80fff878#32=(if close then 1#8 else 0#8))
    (h : ReadAcquire.Pre StackBoard.board c ram s) (hi : Spec.Inv s)
    (hstack : Memory.Block StackBoard.board 0x80ff0000#32 65536)
    (h24 : c.get 24=dst) (h20 : c.get 20=BitVec.ofNat 32 cap) (h22 : c.get 22=1#32)
    (hc : cap<2^32) (hlen : 103≤cap) (hd : Memory.Block StackBoard.board dst cap) (hw : dst.toNat+cap<2^32)
    (hcap : ramRead ram 0x80fff9fc#32 .w=BitVec.ofNat 32 cap)
    (hds : WordRegions.Disjoint dst cap 0x80ffea50#32 320)
    (hss : WordRegions.Disjoint 0x80fffd38#32 10 dst cap)
    (hdf : WordRegions.Disjoint dst cap 0x80fff814#32 753)
    (hdt : WordRegions.Disjoint dst cap 0x80ffeb90#32 24)
    (hkd : WordRegions.Disjoint 0x80ffebcc#32 9 dst cap)
    (hed : WordRegions.Disjoint 0x80ffebbc#32 14 dst cap)
    (hcd : WordRegions.Disjoint 0x80ffeba0#32 4 dst cap)
    (hrd : WordRegions.Disjoint 0x80ffebd8#32 60 dst cap) :
    ∃ d n r, n≤4138 ∧ Quiet.Steps StackBoard.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧ d.pc=0x80001772#32 ∧
      d.get 2=0x80ffeb90#32 ∧ d.get 8=0x80fff814#32 ∧ d.sameCsr c ∧
      SharedResponsePayload.At r 0x80fff814#32 0x800056a8#32 16#32 (BitVec.ofNat 32 (ReplyJson.snapshot s).length) 200#32
        (BitVec.ofNat 32 (ram 0x80fff878#32).toNat) ∧
      Bytes.Span StackBoard.board r dst (ReplyJson.snapshot s) ∧
      Encoding.SnapshotAt r 0x80ffebc0#32 s ∧ ramRead r 0x80ffebbc#32 .w=0#32 ∧ Engine.InvariantAt r 0x80ffebbc#32 ∧ d.get 9=0x80fff878#32 ∧
      SharedResponseView.Descriptor r 0x80fff878#32 tx io 0x800056a8#32 (ReplyJson.snapshot s).length 200
        (WireSpec.ascii "application/json") close (MainMethod.head (ram 0x80fff9f4#32)) ∧ ViewFrame.Region ram r 0x80ffebcc#32 9 ∧ d.get 24=0xfffffffe#32 ∧
      ViewFrame.Region ram r 0x80fff814#32 96 ∧ ViewFrame.Region ram r 0x80ffeba0#32 4 ∧
      ViewFrame.Region ram r 0x80ffebd8#32 60 ∧ d.get 19=c.get 19 ∧ d.get 22=1#32 ∧ d.get 18=2#32 ∧ d.get 23=c.get 23 ∧ d.get 26=c.get 26 := by
  obtain ⟨a,na,ra,hna,ta,hp,hsnap,hborrow,_,hmeta,hkeys,capA,routesA,a19,a23,a26⟩ := StackLoopReadPath.contract_inv_quiet c ram dst cap s h hi hstack h24 h20 h22 hc hlen hd hw hds hss hdf hkd hed hcd hrd
  have hfit : (ReplyJson.snapshot s).length≤cap := Nat.le_trans (JsonCapacity.snapshot_length s) hlen
  have hcap' : ramRead ra (0x80fff814#32+488#32) .w=BitVec.ofNat 32 cap := by
    have hh := ViewFrame.word hmeta 488 (by decide)
    exact hh.trans hcap
  have hfit' : (BitVec.ofNat 32 (ReplyJson.snapshot s).length).toNat≤(BitVec.ofNat 32 cap).toNat := by
    rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hc,Nat.mod_eq_of_lt (by omega : (ReplyJson.snapshot s).length<2^32)]
    exact hfit
  have hspblock : Memory.Block StackBoard.board 0x80ffeb90#32 24 := by
    have hb := Memory.sub_block hstack (off := 60304) (m := 24) (by decide) (by decide)
    rw [show 0x80ff0000#32+BitVec.ofNat 32 60304=0x80ffeb90#32 by decide +kernel] at hb
    exact hb
  have hfpblock : Memory.Block StackBoard.board 0x80fff814#32 753 := by
    have hb := Memory.sub_block h.memory (off := 3284) (m := 753) (by decide) (by decide)
    rw [show (0x80ffeb40 : Word)+BitVec.ofNat 32 3284=0x80fff814#32 by decide +kernel] at hb
    exact hb
  obtain ⟨d,r,td,pd,dc,hstored,dr,fr,protect⟩ := LoopSharedRead.contract StackBoard.board a ra (BitVec.ofNat 32 cap)
    (BitVec.ofNat 32 (ReplyJson.snapshot s).length) 200#32 16#32 0x800056a8#32 0#32 hp.pc hp.fp hp.sp hp.completion hp.used hp.status hp.mimeLength hp.mime hp.extra
    hfpblock (by decide)
    hspblock (by decide) hcap' hfit'
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
  have payload := SharedResponsePayload.of_stored hstored
  have hclose : 0#32 ||| SharedResponse.byteWord (SharedResponseFlags.memory ra 0x80fff814#32) 0x80fff814#32 100 =
      BitVec.ofNat 32 (ram 0x80fff878#32).toNat := by
    rw [BitVec.zero_or]
    unfold SharedResponse.byteWord
    rw [Memory.load_byte]
    have hh := (SharedResponseFlags.low ra 0x80fff814#32 ⟨100,by decide⟩).trans (hmeta ⟨100,by decide⟩)
    exact congrArg (fun b : BitVec 8 => BitVec.ofNat 32 b.toNat) hh
  have hpayload : SharedResponsePayload.At r 0x80fff814#32 0x800056a8#32 16#32 (BitVec.ofNat 32 (ReplyJson.snapshot s).length) 200#32
      (BitVec.ofNat 32 (ram 0x80fff878#32).toNat) := by
    rw [hclose] at payload
    exact payload
  have hbytes : Bytes.Span StackBoard.board r dst (ReplyJson.snapshot s) := by
    apply ViewFrame.span hp.bytes
    intro i
    have hi := Nat.lt_of_lt_of_le i.isLt hfit
    exact fr _ (hdf ⟨i.val,hi⟩) (hdt ⟨i.val,hi⟩)
  have region : ViewFrame.Region ra r 0x80ffebbc#32 14 := by
    intro i
    exact fr _ (WordRegions.before _ _ _ _ (by decide) (by decide) i)
      (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)
  have hs : Encoding.SnapshotAt r 0x80ffebc0#32 s := by
    intro i
    have hh := region ⟨4+i.val,by have := i.isLt;omega⟩
    have he : 0x80ffebbc#32+BitVec.ofNat 32 (4+i.val)=0x80ffebc0#32+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [he] at hh
    exact hh.trans (hsnap i)
  have hb : ramRead r 0x80ffebbc#32 .w=0#32 := by
    have hh := ViewFrame.word region 0 (by decide)
    simp only [BitVec.add_zero] at hh
    exact hh.trans hborrow
  have ioword (off : Nat) (ho : off+4≤532) :
      SharedResponse.ioWord (SharedResponseFlags.memory ra 0x80fff814#32) 0x80fff814#32 off=
        ramRead ram (0x80fff814#32+BitVec.ofNat 32 off) .w := by
    unfold SharedResponse.ioWord
    change ramRead (SharedResponseFlags.memory ra 0x80fff814#32) _ .w=_
    exact (ViewFrame.word (SharedResponseFlags.low ra 0x80fff814#32) off ho).trans (ViewFrame.word hmeta off (by omega))
  have hio0 := (ioword 64 (by decide)).trans htx
  have hio1 := (ioword 68 (by decide)).trans htxcap
  have hio2 := (ioword 72 (by decide)).trans hio
  have closeVal : BitVec.ofNat 32 (ram 0x80fff878#32).toNat=ResponseHeadBodyMath.boolWord close := by
    rw [hcloseByte]
    cases close <;> rfl
  have methodVal : SharedResponse.byteWord (SharedResponseFlags.memory ra 0x80fff814#32) 0x80fff814#32 480=
      BitVec.ofNat 32 (ram 0x80fff9f4#32).toNat := by
    unfold SharedResponse.byteWord
    rw [Memory.load_byte]
    have hh := (SharedResponseFlags.low ra 0x80fff814#32 ⟨480,by decide⟩).trans (hmeta ⟨480,by decide⟩)
    exact congrArg (fun b : BitVec 8 => BitVec.ofNat 32 b.toNat) hh
  have actualStored := hstored
  rw [hio0,hio1,hio2,hclose,closeVal,methodVal] at actualStored
  have descriptor := SharedResponseView.descriptor (ReplyJson.snapshot s).length 200 (WireSpec.ascii "application/json") close
    (MainMethod.head (ram 0x80fff9f4#32)) (by decide) (MainMethod.head_value _) actualStored
  refine ⟨d,na+26,r,by omega,ta.trans td,pd,?_,?_,dc.trans hp.csr,hpayload,hbytes,hs,hb,⟨s,hs,hi⟩,?_,descriptor,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (dr 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp.sp
  · exact (dr 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp.fp
  · exact (dr 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp.future
  · intro i
    exact (fr _ (WordRegions.before _ _ _ _ (by decide) (by decide) i)
      (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)).trans (hkeys i)
  · exact (dr 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp.pending

  · have region := protect 3204 96 (by decide) (Or.inr (by decide))
    intro i
    have same : r (0x80fff814#32+BitVec.ofNat 32 i.val)=ra (0x80fff814#32+BitVec.ofNat 32 i.val) := by
      simpa only [show 0x80ffeb90#32+BitVec.ofNat 32 3204=0x80fff814#32 by decide +kernel] using region i
    exact same.trans (hmeta ⟨i.val,by have := i.isLt;omega⟩)
  · have region := protect 16 4 (by decide) (Or.inl (by decide))
    intro i
    have same : r (0x80ffeba0#32+BitVec.ofNat 32 i.val)=ra (0x80ffeba0#32+BitVec.ofNat 32 i.val) := by
      simpa only [show 0x80ffeb90#32+BitVec.ofNat 32 16=0x80ffeba0#32 by decide +kernel] using region i
    exact same.trans (capA i)
  · have region := protect 72 60 (by decide) (Or.inr (by decide))
    intro i
    have same : r (0x80ffebd8#32+BitVec.ofNat 32 i.val)=ra (0x80ffebd8#32+BitVec.ofNat 32 i.val) := by
      simpa only [show 0x80ffeb90#32+BitVec.ofNat 32 72=0x80ffebd8#32 by decide +kernel] using region i
    exact same.trans (routesA i)
  · exact (dr 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a19
  · exact (dr 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp.completion
  · exact (dr 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp.nextTag
  · exact (dr 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a23
  · exact (dr 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a26
end E5R.Thermostat.StackLoopReadResponse
