import Projects.thermostat.ReadPath
import Projects.thermostat.SharedResponseLow
import Projects.thermostat.SharedResponsePayload
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ReadResponse
open E5R E5R.Thermostat

/-- Actual distinct Read transaction and response-object construction. The
    next boundary starts the original send Future; UART emission is later. -/
theorem contract_inv (c : Core) (ram : Word → BitVec 8) (dst : Word) (cap : Nat) (s : Spec.Snapshot)
    (h : ReadAcquire.Pre UartPlatform.board c ram s) (hi : Spec.Inv s)
    (hstack : Memory.Block UartPlatform.board 0x80ff0000#32 65536)
    (h24 : c.get 24=dst) (h20 : c.get 20=BitVec.ofNat 32 cap) (h22 : c.get 22=1#32)
    (hc : cap<2^32) (hlen : 103≤cap) (hd : Memory.Block UartPlatform.board dst cap) (hw : dst.toNat+cap<2^32)
    (hcap : ramRead ram 0x80fff9fc#32 .w=BitVec.ofNat 32 cap)
    (hds : WordRegions.Disjoint dst cap 0x80ffea50#32 320)
    (hss : WordRegions.Disjoint 0x80fffd38#32 10 dst cap)
    (hdf : WordRegions.Disjoint dst cap 0x80fff814#32 753)
    (hdt : WordRegions.Disjoint dst cap 0x80ffeb90#32 24)
    (hed : WordRegions.Disjoint 0x80ffebbc#32 14 dst cap) :
    ∃ d n r, n≤4138 ∧ DetSteps UartPlatform.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧ d.pc=0x80001772#32 ∧
      d.get 2=0x80ffeb90#32 ∧ d.get 8=0x80fff814#32 ∧ d.sameCsr c ∧
      SharedResponsePayload.At r 0x80fff814#32 0x800056a8#32 16#32 (BitVec.ofNat 32 (ReplyJson.snapshot s).length) 200#32
        (BitVec.ofNat 32 (ram 0x80fff878#32).toNat) ∧
      Bytes.Span UartPlatform.board r dst (ReplyJson.snapshot s) ∧
      Encoding.SnapshotAt r 0x80ffebc0#32 s ∧ ramRead r 0x80ffebbc#32 .w=0#32 ∧ Engine.InvariantAt r 0x80ffebbc#32 := by
  obtain ⟨a,na,ra,hna,ta,hp,hsnap,hborrow,_,hmeta⟩ := ReadPath.contract_inv c ram dst cap s h hi hstack h24 h20 h22 hc hlen hd hw hds hss hdf hed
  have hfit : (ReplyJson.snapshot s).length≤cap := Nat.le_trans (JsonCapacity.snapshot_length s) hlen
  have hcap' : ramRead ra (0x80fff814#32+488#32) .w=BitVec.ofNat 32 cap := by
    have hh := ViewFrame.word hmeta 488 (by decide)
    exact hh.trans hcap
  have hfit' : (BitVec.ofNat 32 (ReplyJson.snapshot s).length).toNat≤(BitVec.ofNat 32 cap).toNat := by
    rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hc,Nat.mod_eq_of_lt (by omega : (ReplyJson.snapshot s).length<2^32)]
    exact hfit
  have hspblock : Memory.Block UartPlatform.board 0x80ffeb90#32 24 := by
    have hb := Memory.sub_block hstack (off := 60304) (m := 24) (by decide) (by decide)
    rw [show 0x80ff0000#32+BitVec.ofNat 32 60304=0x80ffeb90#32 by decide +kernel] at hb
    exact hb
  have hfpblock : Memory.Block UartPlatform.board 0x80fff814#32 753 := by
    have hb := Memory.sub_block h.memory (off := 3284) (m := 753) (by decide) (by decide)
    rw [show (0x80ffeb40 : Word)+BitVec.ofNat 32 3284=0x80fff814#32 by decide +kernel] at hb
    exact hb
  obtain ⟨d,r,td,pd,dc,hstored,dr,fr⟩ := SharedResponse.contract UartPlatform.board a ra 0x80fff814#32 0x80ffeb90#32 (BitVec.ofNat 32 cap)
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
  have hbytes : Bytes.Span UartPlatform.board r dst (ReplyJson.snapshot s) := by
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
  refine ⟨d,na+26,r,by omega,ta.trans td,pd,?_,?_,dc.trans hp.csr,hpayload,hbytes,hs,hb,⟨s,hs,hi⟩⟩
  · exact (dr 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp.sp
  · exact (dr 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp.fp
end E5R.Thermostat.ReadResponse
