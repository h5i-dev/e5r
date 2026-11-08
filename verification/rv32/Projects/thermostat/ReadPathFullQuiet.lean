-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ReadPathFull
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.ReadEngineIOQuiet
import Projects.thermostat.ReadReplyTailQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.ReadPathFull
theorem contract_inv_quiet (c : Core) (ram : Word → BitVec 8) (dst : Word) (cap : Nat) (s : Spec.Snapshot)
    (h : ReadAcquire.Pre UartPlatform.board c ram s) (hi : Spec.Inv s)
    (hstack : Memory.Block UartPlatform.board 0x80ff0000#32 65536)
    (h24 : c.get 24=dst) (h20 : c.get 20=BitVec.ofNat 32 cap) (h22 : c.get 22=1#32)
    (hc : cap<2^32) (hlen : 103≤cap) (hd : Memory.Block UartPlatform.board dst cap) (hw : dst.toNat+cap<2^32)
    (hds : WordRegions.Disjoint dst cap 0x80ffea50#32 320)
    (hss : WordRegions.Disjoint 0x80fffd38#32 10 dst cap)
    (hdf : WordRegions.Disjoint dst cap 0x80fff814#32 753)
    (hkd : WordRegions.Disjoint 0x80ffebcc#32 9 dst cap)
    (hed : WordRegions.Disjoint 0x80ffebbc#32 14 dst cap) :
    ∃ d n r, n≤4112 ∧ Quiet.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      ReadReplyTail.Post c d r dst s ∧ Encoding.SnapshotAt r 0x80ffebc0#32 s ∧
      ramRead r 0x80ffebbc#32 .w=0#32 ∧ Engine.InvariantAt r 0x80ffebbc#32 ∧ ViewFrame.Region ram r 0x80fff814#32 708 ∧ ViewFrame.Region ram r 0x80ffebcc#32 9 := by
  obtain ⟨na,a,ra,hna,ta,hpa,hbuf⟩ := E5R.Thermostat.ReadEngine.contract_io_quiet UartPlatform.board c ram s h
  have block (a : Word) (off n : Nat) (hpos : 0<n) (hptr : 0x80ff0000#32+BitVec.ofNat 32 off=a) (hfit : off+n≤65536) :
      Memory.Block UartPlatform.board a n := by
    rw [←hptr];exact Memory.sub_block hstack hpos hfit
  obtain ⟨d,nb,r,hnb,tb,hp,fr,hmeta⟩ := E5R.Thermostat.ReadReplyTail.contract_quiet a ra dst cap s hpa.pc hpa.sp (hpa.fp.trans h.fp)
    ((hbuf 24 (by decide)).trans h24) ((hbuf 20 (by decide)).trans h20) ((hbuf 22 (by decide)).trans h22)
    (block _ 59984 320 (by decide) (by decide +kernel) (by decide))
    (block _ 64824 10 (by decide) (by decide +kernel) (by decide)) hpa.reply
    (block _ 63508 753 (by decide) (by decide +kernel) (by decide)) hc hd hw hds hss hdf
    (Nat.le_trans (JsonCapacity.snapshot_length s) hlen)
  have region : ViewFrame.Region ra r 0x80ffebbc#32 14 := by
    intro i
    exact fr _
      (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)
      (hed i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)
  have hs : Encoding.SnapshotAt r 0x80ffebc0#32 s := by
    intro i
    have hh := region ⟨4+i.val,by have := i.isLt;omega⟩
    have he : 0x80ffebbc#32+BitVec.ofNat 32 (4+i.val)=0x80ffebc0#32+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
    rw [he] at hh
    exact hh.trans (hpa.state i)
  have hb : ramRead r 0x80ffebbc#32 .w=0#32 := by
    have hh := ViewFrame.word region 0 (by decide)
    simp only [BitVec.add_zero] at hh
    exact hh.trans hpa.released
  refine ⟨d,na+nb,r,by omega,ta.trans tb,?_,hs,hb,⟨s,hs,hi⟩,?_,?_⟩
  · exact {hp with csr := hp.csr.trans hpa.csr}
  · intro i
    rw [hmeta i]
    apply hpa.frame
    exact ⟨WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i,
      WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i,
      WordRegions.before _ _ _ _ (by decide) (by decide) i,
      WordRegions.before _ _ _ _ (by decide) (by decide) i,
      WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i⟩
  · intro i
    exact (fr _
      (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)
      (hkd i) (WordRegions.before _ _ _ _ (by decide) (by decide) i)).trans
      (hpa.frame _ ⟨WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i,
        WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i,
        WordRegions.before _ _ _ _ (by decide) (by decide) i,
        WordRegions.before _ _ _ _ (by decide) (by decide) i,
        WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i⟩)

end E5R.Thermostat.ReadPathFull
