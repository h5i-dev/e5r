import Projects.thermostat.EncodeReplyLayout
import Projects.thermostat.StackFormatLayout
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.StackEncodeReplyLayout
open E5R E5R.Thermostat 
theorem build (ram : Word → BitVec 8) (p reply dst : Word) (s : Spec.Snapshot) (cap : Nat)
    (hm : Memory.Block StackBoard.board p 320) (ha : p.toNat%4=0)
    (hr : Memory.Block StackBoard.board reply 10) (har : reply.toNat%2=0)
    (hs : Encoding.SnapshotAt ram reply s) (hc : cap<2^32)
    (hd : Memory.Block StackBoard.board dst cap) (hw : dst.toNat+cap<2^32)
    (hrs : WordRegions.Disjoint reply 10 p 320) (hds : WordRegions.Disjoint dst cap p 320)
    (hrd : WordRegions.Disjoint reply 10 dst cap)
    (hptr : ramRead ram (p+232#32) .w = dst)
    (hcap : ramRead ram ((p+232#32)+4#32) .w = BitVec.ofNat 32 cap)
    (hpos : ramRead ram ((p+232#32)+8#32) .w = 0#32)
    (ht : FormatTable.At StackBoard.board ram (p+252#32) (EncodeValues.values reply (p+244#32) s))
    (hmode : ramRead ram (p+244#32) .w = ModeLiterals.pointer s.mode)
    (hlen : ramRead ram ((p+244#32)+4#32) .w = BitVec.ofNat 32 (ReplyJson.mode s.mode).length) :
    StackFormatLayout.Layout ram p (p+232#32) (p+252#32) dst cap 0 (EncodeValues.values reply (p+244#32) s) := by
  have objectArena := FormatSpace.offsets_disjoint p 232 12 0 224 (by decide) (by decide) (by decide)
  have tableArena := FormatSpace.offsets_disjoint p 252 64 0 224 (by decide) (by decide) (by decide)
  have tupleArena := FormatSpace.offsets_disjoint p 244 8 0 224 (by decide) (by decide) (by decide)
  simp only [BitVec.add_zero] at objectArena tableArena tupleArena
  refine ⟨⟨?_,ha,Memory.sub_block hm (off := 232) (m := 12) (by decide) (by decide),Memory.word_aligned p 58 ha,
      hc,by omega,hptr,hcap,hpos,hd,hw,objectArena,?_,?_
    ⟩,ht,tableArena,?_,FormatSpace.offsets_disjoint p 252 64 232 12 (by decide) (by decide) (by decide),?_,?_,?_,?_⟩
  · simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := 224) (by decide) (by decide)
  · simpa only [BitVec.add_zero] using Subregion.right hds 0 224 (by decide)
  · exact WordRegions.symm (Subregion.right hds 232 12 (by decide))
  · exact WordRegions.symm (Subregion.right hds 252 64 (by decide))
  · exact EncodeValues.sources hr har hs (Memory.sub_block hm (off := 244) (m := 8) (by decide) (by decide))
      (Memory.word_aligned p 61 ha) hmode hlen
  · apply EncodeValueRegions.regions _ tupleArena
    simpa only [BitVec.add_zero] using Subregion.right hrs 0 224 (by decide)
  · exact EncodeValueRegions.regions hrd (WordRegions.symm (Subregion.right hds 244 8 (by decide)))
  · exact EncodeValueRegions.regions (Subregion.right hrs 232 12 (by decide))
      (FormatSpace.offsets_disjoint p 244 8 232 12 (by decide) (by decide) (by decide))
end E5R.Thermostat.StackEncodeReplyLayout
