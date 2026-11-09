import Projects.thermostat.EncodeReplyMemory
import Projects.thermostat.StackEncodeReplyLayout
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.StackEncodeReplyMemory
open E5R E5R.Thermostat EncodeReplyMemory
theorem layout (ram : Word → BitVec 8) (p reply dst : Word) (cap : Nat) (c : Core) (s : Spec.Snapshot)
    (hm : Memory.Block StackBoard.board p 320) (ha : p.toNat%4=0)
    (hr : Memory.Block StackBoard.board reply 10) (har : reply.toNat%2=0)
    (hs : Encoding.SnapshotAt ram reply s) (hc : cap<2^32)
    (hd : Memory.Block StackBoard.board dst cap) (hw : dst.toNat+cap<2^32)
    (hrs : WordRegions.Disjoint reply 10 p 320) (hds : WordRegions.Disjoint dst cap p 320)
    (hrd : WordRegions.Disjoint reply 10 dst cap) :
    StackFormatLayout.Layout (memory ram p reply dst cap c s) p (p+232#32) (p+252#32) dst cap 0 (EncodeValues.values reply (p+244#32) s) := by
  let q := p+224#32
  let initial := EncodeReplyStart.memory ram q dst (BitVec.ofNat 32 cap) c
  let final := memory ram p reply dst cap c s
  have hstart := EncodeReplyStart.words ram q dst (BitVec.ofNat 32 cap) c
  have hctor := EncodeReplyConstruct.words initial q reply (ModeLiterals.pointer s.mode) (BitVec.ofNat 32 (ReplyJson.mode s.mode).length)
  have cur : ViewFrame.Region initial final (q+8#32) 12 := by
    intro i
    exact EncodeReplyConstruct.frame initial q reply (ModeLiterals.pointer s.mode) (BitVec.ofNat 32 (ReplyJson.mode s.mode).length) _
      (FormatSpace.offsets_disjoint q 8 12 20 72 (by decide) (by decide) (by decide) i)
  have hptr : ramRead final (q+8#32) .w = dst := by
    have hh := ViewFrame.word cur 0 (by decide)
    simp only [BitVec.add_zero] at hh
    exact hh.trans hstart.2.1
  have hcap : ramRead final ((q+8#32)+4#32) .w = BitVec.ofNat 32 cap := by
    have hh := ViewFrame.word cur 4 (by decide)
    rw [BitVec.add_assoc,show 8#32+BitVec.ofNat 32 4 = 12#32 by decide +kernel] at hh
    simpa only [BitVec.add_assoc,show (8#32+4#32)=12#32 by decide +kernel] using hh.trans hstart.2.2.1
  have hpos : ramRead final ((q+8#32)+8#32) .w = 0#32 := by
    have hh := ViewFrame.word cur 8 (by decide)
    rw [BitVec.add_assoc,show 8#32+BitVec.ofNat 32 8 = 16#32 by decide +kernel] at hh
    simpa only [BitVec.add_assoc,show (8#32+8#32)=16#32 by decide +kernel] using hh.trans hstart.2.2.2
  have ht := EncodeReplyTable.table StackBoard.board initial q reply (ModeLiterals.pointer s.mode)
    (BitVec.ofNat 32 (ReplyJson.mode s.mode).length) s
    (Memory.sub_block hm (off := 224) (m := 96) (by decide) (by decide)) (Memory.word_aligned p 56 ha)
  have he8 : q+8#32 = p+232#32 := by dsimp only [q];rw [BitVec.add_assoc];rfl
  have he20 : q+20#32 = p+244#32 := by dsimp only [q];rw [BitVec.add_assoc];rfl
  have he28 : q+28#32 = p+252#32 := by dsimp only [q];rw [BitVec.add_assoc];rfl
  have hmode : ramRead final (p+244#32) .w = ModeLiterals.pointer s.mode := by rw [←he20];exact hctor.1
  have hlen : ramRead final ((p+244#32)+4#32) .w = BitVec.ofNat 32 (ReplyJson.mode s.mode).length := by
    rw [←he20,BitVec.add_assoc,show (20#32+4#32)=24#32 by decide +kernel];exact hctor.2.1
  apply StackEncodeReplyLayout.build final p reply dst s cap hm ha hr har (snapshot hs hrs) hc hd hw hrs hds hrd
    (by rw [←he8];exact hptr) (by rw [←he8];exact hcap) (by rw [←he8];exact hpos)
    (by rw [←he20,←he28];exact ht) hmode hlen
end E5R.Thermostat.StackEncodeReplyMemory
