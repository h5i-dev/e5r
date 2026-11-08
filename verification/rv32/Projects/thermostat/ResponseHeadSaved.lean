import Projects.thermostat.CopyRegs
import Projects.thermostat.ResponseHeadSaveData
import Projects.thermostat.ResponseHeadPrefixMemory
import Projects.thermostat.ResponseHeadEnvelope
namespace E5R.Thermostat.ResponseHeadSaved
open E5R E5R.Thermostat

structure At (ram : Word → BitVec 8) (frame : Word) (c : Core) : Prop where
  x1 : ramRead ram (frame+92#32) .w=c.get 1
  x8 : ramRead ram (frame+88#32) .w=c.get 8
  x9 : ramRead ram (frame+84#32) .w=c.get 9
  x18 : ramRead ram (frame+80#32) .w=c.get 18
  x19 : ramRead ram (frame+76#32) .w=c.get 19
  x20 : ramRead ram (frame+72#32) .w=c.get 20
  x21 : ramRead ram (frame+68#32) .w=c.get 21
  x22 : ramRead ram (frame+64#32) .w=c.get 22
  x23 : ramRead ram (frame+60#32) .w=c.get 23
  x24 : ramRead ram (frame+56#32) .w=c.get 24
  x25 : ramRead ram (frame+52#32) .w=c.get 25
  x26 : ramRead ram (frame+48#32) .w=c.get 26
  x27 : ramRead ram (frame+44#32) .w=c.get 27

theorem save (ram : Word → BitVec 8) (frame : Word) (c : Core) : At (ResponseHeadSave.memory ram frame c) frame c := by
  obtain ⟨h1,h8,h9,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27⟩ := ResponseHeadSaveData.words ram frame c
  exact ⟨h1,h8,h9,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27⟩

theorem core {ram frame c d} (h : At ram frame c) (hc : ∀ r : Reg, CopyRegs.Preserved r → c.get r=d.get r) : At ram frame d :=
  ⟨h.x1.trans (hc 1 (by decide)),h.x8.trans (hc 8 (by decide)),h.x9.trans (hc 9 (by decide)),h.x18.trans (hc 18 (by decide)),h.x19.trans (hc 19 (by decide)),h.x20.trans (hc 20 (by decide)),h.x21.trans (hc 21 (by decide)),h.x22.trans (hc 22 (by decide)),h.x23.trans (hc 23 (by decide)),h.x24.trans (hc 24 (by decide)),h.x25.trans (hc 25 (by decide)),h.x26.trans (hc 26 (by decide)),h.x27.trans (hc 27 (by decide))⟩

theorem region {before after frame c} (h : At before frame c) (hf : ViewFrame.Region before after (frame+44#32) 52) : At after frame c := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hh := ViewFrame.word hf 48 (by decide)
    rw [BitVec.add_assoc,show 44#32+48#32=92#32 by decide +kernel] at hh
    exact hh.trans h.x1
  · have hh := ViewFrame.word hf 44 (by decide)
    rw [BitVec.add_assoc,show 44#32+44#32=88#32 by decide +kernel] at hh
    exact hh.trans h.x8
  · have hh := ViewFrame.word hf 40 (by decide)
    rw [BitVec.add_assoc,show 44#32+40#32=84#32 by decide +kernel] at hh
    exact hh.trans h.x9
  · have hh := ViewFrame.word hf 36 (by decide)
    rw [BitVec.add_assoc,show 44#32+36#32=80#32 by decide +kernel] at hh
    exact hh.trans h.x18
  · have hh := ViewFrame.word hf 32 (by decide)
    rw [BitVec.add_assoc,show 44#32+32#32=76#32 by decide +kernel] at hh
    exact hh.trans h.x19
  · have hh := ViewFrame.word hf 28 (by decide)
    rw [BitVec.add_assoc,show 44#32+28#32=72#32 by decide +kernel] at hh
    exact hh.trans h.x20
  · have hh := ViewFrame.word hf 24 (by decide)
    rw [BitVec.add_assoc,show 44#32+24#32=68#32 by decide +kernel] at hh
    exact hh.trans h.x21
  · have hh := ViewFrame.word hf 20 (by decide)
    rw [BitVec.add_assoc,show 44#32+20#32=64#32 by decide +kernel] at hh
    exact hh.trans h.x22
  · have hh := ViewFrame.word hf 16 (by decide)
    rw [BitVec.add_assoc,show 44#32+16#32=60#32 by decide +kernel] at hh
    exact hh.trans h.x23
  · have hh := ViewFrame.word hf 12 (by decide)
    rw [BitVec.add_assoc,show 44#32+12#32=56#32 by decide +kernel] at hh
    exact hh.trans h.x24
  · have hh := ViewFrame.word hf 8 (by decide)
    rw [BitVec.add_assoc,show 44#32+8#32=52#32 by decide +kernel] at hh
    exact hh.trans h.x25
  · have hh := ViewFrame.word hf 4 (by decide)
    rw [BitVec.add_assoc,show 44#32+4#32=48#32 by decide +kernel] at hh
    exact hh.trans h.x26
  · have hh := ViewFrame.word hf 0 (by decide)
    rw [BitVec.add_assoc,show 44#32+0#32=44#32 by decide +kernel] at hh
    exact hh.trans h.x27

theorem after_prefix {ram frame dst ctptr body flag status ctlen c} (h : At ram frame c) (hs : WordRegions.Disjoint frame 96 dst 192) :
    At (ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen) frame c :=
  region h (ResponseHeadPrefixMemory.saved _ _ _ _ _ _ _ _ hs)

theorem envelope {before after frame dst c} (h : At before frame c) (he : ResponseHeadEnvelope.Frame before after frame dst) (hs : WordRegions.Disjoint frame 96 dst 192) : At after frame c :=
  ⟨(ResponseHeadEnvelope.word he hs 92 (by decide) (by decide)).trans h.x1,(ResponseHeadEnvelope.word he hs 88 (by decide) (by decide)).trans h.x8,(ResponseHeadEnvelope.word he hs 84 (by decide) (by decide)).trans h.x9,(ResponseHeadEnvelope.word he hs 80 (by decide) (by decide)).trans h.x18,(ResponseHeadEnvelope.word he hs 76 (by decide) (by decide)).trans h.x19,(ResponseHeadEnvelope.word he hs 72 (by decide) (by decide)).trans h.x20,(ResponseHeadEnvelope.word he hs 68 (by decide) (by decide)).trans h.x21,(ResponseHeadEnvelope.word he hs 64 (by decide) (by decide)).trans h.x22,(ResponseHeadEnvelope.word he hs 60 (by decide) (by decide)).trans h.x23,(ResponseHeadEnvelope.word he hs 56 (by decide) (by decide)).trans h.x24,(ResponseHeadEnvelope.word he hs 52 (by decide) (by decide)).trans h.x25,(ResponseHeadEnvelope.word he hs 48 (by decide) (by decide)).trans h.x26,(ResponseHeadEnvelope.word he hs 44 (by decide) (by decide)).trans h.x27⟩
end E5R.Thermostat.ResponseHeadSaved
