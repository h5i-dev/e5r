import Projects.thermostat.ResponseHeadPrefix
import Projects.thermostat.StoreWords
import Projects.thermostat.ReadFrame
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ResponseHeadPrefixMemory
open E5R E5R.Thermostat

theorem body_word (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat)
    (hsep : WordRegions.Disjoint frame 96 dst 192) :
    ramRead (ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen) (frame+28#32) .w=body := by
  unfold ResponseHeadPrefix.memory ResponseHeadPrefixPart2.memory ResponseHeadPrefixPart1.memory ResponseHeadPrefixPart0.memory
  rw [StoreWords.read_other _ (frame+28#32) (frame+36#32) ((BitVec.ofNat 32 status)) .w (by
    exact StoreWords.offsets frame 28 4 36 4 (by decide) (by decide) (by decide))]
  rw [StoreWords.read_other _ (frame+28#32) (frame+40#32) (192#32) .w (by
    exact StoreWords.offsets frame 28 4 40 4 (by decide) (by decide) (by decide))]
  rw [StoreWords.read_other _ (frame+28#32) (dst+12#32) (32#32) .b (by
    intro i j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    have hn := hsep ⟨28+i.val,by have := i.isLt;omega⟩ ⟨12,by decide⟩
    rw [hj,BitVec.add_zero,BitVec.add_assoc,←BitVec.ofNat_add]
    exact hn)]
  rw [StoreWords.read_other _ (frame+28#32) (frame+32#32) (flag) .w (by
    exact StoreWords.offsets frame 28 4 32 4 (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _
theorem close_word (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat)
    (hsep : WordRegions.Disjoint frame 96 dst 192) :
    ramRead (ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen) (frame+32#32) .w=flag := by
  unfold ResponseHeadPrefix.memory ResponseHeadPrefixPart2.memory ResponseHeadPrefixPart1.memory ResponseHeadPrefixPart0.memory
  rw [StoreWords.read_other _ (frame+32#32) (frame+36#32) ((BitVec.ofNat 32 status)) .w (by
    exact StoreWords.offsets frame 32 4 36 4 (by decide) (by decide) (by decide))]
  rw [StoreWords.read_other _ (frame+32#32) (frame+40#32) (192#32) .w (by
    exact StoreWords.offsets frame 32 4 40 4 (by decide) (by decide) (by decide))]
  rw [StoreWords.read_other _ (frame+32#32) (dst+12#32) (32#32) .b (by
    intro i j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    have hn := hsep ⟨32+i.val,by have := i.isLt;omega⟩ ⟨12,by decide⟩
    rw [hj,BitVec.add_zero,BitVec.add_assoc,←BitVec.ofNat_add]
    exact hn)]
  exact ramRead_ramWrite_w _ _ _
theorem status_word (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat)
    (hsep : WordRegions.Disjoint frame 96 dst 192) :
    ramRead (ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen) (frame+36#32) .w=BitVec.ofNat 32 status := by
  unfold ResponseHeadPrefix.memory ResponseHeadPrefixPart2.memory ResponseHeadPrefixPart1.memory ResponseHeadPrefixPart0.memory
  exact ramRead_ramWrite_w _ _ _
theorem cap_word (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat)
    (hsep : WordRegions.Disjoint frame 96 dst 192) :
    ramRead (ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen) (frame+40#32) .w=192#32 := by
  unfold ResponseHeadPrefix.memory ResponseHeadPrefixPart2.memory ResponseHeadPrefixPart1.memory ResponseHeadPrefixPart0.memory
  rw [StoreWords.read_other _ (frame+40#32) (frame+36#32) ((BitVec.ofNat 32 status)) .w (by
    exact StoreWords.offsets frame 40 4 36 4 (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _
theorem frame (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat) (x : Word)
    (hs : ∀ i : Fin 96, x≠frame+BitVec.ofNat 32 i.val)
    (hd : ∀ i : Fin 13, x≠dst+BitVec.ofNat 32 i.val) :
    ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen x=ram x := by
  unfold ResponseHeadPrefix.memory ResponseHeadPrefixPart2.memory ResponseHeadPrefixPart1.memory ResponseHeadPrefixPart0.memory
  rw [StoreBytes.frame _ (frame+36#32) ((BitVec.ofNat 32 status)) x .w (by
    intro j
    have hj : j.val<4 := j.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hs ⟨36+j.val,by omega⟩)]
  rw [StoreBytes.frame _ (frame+40#32) (192#32) x .w (by
    intro j
    have hj : j.val<4 := j.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hs ⟨40+j.val,by omega⟩)]
  rw [StoreBytes.frame _ (dst+12#32) (32#32) x .b (by
    intro j
    have hj : j.val<1 := j.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hd ⟨12+j.val,by omega⟩)]
  rw [StoreBytes.frame _ (frame+32#32) (flag) x .w (by
    intro j
    have hj : j.val<4 := j.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hs ⟨32+j.val,by omega⟩)]
  rw [StoreBytes.frame _ (frame+28#32) (body) x .w (by
    intro j
    have hj : j.val<4 := j.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hs ⟨28+j.val,by omega⟩)]
  rw [StoreBytes.frame _ (dst+11#32) ((BitVec.ofNat 32 (48+status%10))) x .b (by
    intro j
    have hj : j.val<1 := j.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hd ⟨11+j.val,by omega⟩)]
  rw [StoreBytes.frame _ (dst+10#32) ((BitVec.ofNat 32 (48+(status/10)%10))) x .b (by
    intro j
    have hj : j.val<1 := j.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hd ⟨10+j.val,by omega⟩)]
  rw [StoreBytes.frame _ (dst+9#32) ((BitVec.ofNat 32 (48+status/100))) x .b (by
    intro j
    have hj : j.val<1 := j.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hd ⟨9+j.val,by omega⟩)]
  rw [StoreBytes.frame _ (dst+8#32) (32#32) x .b (by
    intro j
    have hj : j.val<1 := j.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hd ⟨8+j.val,by omega⟩)]
  rw [StoreBytes.frame _ (dst+7#32) (49#32) x .b (by
    intro j
    have hj : j.val<1 := j.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hd ⟨7+j.val,by omega⟩)]
  rw [StoreBytes.frame _ (dst+6#32) (46#32) x .b (by
    intro j
    have hj : j.val<1 := j.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hd ⟨6+j.val,by omega⟩)]
  rw [StoreBytes.frame _ (dst+5#32) (49#32) x .b (by
    intro j
    have hj : j.val<1 := j.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hd ⟨5+j.val,by omega⟩)]
  rw [StoreBytes.frame _ (dst+4#32) (47#32) x .b (by
    intro j
    have hj : j.val<1 := j.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hd ⟨4+j.val,by omega⟩)]
  rw [StoreBytes.frame _ (dst+3#32) (80#32) x .b (by
    intro j
    have hj : j.val<1 := j.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hd ⟨3+j.val,by omega⟩)]
  rw [StoreBytes.frame _ (dst+2#32) (84#32) x .b (by
    intro j
    have hj : j.val<1 := j.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hd ⟨2+j.val,by omega⟩)]
  rw [StoreBytes.frame _ (dst+1#32) (84#32) x .b (by
    intro j
    have hj : j.val<1 := j.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hd ⟨1+j.val,by omega⟩)]
  rw [StoreBytes.frame _ (dst+0#32) (72#32) x .b (by
    intro j
    have hj : j.val<1 := j.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hd ⟨0+j.val,by omega⟩)]
theorem saved (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat)
    (hsep : WordRegions.Disjoint frame 96 dst 192) :
    ViewFrame.Region ram (ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen) (frame+44#32) 52 := by
  intro i
  unfold ResponseHeadPrefix.memory ResponseHeadPrefixPart2.memory ResponseHeadPrefixPart1.memory ResponseHeadPrefixPart0.memory
  rw [StoreBytes.frame _ (frame+36#32) ((BitVec.ofNat 32 status)) ((frame+44#32)+BitVec.ofNat 32 i.val) .w (by
    exact StoreWords.offsets frame 44 52 36 4 (by decide) (by decide) (by decide) i)]
  rw [StoreBytes.frame _ (frame+40#32) (192#32) ((frame+44#32)+BitVec.ofNat 32 i.val) .w (by
    exact StoreWords.offsets frame 44 52 40 4 (by decide) (by decide) (by decide) i)]
  rw [StoreBytes.frame _ (dst+12#32) (32#32) ((frame+44#32)+BitVec.ofNat 32 i.val) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    have hn := hsep ⟨44+i.val,by have := i.isLt;omega⟩ ⟨12,by decide⟩
    rw [hj,BitVec.add_zero,BitVec.add_assoc,←BitVec.ofNat_add]
    exact hn)]
  rw [StoreBytes.frame _ (frame+32#32) (flag) ((frame+44#32)+BitVec.ofNat 32 i.val) .w (by
    exact StoreWords.offsets frame 44 52 32 4 (by decide) (by decide) (by decide) i)]
  rw [StoreBytes.frame _ (frame+28#32) (body) ((frame+44#32)+BitVec.ofNat 32 i.val) .w (by
    exact StoreWords.offsets frame 44 52 28 4 (by decide) (by decide) (by decide) i)]
  rw [StoreBytes.frame _ (dst+11#32) ((BitVec.ofNat 32 (48+status%10))) ((frame+44#32)+BitVec.ofNat 32 i.val) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    have hn := hsep ⟨44+i.val,by have := i.isLt;omega⟩ ⟨11,by decide⟩
    rw [hj,BitVec.add_zero,BitVec.add_assoc,←BitVec.ofNat_add]
    exact hn)]
  rw [StoreBytes.frame _ (dst+10#32) ((BitVec.ofNat 32 (48+(status/10)%10))) ((frame+44#32)+BitVec.ofNat 32 i.val) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    have hn := hsep ⟨44+i.val,by have := i.isLt;omega⟩ ⟨10,by decide⟩
    rw [hj,BitVec.add_zero,BitVec.add_assoc,←BitVec.ofNat_add]
    exact hn)]
  rw [StoreBytes.frame _ (dst+9#32) ((BitVec.ofNat 32 (48+status/100))) ((frame+44#32)+BitVec.ofNat 32 i.val) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    have hn := hsep ⟨44+i.val,by have := i.isLt;omega⟩ ⟨9,by decide⟩
    rw [hj,BitVec.add_zero,BitVec.add_assoc,←BitVec.ofNat_add]
    exact hn)]
  rw [StoreBytes.frame _ (dst+8#32) (32#32) ((frame+44#32)+BitVec.ofNat 32 i.val) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    have hn := hsep ⟨44+i.val,by have := i.isLt;omega⟩ ⟨8,by decide⟩
    rw [hj,BitVec.add_zero,BitVec.add_assoc,←BitVec.ofNat_add]
    exact hn)]
  rw [StoreBytes.frame _ (dst+7#32) (49#32) ((frame+44#32)+BitVec.ofNat 32 i.val) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    have hn := hsep ⟨44+i.val,by have := i.isLt;omega⟩ ⟨7,by decide⟩
    rw [hj,BitVec.add_zero,BitVec.add_assoc,←BitVec.ofNat_add]
    exact hn)]
  rw [StoreBytes.frame _ (dst+6#32) (46#32) ((frame+44#32)+BitVec.ofNat 32 i.val) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    have hn := hsep ⟨44+i.val,by have := i.isLt;omega⟩ ⟨6,by decide⟩
    rw [hj,BitVec.add_zero,BitVec.add_assoc,←BitVec.ofNat_add]
    exact hn)]
  rw [StoreBytes.frame _ (dst+5#32) (49#32) ((frame+44#32)+BitVec.ofNat 32 i.val) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    have hn := hsep ⟨44+i.val,by have := i.isLt;omega⟩ ⟨5,by decide⟩
    rw [hj,BitVec.add_zero,BitVec.add_assoc,←BitVec.ofNat_add]
    exact hn)]
  rw [StoreBytes.frame _ (dst+4#32) (47#32) ((frame+44#32)+BitVec.ofNat 32 i.val) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    have hn := hsep ⟨44+i.val,by have := i.isLt;omega⟩ ⟨4,by decide⟩
    rw [hj,BitVec.add_zero,BitVec.add_assoc,←BitVec.ofNat_add]
    exact hn)]
  rw [StoreBytes.frame _ (dst+3#32) (80#32) ((frame+44#32)+BitVec.ofNat 32 i.val) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    have hn := hsep ⟨44+i.val,by have := i.isLt;omega⟩ ⟨3,by decide⟩
    rw [hj,BitVec.add_zero,BitVec.add_assoc,←BitVec.ofNat_add]
    exact hn)]
  rw [StoreBytes.frame _ (dst+2#32) (84#32) ((frame+44#32)+BitVec.ofNat 32 i.val) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    have hn := hsep ⟨44+i.val,by have := i.isLt;omega⟩ ⟨2,by decide⟩
    rw [hj,BitVec.add_zero,BitVec.add_assoc,←BitVec.ofNat_add]
    exact hn)]
  rw [StoreBytes.frame _ (dst+1#32) (84#32) ((frame+44#32)+BitVec.ofNat 32 i.val) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    have hn := hsep ⟨44+i.val,by have := i.isLt;omega⟩ ⟨1,by decide⟩
    rw [hj,BitVec.add_zero,BitVec.add_assoc,←BitVec.ofNat_add]
    exact hn)]
  rw [StoreBytes.frame _ (dst+0#32) (72#32) ((frame+44#32)+BitVec.ofNat 32 i.val) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    have hn := hsep ⟨44+i.val,by have := i.isLt;omega⟩ ⟨0,by decide⟩
    rw [hj,BitVec.add_zero,BitVec.add_assoc,←BitVec.ofNat_add]
    exact hn)]
end E5R.Thermostat.ResponseHeadPrefixMemory
