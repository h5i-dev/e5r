import Projects.thermostat.ResponseHeadPrefix
import Projects.thermostat.ResponseHeadPrefixSpec
import Projects.thermostat.StoreWords
import Projects.thermostat.WordRegions
import Projects.thermostat.HttpDecDigitsData
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ResponseHeadPrefixData
open E5R E5R.Thermostat

theorem cell0 (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat)
    (hsep : WordRegions.Disjoint frame 96 dst 192) :
    ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen (dst+0#32)=byteOf (72#32) 0 := by
  unfold ResponseHeadPrefix.memory ResponseHeadPrefixPart2.memory ResponseHeadPrefixPart1.memory ResponseHeadPrefixPart0.memory
  rw [StoreBytes.frame _ (frame+36#32) ((BitVec.ofNat 32 status)) (dst+0#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨36+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨0,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+40#32) (192#32) (dst+0#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨40+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨0,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+12#32) (32#32) (dst+0#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 0 12 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (frame+32#32) (flag) (dst+0#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨32+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨0,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+28#32) (body) (dst+0#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨28+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨0,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+11#32) ((BitVec.ofNat 32 (48+status%10))) (dst+0#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 0 11 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+10#32) ((BitVec.ofNat 32 (48+(status/10)%10))) (dst+0#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 0 10 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+9#32) ((BitVec.ofNat 32 (48+status/100))) (dst+0#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 0 9 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+8#32) (32#32) (dst+0#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 0 8 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+7#32) (49#32) (dst+0#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 0 7 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+6#32) (46#32) (dst+0#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 0 6 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+5#32) (49#32) (dst+0#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 0 5 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+4#32) (47#32) (dst+0#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 0 4 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+3#32) (80#32) (dst+0#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 0 3 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+2#32) (84#32) (dst+0#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 0 2 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+1#32) (84#32) (dst+0#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 0 1 (by decide) (by decide) (by decide)))]
  change ramPut _ _ _ _ = _
  exact ramPut_eq _ _ _
theorem cell1 (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat)
    (hsep : WordRegions.Disjoint frame 96 dst 192) :
    ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen (dst+1#32)=byteOf (84#32) 0 := by
  unfold ResponseHeadPrefix.memory ResponseHeadPrefixPart2.memory ResponseHeadPrefixPart1.memory ResponseHeadPrefixPart0.memory
  rw [StoreBytes.frame _ (frame+36#32) ((BitVec.ofNat 32 status)) (dst+1#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨36+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨1,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+40#32) (192#32) (dst+1#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨40+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨1,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+12#32) (32#32) (dst+1#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 1 12 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (frame+32#32) (flag) (dst+1#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨32+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨1,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+28#32) (body) (dst+1#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨28+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨1,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+11#32) ((BitVec.ofNat 32 (48+status%10))) (dst+1#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 1 11 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+10#32) ((BitVec.ofNat 32 (48+(status/10)%10))) (dst+1#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 1 10 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+9#32) ((BitVec.ofNat 32 (48+status/100))) (dst+1#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 1 9 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+8#32) (32#32) (dst+1#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 1 8 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+7#32) (49#32) (dst+1#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 1 7 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+6#32) (46#32) (dst+1#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 1 6 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+5#32) (49#32) (dst+1#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 1 5 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+4#32) (47#32) (dst+1#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 1 4 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+3#32) (80#32) (dst+1#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 1 3 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+2#32) (84#32) (dst+1#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 1 2 (by decide) (by decide) (by decide)))]
  change ramPut _ _ _ _ = _
  exact ramPut_eq _ _ _
theorem cell2 (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat)
    (hsep : WordRegions.Disjoint frame 96 dst 192) :
    ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen (dst+2#32)=byteOf (84#32) 0 := by
  unfold ResponseHeadPrefix.memory ResponseHeadPrefixPart2.memory ResponseHeadPrefixPart1.memory ResponseHeadPrefixPart0.memory
  rw [StoreBytes.frame _ (frame+36#32) ((BitVec.ofNat 32 status)) (dst+2#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨36+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨2,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+40#32) (192#32) (dst+2#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨40+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨2,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+12#32) (32#32) (dst+2#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 2 12 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (frame+32#32) (flag) (dst+2#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨32+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨2,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+28#32) (body) (dst+2#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨28+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨2,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+11#32) ((BitVec.ofNat 32 (48+status%10))) (dst+2#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 2 11 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+10#32) ((BitVec.ofNat 32 (48+(status/10)%10))) (dst+2#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 2 10 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+9#32) ((BitVec.ofNat 32 (48+status/100))) (dst+2#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 2 9 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+8#32) (32#32) (dst+2#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 2 8 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+7#32) (49#32) (dst+2#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 2 7 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+6#32) (46#32) (dst+2#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 2 6 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+5#32) (49#32) (dst+2#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 2 5 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+4#32) (47#32) (dst+2#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 2 4 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+3#32) (80#32) (dst+2#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 2 3 (by decide) (by decide) (by decide)))]
  change ramPut _ _ _ _ = _
  exact ramPut_eq _ _ _
theorem cell3 (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat)
    (hsep : WordRegions.Disjoint frame 96 dst 192) :
    ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen (dst+3#32)=byteOf (80#32) 0 := by
  unfold ResponseHeadPrefix.memory ResponseHeadPrefixPart2.memory ResponseHeadPrefixPart1.memory ResponseHeadPrefixPart0.memory
  rw [StoreBytes.frame _ (frame+36#32) ((BitVec.ofNat 32 status)) (dst+3#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨36+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨3,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+40#32) (192#32) (dst+3#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨40+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨3,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+12#32) (32#32) (dst+3#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 3 12 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (frame+32#32) (flag) (dst+3#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨32+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨3,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+28#32) (body) (dst+3#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨28+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨3,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+11#32) ((BitVec.ofNat 32 (48+status%10))) (dst+3#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 3 11 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+10#32) ((BitVec.ofNat 32 (48+(status/10)%10))) (dst+3#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 3 10 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+9#32) ((BitVec.ofNat 32 (48+status/100))) (dst+3#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 3 9 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+8#32) (32#32) (dst+3#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 3 8 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+7#32) (49#32) (dst+3#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 3 7 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+6#32) (46#32) (dst+3#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 3 6 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+5#32) (49#32) (dst+3#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 3 5 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+4#32) (47#32) (dst+3#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 3 4 (by decide) (by decide) (by decide)))]
  change ramPut _ _ _ _ = _
  exact ramPut_eq _ _ _
theorem cell4 (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat)
    (hsep : WordRegions.Disjoint frame 96 dst 192) :
    ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen (dst+4#32)=byteOf (47#32) 0 := by
  unfold ResponseHeadPrefix.memory ResponseHeadPrefixPart2.memory ResponseHeadPrefixPart1.memory ResponseHeadPrefixPart0.memory
  rw [StoreBytes.frame _ (frame+36#32) ((BitVec.ofNat 32 status)) (dst+4#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨36+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨4,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+40#32) (192#32) (dst+4#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨40+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨4,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+12#32) (32#32) (dst+4#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 4 12 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (frame+32#32) (flag) (dst+4#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨32+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨4,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+28#32) (body) (dst+4#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨28+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨4,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+11#32) ((BitVec.ofNat 32 (48+status%10))) (dst+4#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 4 11 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+10#32) ((BitVec.ofNat 32 (48+(status/10)%10))) (dst+4#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 4 10 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+9#32) ((BitVec.ofNat 32 (48+status/100))) (dst+4#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 4 9 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+8#32) (32#32) (dst+4#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 4 8 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+7#32) (49#32) (dst+4#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 4 7 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+6#32) (46#32) (dst+4#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 4 6 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+5#32) (49#32) (dst+4#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 4 5 (by decide) (by decide) (by decide)))]
  change ramPut _ _ _ _ = _
  exact ramPut_eq _ _ _
theorem cell5 (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat)
    (hsep : WordRegions.Disjoint frame 96 dst 192) :
    ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen (dst+5#32)=byteOf (49#32) 0 := by
  unfold ResponseHeadPrefix.memory ResponseHeadPrefixPart2.memory ResponseHeadPrefixPart1.memory ResponseHeadPrefixPart0.memory
  rw [StoreBytes.frame _ (frame+36#32) ((BitVec.ofNat 32 status)) (dst+5#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨36+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨5,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+40#32) (192#32) (dst+5#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨40+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨5,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+12#32) (32#32) (dst+5#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 5 12 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (frame+32#32) (flag) (dst+5#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨32+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨5,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+28#32) (body) (dst+5#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨28+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨5,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+11#32) ((BitVec.ofNat 32 (48+status%10))) (dst+5#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 5 11 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+10#32) ((BitVec.ofNat 32 (48+(status/10)%10))) (dst+5#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 5 10 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+9#32) ((BitVec.ofNat 32 (48+status/100))) (dst+5#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 5 9 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+8#32) (32#32) (dst+5#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 5 8 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+7#32) (49#32) (dst+5#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 5 7 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+6#32) (46#32) (dst+5#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 5 6 (by decide) (by decide) (by decide)))]
  change ramPut _ _ _ _ = _
  exact ramPut_eq _ _ _
theorem cell6 (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat)
    (hsep : WordRegions.Disjoint frame 96 dst 192) :
    ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen (dst+6#32)=byteOf (46#32) 0 := by
  unfold ResponseHeadPrefix.memory ResponseHeadPrefixPart2.memory ResponseHeadPrefixPart1.memory ResponseHeadPrefixPart0.memory
  rw [StoreBytes.frame _ (frame+36#32) ((BitVec.ofNat 32 status)) (dst+6#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨36+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨6,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+40#32) (192#32) (dst+6#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨40+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨6,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+12#32) (32#32) (dst+6#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 6 12 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (frame+32#32) (flag) (dst+6#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨32+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨6,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+28#32) (body) (dst+6#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨28+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨6,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+11#32) ((BitVec.ofNat 32 (48+status%10))) (dst+6#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 6 11 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+10#32) ((BitVec.ofNat 32 (48+(status/10)%10))) (dst+6#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 6 10 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+9#32) ((BitVec.ofNat 32 (48+status/100))) (dst+6#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 6 9 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+8#32) (32#32) (dst+6#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 6 8 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+7#32) (49#32) (dst+6#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 6 7 (by decide) (by decide) (by decide)))]
  change ramPut _ _ _ _ = _
  exact ramPut_eq _ _ _
theorem cell7 (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat)
    (hsep : WordRegions.Disjoint frame 96 dst 192) :
    ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen (dst+7#32)=byteOf (49#32) 0 := by
  unfold ResponseHeadPrefix.memory ResponseHeadPrefixPart2.memory ResponseHeadPrefixPart1.memory ResponseHeadPrefixPart0.memory
  rw [StoreBytes.frame _ (frame+36#32) ((BitVec.ofNat 32 status)) (dst+7#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨36+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨7,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+40#32) (192#32) (dst+7#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨40+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨7,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+12#32) (32#32) (dst+7#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 7 12 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (frame+32#32) (flag) (dst+7#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨32+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨7,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+28#32) (body) (dst+7#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨28+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨7,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+11#32) ((BitVec.ofNat 32 (48+status%10))) (dst+7#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 7 11 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+10#32) ((BitVec.ofNat 32 (48+(status/10)%10))) (dst+7#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 7 10 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+9#32) ((BitVec.ofNat 32 (48+status/100))) (dst+7#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 7 9 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+8#32) (32#32) (dst+7#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 7 8 (by decide) (by decide) (by decide)))]
  change ramPut _ _ _ _ = _
  exact ramPut_eq _ _ _
theorem cell8 (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat)
    (hsep : WordRegions.Disjoint frame 96 dst 192) :
    ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen (dst+8#32)=byteOf (32#32) 0 := by
  unfold ResponseHeadPrefix.memory ResponseHeadPrefixPart2.memory ResponseHeadPrefixPart1.memory ResponseHeadPrefixPart0.memory
  rw [StoreBytes.frame _ (frame+36#32) ((BitVec.ofNat 32 status)) (dst+8#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨36+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨8,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+40#32) (192#32) (dst+8#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨40+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨8,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+12#32) (32#32) (dst+8#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 8 12 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (frame+32#32) (flag) (dst+8#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨32+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨8,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+28#32) (body) (dst+8#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨28+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨8,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+11#32) ((BitVec.ofNat 32 (48+status%10))) (dst+8#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 8 11 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+10#32) ((BitVec.ofNat 32 (48+(status/10)%10))) (dst+8#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 8 10 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+9#32) ((BitVec.ofNat 32 (48+status/100))) (dst+8#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 8 9 (by decide) (by decide) (by decide)))]
  change ramPut _ _ _ _ = _
  exact ramPut_eq _ _ _
theorem cell9 (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat)
    (hsep : WordRegions.Disjoint frame 96 dst 192) :
    ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen (dst+9#32)=byteOf ((BitVec.ofNat 32 (48+status/100))) 0 := by
  unfold ResponseHeadPrefix.memory ResponseHeadPrefixPart2.memory ResponseHeadPrefixPart1.memory ResponseHeadPrefixPart0.memory
  rw [StoreBytes.frame _ (frame+36#32) ((BitVec.ofNat 32 status)) (dst+9#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨36+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨9,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+40#32) (192#32) (dst+9#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨40+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨9,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+12#32) (32#32) (dst+9#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 9 12 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (frame+32#32) (flag) (dst+9#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨32+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨9,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+28#32) (body) (dst+9#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨28+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨9,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+11#32) ((BitVec.ofNat 32 (48+status%10))) (dst+9#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 9 11 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (dst+10#32) ((BitVec.ofNat 32 (48+(status/10)%10))) (dst+9#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 9 10 (by decide) (by decide) (by decide)))]
  change ramPut _ _ _ _ = _
  exact ramPut_eq _ _ _
theorem cell10 (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat)
    (hsep : WordRegions.Disjoint frame 96 dst 192) :
    ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen (dst+10#32)=byteOf ((BitVec.ofNat 32 (48+(status/10)%10))) 0 := by
  unfold ResponseHeadPrefix.memory ResponseHeadPrefixPart2.memory ResponseHeadPrefixPart1.memory ResponseHeadPrefixPart0.memory
  rw [StoreBytes.frame _ (frame+36#32) ((BitVec.ofNat 32 status)) (dst+10#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨36+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨10,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+40#32) (192#32) (dst+10#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨40+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨10,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+12#32) (32#32) (dst+10#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 10 12 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (frame+32#32) (flag) (dst+10#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨32+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨10,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+28#32) (body) (dst+10#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨28+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨10,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+11#32) ((BitVec.ofNat 32 (48+status%10))) (dst+10#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 10 11 (by decide) (by decide) (by decide)))]
  change ramPut _ _ _ _ = _
  exact ramPut_eq _ _ _
theorem cell11 (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat)
    (hsep : WordRegions.Disjoint frame 96 dst 192) :
    ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen (dst+11#32)=byteOf ((BitVec.ofNat 32 (48+status%10))) 0 := by
  unfold ResponseHeadPrefix.memory ResponseHeadPrefixPart2.memory ResponseHeadPrefixPart1.memory ResponseHeadPrefixPart0.memory
  rw [StoreBytes.frame _ (frame+36#32) ((BitVec.ofNat 32 status)) (dst+11#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨36+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨11,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+40#32) (192#32) (dst+11#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨40+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨11,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (dst+12#32) (32#32) (dst+11#32) .b (by
    intro j
    have hj : j.val=0 := by have := j.isLt;change j.val<1 at this;omega
    simpa only [hj,BitVec.add_zero] using (Bytes.offset_ne dst 11 12 (by decide) (by decide) (by decide)))]
  rw [StoreBytes.frame _ (frame+32#32) (flag) (dst+11#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨32+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨11,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+28#32) (body) (dst+11#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨28+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨11,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  change ramPut _ _ _ _ = _
  exact ramPut_eq _ _ _
theorem cell12 (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat)
    (hsep : WordRegions.Disjoint frame 96 dst 192) :
    ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen (dst+12#32)=byteOf (32#32) 0 := by
  unfold ResponseHeadPrefix.memory ResponseHeadPrefixPart2.memory ResponseHeadPrefixPart1.memory ResponseHeadPrefixPart0.memory
  rw [StoreBytes.frame _ (frame+36#32) ((BitVec.ofNat 32 status)) (dst+12#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨36+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨12,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  rw [StoreBytes.frame _ (frame+40#32) (192#32) (dst+12#32) .w (by
    intro j
    have hn := Ne.symm (hsep ⟨40+j.val,by have := j.isLt;change j.val<4 at this;omega⟩ ⟨12,by decide⟩)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hn)]
  change ramPut _ _ _ _ = _
  exact ramPut_eq _ _ _
theorem written (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat)
    (hlo : 100≤status) (hhi : status≤599) (hsep : WordRegions.Disjoint frame 96 dst 192) :
    Bytes.At (ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen) dst (ResponseHeadPrefixSpec.bytes status) := by
  rw [ResponseHeadPrefixSpec.expanded status hlo hhi]
  intro i
  change ResponseHeadPrefix.memory ram frame dst ctptr body flag status ctlen (dst+BitVec.ofNat 32 i.val)=(ResponseHeadPrefixSpec.listing status)[i.val]
  have hi : i.val<13 := i.isLt
  have hh : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 ∨ i.val=6 ∨ i.val=7 ∨ i.val=8 ∨ i.val=9 ∨ i.val=10 ∨ i.val=11 ∨ i.val=12 := by omega
  rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
  · have hc := cell0 ram frame dst ctptr body flag status ctlen hsep
    simpa only [h0,ResponseHeadPrefixSpec.listing,List.getElem_cons_zero,List.getElem_cons_succ,HttpDecDigitsData.byte_nat,DecimalDigits.digit] using hc
  · have hc := cell1 ram frame dst ctptr body flag status ctlen hsep
    simpa only [h1,ResponseHeadPrefixSpec.listing,List.getElem_cons_zero,List.getElem_cons_succ,HttpDecDigitsData.byte_nat,DecimalDigits.digit] using hc
  · have hc := cell2 ram frame dst ctptr body flag status ctlen hsep
    simpa only [h2,ResponseHeadPrefixSpec.listing,List.getElem_cons_zero,List.getElem_cons_succ,HttpDecDigitsData.byte_nat,DecimalDigits.digit] using hc
  · have hc := cell3 ram frame dst ctptr body flag status ctlen hsep
    simpa only [h3,ResponseHeadPrefixSpec.listing,List.getElem_cons_zero,List.getElem_cons_succ,HttpDecDigitsData.byte_nat,DecimalDigits.digit] using hc
  · have hc := cell4 ram frame dst ctptr body flag status ctlen hsep
    simpa only [h4,ResponseHeadPrefixSpec.listing,List.getElem_cons_zero,List.getElem_cons_succ,HttpDecDigitsData.byte_nat,DecimalDigits.digit] using hc
  · have hc := cell5 ram frame dst ctptr body flag status ctlen hsep
    simpa only [h5,ResponseHeadPrefixSpec.listing,List.getElem_cons_zero,List.getElem_cons_succ,HttpDecDigitsData.byte_nat,DecimalDigits.digit] using hc
  · have hc := cell6 ram frame dst ctptr body flag status ctlen hsep
    simpa only [h6,ResponseHeadPrefixSpec.listing,List.getElem_cons_zero,List.getElem_cons_succ,HttpDecDigitsData.byte_nat,DecimalDigits.digit] using hc
  · have hc := cell7 ram frame dst ctptr body flag status ctlen hsep
    simpa only [h7,ResponseHeadPrefixSpec.listing,List.getElem_cons_zero,List.getElem_cons_succ,HttpDecDigitsData.byte_nat,DecimalDigits.digit] using hc
  · have hc := cell8 ram frame dst ctptr body flag status ctlen hsep
    simpa only [h8,ResponseHeadPrefixSpec.listing,List.getElem_cons_zero,List.getElem_cons_succ,HttpDecDigitsData.byte_nat,DecimalDigits.digit] using hc
  · have hc := cell9 ram frame dst ctptr body flag status ctlen hsep
    simpa only [h9,ResponseHeadPrefixSpec.listing,List.getElem_cons_zero,List.getElem_cons_succ,HttpDecDigitsData.byte_nat,DecimalDigits.digit] using hc
  · have hc := cell10 ram frame dst ctptr body flag status ctlen hsep
    simpa only [h10,ResponseHeadPrefixSpec.listing,List.getElem_cons_zero,List.getElem_cons_succ,HttpDecDigitsData.byte_nat,DecimalDigits.digit] using hc
  · have hc := cell11 ram frame dst ctptr body flag status ctlen hsep
    simpa only [h11,ResponseHeadPrefixSpec.listing,List.getElem_cons_zero,List.getElem_cons_succ,HttpDecDigitsData.byte_nat,DecimalDigits.digit] using hc
  · have hc := cell12 ram frame dst ctptr body flag status ctlen hsep
    simpa only [h12,ResponseHeadPrefixSpec.listing,List.getElem_cons_zero,List.getElem_cons_succ,HttpDecDigitsData.byte_nat,DecimalDigits.digit] using hc
end E5R.Thermostat.ResponseHeadPrefixData
