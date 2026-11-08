import Projects.thermostat.SharedResponseStore
import Projects.thermostat.StoreBytes
import Projects.thermostat.WordRegions
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.SharedResponseMemory
open E5R E5R.Thermostat

/-- Live bytes in the real response Future. Padding stays unconstrained. -/
def liveByte (io0 io1 io2 saved status mimeLength mime close methodMinus used : Word) (i : Fin 40) : Option (BitVec 8) :=
  if i.val<4 then some (byteOf io0 i.val)
  else if i.val<8 then some (byteOf io1 (i.val-4))
  else if 16≤i.val ∧ i.val<20 then some (byteOf io2 (i.val-16))
  else if 20≤i.val ∧ i.val<24 then some (byteOf mime (i.val-20))
  else if 24≤i.val ∧ i.val<28 then some (byteOf mimeLength (i.val-24))
  else if 28≤i.val ∧ i.val<32 then some (byteOf used (i.val-28))
  else if i.val=32 then some (byteOf status 0)
  else if i.val=33 then some (byteOf status 1)
  else if i.val=34 then some (byteOf close 0)
  else if i.val=35 then some (byteOf saved 0)
  else if i.val=37 then some 0#8
  else if i.val=38 then some (byteOf (alu .sltu methodMinus 1#32) 0)
  else none

def At (ram : Word → BitVec 8) (fp io0 io1 io2 saved status mimeLength mime close methodMinus used : Word) : Prop :=
  ∀ i : Fin 40, ∀ v, liveByte io0 io1 io2 saved status mimeLength mime close methodMinus used i=some v → ram ((fp+108#32)+BitVec.ofNat 32 i.val)=v

theorem stored (ram : Word → BitVec 8) (sp fp io0 io1 io2 saved status mimeLength mime close methodMinus used : Word)
    (hs : WordRegions.Disjoint fp 148 sp 24) :
    At (SharedResponseStore.memory ram sp fp io0 io1 io2 saved status mimeLength mime close methodMinus used) fp io0 io1 io2 saved status mimeLength mime close methodMinus used := by
  intro i value hv
  have hi := i.isLt
  have hsp0 : (fp+108#32)+BitVec.ofNat 32 i.val≠sp+20#32 := by
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hs ⟨108+i.val,by omega⟩ ⟨20,by decide⟩
  have hsp1 : (fp+108#32)+BitVec.ofNat 32 i.val≠sp+21#32 := by
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hs ⟨108+i.val,by omega⟩ ⟨21,by decide⟩
  have hsp2 : (fp+108#32)+BitVec.ofNat 32 i.val≠sp+22#32 := by
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hs ⟨108+i.val,by omega⟩ ⟨22,by decide⟩
  have hsp3 : (fp+108#32)+BitVec.ofNat 32 i.val≠sp+23#32 := by
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hs ⟨108+i.val,by omega⟩ ⟨23,by decide⟩
  have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 ∨ i.val=6 ∨ i.val=7 ∨ i.val=8 ∨ i.val=9 ∨ i.val=10 ∨ i.val=11 ∨ i.val=12 ∨ i.val=13 ∨ i.val=14 ∨ i.val=15 ∨ i.val=16 ∨ i.val=17 ∨ i.val=18 ∨ i.val=19 ∨ i.val=20 ∨ i.val=21 ∨ i.val=22 ∨ i.val=23 ∨ i.val=24 ∨ i.val=25 ∨ i.val=26 ∨ i.val=27 ∨ i.val=28 ∨ i.val=29 ∨ i.val=30 ∨ i.val=31 ∨ i.val=32 ∨ i.val=33 ∨ i.val=34 ∨ i.val=35 ∨ i.val=36 ∨ i.val=37 ∨ i.val=38 ∨ i.val=39 := by omega
  rcases hc with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  all_goals simp [liveByte,h] at hv
  all_goals subst value
  all_goals simp [h,BitVec.add_assoc] at hsp0 hsp1 hsp2 hsp3
  all_goals simp [SharedResponseStore.memory,h,ramWrite,ramPut,BitVec.add_assoc,BitVec.add_right_inj,BitVec.self_eq_add_right,byteOf,hsp0,hsp1,hsp2,hsp3]
end E5R.Thermostat.SharedResponseMemory
