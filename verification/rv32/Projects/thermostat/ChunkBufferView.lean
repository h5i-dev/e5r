import Projects.thermostat.Bytes
import Projects.thermostat.ViewFrame
namespace E5R.Thermostat.ChunkBufferView
open E5R E5R.Thermostat

def Unread (wire : Nat → BitVec 8) (ram : Word → BitVec 8) (sp : Word) (read filled : Nat) : Prop :=
  ∀ k, read≤k → k<filled → ram ((sp+132#32)+BitVec.ofNat 32 k)=wire k

def Body (ram : Word → BitVec 8) (sp : Word) (start : Nat) (body : List (BitVec 8)) : Prop :=
  Bytes.At ram ((sp+132#32)+BitVec.ofNat 32 start) body

theorem address (sp : Word) (a b : Nat) :
    ((sp+132#32)+BitVec.ofNat 32 a)+BitVec.ofNat 32 b=(sp+132#32)+BitVec.ofNat 32 (a+b) := by
  rw [BitVec.add_assoc,←BitVec.ofNat_add]

theorem body_frame {before after sp start written body}
    (hb : Body before sp start body) (hlen : written=start+body.length) (hw : written≤2048)
    (hf : ViewFrame.Region before after (sp+132#32) 2048) : Body after sp start body := by
  intro i
  have hi := i.isLt
  rw [address,hf ⟨start+i.val,by omega⟩]
  simpa only [address] using hb i

theorem unread_frame {wire before after sp read filled}
    (hu : Unread wire before sp read filled) (hf : ViewFrame.Region before after (sp+132#32) 2048)
    (hc : filled≤2048) : Unread wire after sp (read+1) filled := by
  intro k hk he
  rw [hf ⟨k,by omega⟩]
  exact hu k (by omega) he

theorem body_data {before after sp start written body b}
    (hb : Body before sp start body) (hlen : written=start+body.length) (hw : written<2048)
    (stored : after ((sp+132#32)+BitVec.ofNat 32 written)=b)
    (other : ∀ k, k<2048 → k≠written →
      after ((sp+132#32)+BitVec.ofNat 32 k)=before ((sp+132#32)+BitVec.ofNat 32 k)) :
    Body after sp start (body++[b]) := by
  intro i
  have hi := i.isLt
  change after (((sp+132#32)+BitVec.ofNat 32 start)+BitVec.ofNat 32 i.val)=(body++[b])[i.val]
  rw [address]
  by_cases left : i.val<body.length
  · rw [List.getElem_append_left left,other (start+i.val) (by omega) (by omega)]
    have old := hb ⟨i.val,left⟩
    change before (((sp+132#32)+BitVec.ofNat 32 start)+BitVec.ofNat 32 i.val)=body[i.val] at old
    simpa only [address] using old
  · have endIndex : i.val=body.length := by simp only [List.length_append,List.length_singleton] at hi;omega
    have addr : start+i.val=written := by omega
    rw [addr,stored,List.getElem_append_right (by omega)]
    simp only [endIndex,Nat.sub_self,List.getElem_cons_zero]

theorem unread_data {wire before after sp read written filled}
    (hu : Unread wire before sp read filled) (hw : written≤read) (hc : filled≤2048)
    (other : ∀ k, k<2048 → k≠written →
      after ((sp+132#32)+BitVec.ofNat 32 k)=before ((sp+132#32)+BitVec.ofNat 32 k)) :
    Unread wire after sp (read+1) filled := by
  intro k hk he
  rw [other k (by omega) (by omega)]
  exact hu k (by omega) he

end E5R.Thermostat.ChunkBufferView
