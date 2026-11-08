import Projects.thermostat.RequestAuth
import Projects.thermostat.ViewFrame
import Projects.thermostat.Engine
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.TxnScratch
open E5R E5R.Thermostat

def Separate (obj : Word) (len : Nat) (base : Word) : Prop :=
  ∀ i : Fin len, ∀ j : Fin 128, obj+BitVec.ofNat 32 i.val ≠ base+BitVec.ofNat 32 j.val

def memory (ram : Word → BitVec 8) (sp : Word) (header : Option (List (BitVec 8))) (admin : Bool) : Word → BitVec 8 :=
  ramPut (RequestAuth.memory ram sp header) (sp+9#32) (Encoding.boolByte admin)

theorem frame (ram : Word → BitVec 8) (sp x : Word) (header : Option (List (BitVec 8))) (admin : Bool)
    (h9 : x ≠ sp+9#32) (h24 : x ≠ sp+24#32) : memory ram sp header admin x = ram x := by
  rw [memory,ramPut_ne _ h9]
  exact RequestAuth.memory_frame ram sp x header h24

theorem auth_region (ram : Word → BitVec 8) (p obj : Word) (len : Nat) (header : Option (List (BitVec 8)))
    (hsep : Separate obj len p) : ViewFrame.Region ram (RequestAuth.memory ram (p+80#32) header) obj len := by
  intro i
  apply RequestAuth.memory_frame
  have he : (p+80#32)+24#32 = p+104#32 := by rw [BitVec.add_assoc];rfl
  rw [he];exact hsep i ⟨104,by decide⟩

theorem region (ram : Word → BitVec 8) (p obj : Word) (len : Nat) (header : Option (List (BitVec 8))) (admin : Bool)
    (hsep : Separate obj len p) : ViewFrame.Region ram (memory ram (p+80#32) header admin) obj len := by
  intro i
  apply frame
  · have he : (p+80#32)+9#32 = p+89#32 := by rw [BitVec.add_assoc];rfl
    rw [he];exact hsep i ⟨89,by decide⟩
  · have he : (p+80#32)+24#32 = p+104#32 := by rw [BitVec.add_assoc];rfl
    rw [he];exact hsep i ⟨104,by decide⟩

theorem actor (ram : Word → BitVec 8) (p : Word) (header : Option (List (BitVec 8))) (admin : Bool) :
    memory ram (p+80#32) header admin (p+89#32) = Encoding.boolByte admin := by
  have he : (p+80#32)+9#32 = p+89#32 := by rw [BitVec.add_assoc];rfl
  unfold memory
  rw [he,ramPut_eq]

theorem decoder_separate {obj len p} (h : Separate obj len p) :
    ∀ i : Fin len, ∀ j : Fin 16, obj+BitVec.ofNat 32 i.val ≠ (p+64#32)+BitVec.ofNat 32 j.val := by
  intro i j
  have hi := h i ⟨64+j.val,by have := j.isLt;omega⟩
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hi

theorem engine_separate {eng p} (h : Separate eng 25 p) : Engine.Separate eng p := by
  intro i j;exact h ⟨i.val,by have := i.isLt;omega⟩ j

theorem outside (ram : Word → BitVec 8) (p x : Word) (header : Option (List (BitVec 8))) (admin : Bool)
    (hx : ∀ i : Fin 128, x ≠ p+BitVec.ofNat 32 i.val) : memory ram (p+80#32) header admin x = ram x := by
  apply frame
  · have he : (p+80#32)+9#32 = p+89#32 := by rw [BitVec.add_assoc];rfl
    rw [he];exact hx ⟨89,by decide⟩
  · have he : (p+80#32)+24#32 = p+104#32 := by rw [BitVec.add_assoc];rfl
    rw [he];exact hx ⟨104,by decide⟩
/-- Nonwrapping ordered allocations are disjoint without enumerating byte pairs. -/
theorem separate_of_before (obj p : Word) (len : Nat)
    (ho : obj.toNat+len ≤ p.toNat) (hp : p.toNat+128 ≤ 2^32) : Separate obj len p := by
  intro i j he
  have hi := i.isLt
  have hj := j.isLt
  have hpn := p.isLt
  have hi32 : i.val < 2^32 := by omega
  have hj32 : j.val < 2^32 := by omega
  have hoi : obj.toNat+i.val < 2^32 := by omega
  have hpj : p.toNat+j.val < 2^32 := by omega
  have hh := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hi32,Nat.mod_eq_of_lt hj32,
    Nat.mod_eq_of_lt hoi,Nat.mod_eq_of_lt hpj] at hh
  omega
end E5R.Thermostat.TxnScratch
