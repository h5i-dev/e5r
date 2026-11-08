import Projects.thermostat.ViewFrame
namespace E5R.Thermostat.MainHalfMemory
open E5R E5R.Thermostat

theorem frame {before after : Word → BitVec 8} {p : Word} {n : Nat}
    (h : ViewFrame.Region before after p n) (k : Nat) (bound : k+2≤n) :
    ramRead after (p+BitVec.ofNat 32 k) .h=ramRead before (p+BitVec.ofNat 32 k) .h := by
  have b0 := h ⟨k,by omega⟩
  have b1 : after ((p+BitVec.ofNat 32 k)+1)=before ((p+BitVec.ofNat 32 k)+1) := by
    simpa only [show (1 : Word)=1#32 by decide +kernel,BitVec.add_assoc,←BitVec.ofNat_add] using h ⟨k+1,by omega⟩
  simp only [ramRead,b0,b1]

/-- Real zero halfword store, under either signed or unsigned load extension. -/
theorem zero_store (ram : Word → BitVec 8) (p : Word) (signed : Bool) :
    extend .h signed (ramRead (ramWrite ram p 0#32 .h) p .h)=0#32 := by
  have b0 : ramWrite ram p 0#32 .h p=0#8 := by
    have different : p≠p+1 := by simp [BitVec.self_eq_add_right]
    simp only [ramWrite,ramPut,different,ite_false,ite_true,show byteOf 0#32 0=0#8 by decide +kernel]
  have b1 : ramWrite ram p 0#32 .h (p+1)=0#8 := by
    simp only [ramWrite,ramPut,ite_true,show byteOf 0#32 1=0#8 by decide +kernel]
  rw [ramRead,b0,b1]
  cases signed <;> decide +kernel
end E5R.Thermostat.MainHalfMemory
