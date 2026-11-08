import Projects.thermostat.MainRamCopyByte
set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.RamWriteBytes
open E5R E5R.Thermostat

/-- Every byte actually written by SB/SH/SW, including modular addresses.
    No initial-memory, alignment or host evaluation assumption is needed. -/
theorem written (ram : Word → BitVec 8) (p v : Word) (w : Width) (i : Fin w.bytes) :
    ramWrite ram p v w (p+BitVec.ofNat 32 i.val)=byteOf v i.val := by
  cases w with
  | b =>
    have zero : i.val=0 := by have hi : i.val<1 := i.isLt;omega
    simp only [zero,BitVec.add_zero,ramWrite,ramPut,ite_true]
  | h =>
    have casesIndex : i.val=0 ∨ i.val=1 := by have hi : i.val<2 := i.isLt;omega
    rcases casesIndex with zero|one
    · have ne : p≠p+1 := by simp [BitVec.self_eq_add_right]
      simp only [zero,BitVec.add_zero,ramWrite,ramPut,ne,ite_false,ite_true]
    · simp only [one,ramWrite,show (1 : Word)=1#32 by decide +kernel,ramPut,ite_true]
  | w =>
    have read := MainRamCopyByte.read_byte (ramWrite ram p v .w) p ⟨i.val,i.isLt⟩
    rw [ramRead_ramWrite_w] at read
    exact read.symm
end E5R.Thermostat.RamWriteBytes
