import Projects.thermostat.I16One
import Projects.thermostat.I16Small
import Projects.thermostat.I16Large
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.I16Digits
open E5R E5R.Thermostat

/-- Every i16 value, including -32768, constructs its independent decimal
    bytes by actual ELF instructions before calling the actual formatter. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp ptr fmt : Word) (v : BitVec 16)
    (hp : c.pc = 0x80004e5e#32) (hsp : c.get 2 = sp+16#32) (h10 : c.get 10 = ptr) (h11 : c.get 11 = fmt)
    (hst : Memory.Block B sp 16) (hsa : sp.toNat%4 = 0)
    (hm : Memory.Block B ptr 2) (ha : ptr.toNat%2 = 0)
    (hv : extend .h true (ramRead ram ptr .h) = SignedMagnitude.input v)
    (hsep : WordRegions.Disjoint ptr 2 sp 16)
    (hrom : ∀ i : Fin 100, ∀ unit : Bool, B.inRam (DigitTable.address i unit) 1 = false) :
    ∃ d k r, k ≤ 77 ∧ DetSteps B img k ⟨c,ram⟩ ⟨d,r⟩ ∧
      I16Ready.Ready c d sp fmt v (I16Ready.offset v.toInt.natAbs) (I16Ready.length v.toInt.natAbs) ∧
      ReadBytes.Span B img r (sp+BitVec.ofNat 32 (I16Ready.offset v.toInt.natAbs)) (ReplyJson.decimal v.toInt.natAbs) ∧
      ViewFrame.Region (I16Save.memory ram sp c) r (sp+8#32) 8 ∧
      (∀ x, (∀ i : Fin 16, x ≠ sp+BitVec.ofNat 32 i.val) → r x = ram x) := by
  let n := v.toInt.natAbs
  by_cases h1 : n < 10
  · have ho : I16Ready.offset n = 7 := by simp only [I16Ready.offset,ite_eq_left h1]
    have hl : I16Ready.length n = 1 := by rw [I16Ready.length,ho]
    obtain ⟨d,td,hd,hbytes,hs,hf⟩ := I16One.contract B c ram sp ptr fmt v hp hsp h10 h11 hst hsa hm ha hv hsep h1 (fun i => hrom i true)
    refine ⟨d,44,I16One.memory ram sp c v,by decide,td,?_,?_,hs,hf⟩
    · rw [ho,hl]
      exact ⟨hd.pc,hd.spReg,hd.x1,hd.x10,hd.x11,hd.x12,hd.x13,hd.x14,hd.x15,hd.csr,hd.saved⟩
    · rw [ho];exact hbytes
  · by_cases h2 : n < 1000
    · have ho : I16Ready.offset n = if n < 100 then 6 else 5 := by
        simp only [I16Ready.offset,ite_eq_right h1,ite_eq_left h2]
      have hl : I16Ready.length n = if n < 100 then 2 else 3 := by
        rw [I16Ready.length,ho]
        by_cases h : n < 100
        · simp only [ite_eq_left h]
        · simp only [ite_eq_right h]
      obtain ⟨d,k,r,hk,td,hd,hbytes,hs,hf⟩ := I16Small.contract B c ram sp ptr fmt v hp hsp h10 h11 hst hsa hm ha hv hsep (by omega) h2 hrom
      refine ⟨d,k,r,by omega,td,?_,?_,hs,hf⟩
      · rw [ho,hl];exact hd
      · rw [ho];exact hbytes
    · have h10n : ¬n < 100 := by omega
      have ho : I16Ready.offset n = if n < 10000 then 4 else 3 := by
        simp only [I16Ready.offset,ite_eq_right h1,ite_eq_right h10n,ite_eq_right h2]
      have hl : I16Ready.length n = if n < 10000 then 4 else 5 := by
        rw [I16Ready.length,ho]
        by_cases h : n < 10000
        · simp only [ite_eq_left h]
        · simp only [ite_eq_right h]
      obtain ⟨d,k,r,hk,td,hd,hbytes,hs,hf⟩ := I16Large.contract B c ram sp ptr fmt v hp hsp h10 h11 hst hsa hm ha hv hsep (by omega) hrom
      refine ⟨d,k,r,by omega,td,?_,?_,hs,hf⟩
      · rw [ho,hl];exact hd
      · rw [ho];exact hbytes
end E5R.Thermostat.I16Digits
