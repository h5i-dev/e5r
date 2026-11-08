import Projects.thermostat.HeadRamCopy
namespace E5R.Thermostat.HeadRamCopyMemory
open E5R E5R.Thermostat

/-- Each copied word is the corresponding word in the input snapshot. -/
theorem word (ram : Word → BitVec 8) (dst : Word) (ws : List Word)
    (i : Fin ws.length) (nowrap : dst.toNat+4*ws.length<2^32) :
    ramRead (AlignedCopyLoop.writes ram dst ws) (dst+BitVec.ofNat 32 (4*i.val)) .w=ws[i.val] := by
  induction ws generalizing ram dst with
  | nil => exact Fin.elim0 i
  | cons w ws ih =>
    cases i with
    | mk n hn =>
      cases n with
      | zero =>
        simp only [Nat.mul_zero,BitVec.add_zero,List.getElem_cons_zero]
        change ramRead (AlignedCopyLoop.writes (ramWrite ram dst w .w) (dst+4#32) ws) dst .w=w
        rw [show ramRead (AlignedCopyLoop.writes (ramWrite ram dst w .w) (dst+4#32) ws) dst .w=ramRead (ramWrite ram dst w .w) dst .w by
          apply ramRead_w_congr
          intro k hk
          apply AlignedCopyLoop.frame
          intro j eq
          have hj := j.isLt
          rw [BitVec.add_assoc,←BitVec.ofNat_add] at eq
          exact WordZero.offset_ne dst k (4+j.val) (by omega) (by simp only [List.length_cons] at nowrap;omega) (by omega) eq]
        exact ramRead_ramWrite_w ram dst w
      | succ n =>
        have bound : n<ws.length := by simp only [List.length_cons] at hn;omega
        have nextNat := WordZero.add_nat dst 4 (by simp only [List.length_cons] at nowrap;omega)
        have address : dst+BitVec.ofNat 32 (4*(n+1))=(dst+4#32)+BitVec.ofNat 32 (4*n) := by
          rw [BitVec.add_assoc,←BitVec.ofNat_add,show 4+4*n=4*(n+1) by omega]
        change ramRead (AlignedCopyLoop.writes (ramWrite ram dst w .w) (dst+4#32) ws) (dst+BitVec.ofNat 32 (4*(n+1))) .w=ws[n]
        rw [address]
        exact ih (ramWrite ram dst w .w) (dst+4#32) ⟨n,bound⟩ (by rw [nextNat];simp only [List.length_cons] at nowrap;omega)

def snapshot (ram : Word → BitVec 8) (src : Word) (n : Nat) : List Word :=
  List.ofFn fun i : Fin n => ramRead ram (src+BitVec.ofNat 32 (4*i.val)) .w

@[simp] theorem snapshot_length (ram : Word → BitVec 8) (src : Word) (n : Nat) : (snapshot ram src n).length=n := by simp [snapshot]

theorem source (B : Board) (ram : Word → BitVec 8) (src : Word) (n : Nat)
    (aligned : src.toNat%4=0) (block : Memory.Block B src (4*n)) :
    HeadCopyRamSource.Source B ram src (snapshot ram src n) := by
  refine ⟨aligned,by simpa only [snapshot_length] using block,?_⟩
  intro i
  simp [snapshot]

theorem copied (ram : Word → BitVec 8) (src dst : Word) (n : Nat) (i : Fin n)
    (nowrap : dst.toNat+4*n<2^32) :
    ramRead (AlignedCopyLoop.writes ram dst (snapshot ram src n)) (dst+BitVec.ofNat 32 (4*i.val)) .w=
      ramRead ram (src+BitVec.ofNat 32 (4*i.val)) .w := by
  have h := word ram dst (snapshot ram src n) ⟨i.val,by simpa only [snapshot_length] using i.isLt⟩ (by simpa only [snapshot_length] using nowrap)
  simpa [snapshot] using h
end E5R.Thermostat.HeadRamCopyMemory
