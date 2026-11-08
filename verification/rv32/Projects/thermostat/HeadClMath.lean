import Projects.thermostat.ReadBytes
import Projects.thermostat.HeadHeaderLiterals
import Projects.thermostat.Usize
namespace E5R.Thermostat.HeadClMath
open E5R E5R.Thermostat HttpRequestSpec

theorem guard (start length k : Nat) (width : start+14≤length) (bound : length≤2048) (hk : k<14) :
    taken .eq ((BitVec.ofNat 32 length-BitVec.ofNat 32 start)+BitVec.ofNat 32 (14-k)) 14#32=false := by
  rw [BitVec.ofNat_sub_ofNat_of_le length start (by omega) (by omega),←BitVec.ofNat_add]
  change decide (BitVec.ofNat 32 (length-start+(14-k))=BitVec.ofNat 32 14)=false
  have neq : BitVec.ofNat 32 (length-start+(14-k))≠BitVec.ofNat 32 14 := by
    intro eq
    have h := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat] at h
    omega
  simp [neq]

theorem count_sub (k : Nat) (hk : k<14) :
    BitVec.ofNat 32 (14-k)+0xffffffff#32=BitVec.ofNat 32 (14-(k+1)) := by
  rw [show 14-k=(14-(k+1))+1 by omega,BitVec.ofNat_add,BitVec.add_assoc,
    show 1#32+0xffffffff#32=0#32 by decide +kernel,BitVec.add_zero]

theorem count_test (k : Nat) (hk : k<14) :
    taken .ne (BitVec.ofNat 32 (14-(k+1))) (0 : Word)=decide (k+1<14) := by
  change taken .ne (BitVec.ofNat 32 (14-(k+1))) (BitVec.ofNat 32 0)=_
  rw [Usize.ne _ _ (by omega) (by decide)]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

theorem literal_bound (k : Fin 14) : litContentLength[k.val]<256 := by revert k;decide +kernel

theorem literal_byte (B : Board) (ram : Word → BitVec 8) (k : Fin 14)
    (outside : B.inRam (BitVec.ofNat 32 (0x80005de0+k.val)) 1=false) :
    ReadBytes.Byte B img ram (BitVec.ofNat 32 (0x80005de0+k.val)) (BitVec.ofNat 8 litContentLength[k.val]) := by
  apply ReadBytes.Byte.rom outside
  have kb := k.isLt
  have vb := literal_bound k
  have address : (BitVec.ofNat 32 (0x80005de0+k.val)).toNat=0x80005de0+k.val := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [address,HeadHeaderLiterals.content_rom]
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt vb]

end E5R.Thermostat.HeadClMath
