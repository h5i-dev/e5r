import Projects.thermostat.I16Code
import Projects.thermostat.SmallCopyTurn
import Projects.thermostat.DigitSmallMath
namespace E5R.Thermostat.I16DigitStore
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (n k : Nat)
    (hp : c.pc = 0x80004f66#32) (h11 : c.get 11 = BitVec.ofNat 32 (48+n))
    (h12 : c.get 12 = (sp+3#32)+BitVec.ofNat 32 (k-1)) (hn : n < 10) (hk : 1 ≤ k) (hkb : k ≤ 5)
    (hm : Memory.Block B sp 16) :
    DetStep B img ⟨c,ram⟩ ⟨c.goto 0x80004f6a#32,ramPut ram (sp+BitVec.ofNat 32 (k+2)) (DecimalDigits.digit n)⟩ := by
  have he : (sp+3#32)+BitVec.ofNat 32 (k-1) = sp+BitVec.ofNat 32 (k+2) := by
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    congr 2
    omega
  refine detStep_of (by rw [hp];decide) (by rw [hp];exact di2147503974) fun o => ?_
  rw [exec_store,h12,h11,BitVec.add_zero,he,interp_store_ram (B := B) (img := img) (w := .b) o
    (Nat.mod_one _) (Memory.block_access hm (off := k+2) (by decide) (by change k+2+1 ≤ 16;omega)),hp]
  change interp B img o (.done (c.goto 0x80004f6a#32))
    (ramPut ram (sp+BitVec.ofNat 32 (k+2)) (byteOf (BitVec.ofNat 32 (48+n)) 0)) 0 [] = _
  rw [←DigitSmallMath.digit_nat n hn,SmallCopyTurn.byte_word];rfl
end E5R.Thermostat.I16DigitStore
