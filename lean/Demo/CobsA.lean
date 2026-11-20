import Demo.CobsSpec
import Demo.Cobs.ImageA

namespace Demo.Cobs
open E5R Demo.Cobs.ImageA

/-- `cobs_decode` as plain clang -O2 -march=rv64gc compiled it (demo/elf/cobs.a.elf).
    No block/loop tree: the cut points are read off the control-flow graph by
    hand. The decode loop is entered by a jump into its middle (0x111b8), past
    its exit test at 0x111b4; the cut point is 0x111b8, which every trip
    around the loop passes, with the copy loop's 0x111d8 and the scan's 0x11194. -/
set_option maxHeartbeats 20000000 in
theorem cobs_a : VerifiedC code cobs_decode_dom cobs_decode_entry spec := by
  rintro ⟨r, buf, orig⟩ s he ⟨ha0, ha1, ha2, hlen, hmem, hal, hdis⟩
  e5r_auto_c cobs_decode_entry cobs_decode_size s he
    loop_inv 0x11194 (fun u => ∃ k, u.reg 7 = BitVec.ofNat 64 k ∧ k < orig.length ∧ k ≤ frameLen orig ∧
        u.reg 10 = r ∧ u.reg 11 = buf ∧ u.reg 12 = BitVec.ofNat 64 orig.length ∧ u.mem = s.mem)
      measure (fun u => 3 * orig.length + 3 - (u.reg 7).toNat)
    loop_inv 0x111b8 (fun u => ∃ src dst L, u.reg 5 = BitVec.ofNat 64 src ∧
        u.reg 12 = BitVec.ofNat 64 dst ∧ readBytes u.mem buf orig.length = L ∧
        u.reg 10 = r ∧ u.reg 11 = buf ∧ u.reg 7 = BitVec.ofNat 64 (frameLen orig) ∧
        u.reg 16 = buf + 1 ∧ src < frameLen orig ∧ dst ≤ src ∧ L.length = orig.length ∧
        L.drop dst = orig.drop dst ∧
        decodeFrame (orig.take (frameLen orig)) =
          prepend (L.take dst) (decodeFrame ((orig.take (frameLen orig)).drop src)))
      measure (fun u => 2 * (frameLen orig - (u.reg 5).toNat) + 1)
    loop_inv 0x111d8 (fun u => ∃ p cnt dst L c e, u.reg 15 = buf + BitVec.ofNat 64 p ∧
        u.reg 14 = BitVec.ofNat 64 cnt ∧ u.reg 12 = BitVec.ofNat 64 dst ∧
        readBytes u.mem buf orig.length = L ∧ u.reg 17 = BitVec.ofNat 64 c ∧
        u.reg 6 = BitVec.ofNat 64 e ∧
        u.reg 10 = r ∧ u.reg 11 = buf ∧ u.reg 7 = BitVec.ofNat 64 (frameLen orig) ∧
        u.reg 16 = buf + 1 ∧ p + cnt = e ∧ 0 < cnt ∧ e ≤ frameLen orig ∧ dst < p ∧ c < 256 ∧
        L.length = orig.length ∧ L.drop dst = orig.drop dst ∧
        decodeFrame (orig.take (frameLen orig)) =
          prepend (L.take dst ++ (orig.drop p).take cnt ++ zeroAfter c e (frameLen orig))
            (decodeFrame ((orig.take (frameLen orig)).drop e)))
      measure (fun u => 2 * (frameLen orig - ((u.reg 15) - buf).toNat))
  all_goals sorry
