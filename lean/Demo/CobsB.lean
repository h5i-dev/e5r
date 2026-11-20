import Demo.CobsSpec
import Demo.Cobs.ImageB

namespace Demo.Cobs
open E5R Demo.Cobs.ImageB

set_option maxHeartbeats 20000000 in
theorem cobs_b : Verified code cobs_decode_dom cobs_decode_entry spec := by
  rintro ⟨r, buf, orig⟩ s he ⟨ha0, ha1, ha2, hlen, hmem, hal, hdis⟩
  e5r_auto cobs_decode_func s he
    loop_inv 0x11198 (fun u => ∃ k, u.reg 13 = BitVec.ofNat 64 k ∧ k < orig.length ∧ k ≤ frameLen orig ∧
        u.reg 10 = r ∧ u.reg 11 = buf ∧ u.reg 12 = BitVec.ofNat 64 orig.length ∧ u.mem = s.mem)
      measure (fun u => 3 * orig.length + 3 - (u.reg 13).toNat)
    loop_inv 0x111cc (fun u => ∃ src dst L, u.reg 15 = BitVec.ofNat 64 src ∧
        u.reg 12 = BitVec.ofNat 64 dst ∧ readBytes u.mem buf orig.length = L ∧
        u.reg 10 = r ∧ u.reg 11 = buf ∧ u.reg 13 = BitVec.ofNat 64 (frameLen orig) ∧
        u.reg 14 = buf + 1 ∧ src < frameLen orig ∧ dst ≤ src ∧ L.length = orig.length ∧
        L.drop dst = orig.drop dst ∧
        decodeFrame (orig.take (frameLen orig)) =
          prepend (L.take dst) (decodeFrame ((orig.take (frameLen orig)).drop src)))
      measure (fun u => 2 * (frameLen orig - (u.reg 15).toNat) + 1)
    loop_inv 0x11208 (fun u => ∃ p cnt dst L c e, u.reg 15 = buf + BitVec.ofNat 64 p ∧
        u.reg 5 = BitVec.ofNat 64 cnt ∧ u.reg 12 = BitVec.ofNat 64 dst ∧
        readBytes u.mem buf orig.length = L ∧ u.reg 16 = BitVec.ofNat 64 c ∧
        u.reg 17 = BitVec.ofNat 64 e ∧
        u.reg 10 = r ∧ u.reg 11 = buf ∧ u.reg 13 = BitVec.ofNat 64 (frameLen orig) ∧
        u.reg 14 = buf + 1 ∧ p + cnt = e ∧ 0 < cnt ∧ e ≤ frameLen orig ∧ dst < p ∧ c < 256 ∧
        L.length = orig.length ∧ L.drop dst = orig.drop dst ∧
        decodeFrame (orig.take (frameLen orig)) =
          prepend (L.take dst ++ (orig.drop p).take cnt ++ zeroAfter c e (frameLen orig))
            (decodeFrame ((orig.take (frameLen orig)).drop e)))
      measure (fun u => 2 * (frameLen orig - ((u.reg 15) - buf).toNat))
  all_goals trace_state
  all_goals sorry
