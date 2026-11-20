import Demo.CobsSpec
import Demo.Cobs.ImageB

namespace Demo.Cobs
open NoCompiler NoCompiler.Vocab Demo.Cobs.ImageB

set_option maxHeartbeats 20000000 in
theorem cobs_b : VerifiedImg code cobs_decode_dom cobs_decode_entry spec := by
  rintro ⟨r, buf, orig⟩ s he ⟨ha0, ha1, ha2, hlen, hmem, hal, hdis⟩
  have hfl : frameLen orig ≤ orig.length := List.findIdx_le_length
  nocompiler_auto cobs_decode_func s he
    loop_inv $l2 (fun u => ∃ k, u.reg 13 = BitVec.ofNat 64 k ∧ k < orig.length ∧ k ≤ frameLen orig ∧
        u.reg 10 = r ∧ u.reg 11 = buf ∧ u.reg 12 = BitVec.ofNat 64 orig.length ∧ u.mem = s.mem)
      measure (fun u => 3 * orig.length + 3 - (u.reg 13).toNat)
    loop_inv $l5 (fun u => ∃ src dst L, u.reg 15 = BitVec.ofNat 64 src ∧
        u.reg 12 = BitVec.ofNat 64 dst ∧ readBytes u.mem buf orig.length = L ∧
        u.reg 10 = r ∧ u.reg 11 = buf ∧ u.reg 13 = BitVec.ofNat 64 (frameLen orig) ∧
        u.reg 14 = buf + 1 ∧ src < frameLen orig ∧ dst ≤ src ∧ L.length = orig.length ∧
        L.drop dst = orig.drop dst ∧
        decodeFrame (orig.take (frameLen orig)) =
          prepend (L.take dst) (decodeFrame ((orig.take (frameLen orig)).drop src)))
      measure (fun u => 2 * (frameLen orig - (u.reg 15).toNat) + 1)
    loop_inv $l9 (fun u => ∃ p cnt dst L c e, u.reg 15 = buf + BitVec.ofNat 64 p ∧
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
  -- The verification conditions, by path (pure facts about the specification).
  case entry_ret_xd8_0 | entry_ret_xd8_1 | entry_ret_xd8_2 | entry_ret_xd8_3 =>
    rw [report_empty (by omega)] <;> first | rfl | trivial
  case l2_to_l5_0 =>
    exact (findIdx_eq_of_getD 0 h2 ((byte_beq_zero_iff _).2 ‹_ = 0›) h3).symm
  case l2_to_l5_1 | l2_to_l5_b_2 => simp [prepend]
  case l2_ret_xc8_0 | l2_ret_xc8_1 | l2_ret_xc8_2 |
      l2_ret_xc8_3 =>
    have hn : frameLen orig = 0 := by
      have : frameLen orig = k := findIdx_eq_of_getD 0 h2 ((byte_beq_zero_iff _).2 ‹_ = 0›) h3; omega
    have := report_of (orig := orig) (by omega)
      (show decodeFrame (orig.take (frameLen orig)) = (true, []) by rw [hn]; simp [decodeFrame])
    simp [this, hn]
  case l2_to_l2 => exact succ_le_findIdx_of_getD 0 h2 ((byte_beq_zero_false _).2 ‹_›) h3
  case l2_to_l5_b_0 | l2_to_l5_b_1 =>
    have : k + 1 ≤ frameLen orig := succ_le_findIdx_of_getD 0 h2 ((byte_beq_zero_false _).2 ‹_›) h3; omega
  case l5_ret_x6c_0 | l5_ret_x6c_1 | l5_ret_x6c_2 |
      l5_ret_x6c_3 =>
    have hr := report_of (orig := orig) (by omega)
      (by rw [inv_block h8 h9 h11 h12, ite_eq_left (by omega)])
    have hd : (L.take dst).length = dst := by simp; omega
    simp [hr, hd, prepend, take_append_drop_of h11]
  case l5_to_l9 => rw [inv_block h8 h9 h11 h12, ite_eq_right (by omega), Nat.add_comm 1 src]
  case l5_ret_xc8_0 | l5_ret_xc8_1 | l5_ret_xc8_2 |
      l5_ret_xc8_3 =>
    have hc := code_pos h8 h9 h11
    have hdec : decodeFrame (orig.take (frameLen orig)) = (true, L.take dst) := by
      rw [inv_block h8 h9 h11 h12, ite_eq_right (by omega), show (L.getD src 0).toNat = 1 by omega,
        List.drop_eq_nil_of_le (as := orig.take (frameLen orig)) (by simp; omega)]
      simp [zeroAfter, prepend, decodeFrame]; (try omega)
    have hd : (L.take dst).length = dst := by simp; omega
    simp [report_of (orig := orig) (by omega) hdec, hd, take_append_drop_of h11,
      show frameLen orig = src + 1 by omega]
  case l5_to_l5_0 => exact drop_set_of_drop _ h11
  case l5_to_l5_1 =>
    have hc := code_pos h8 h9 h11
    rw [inv_block h8 h9 h11 h12, ite_eq_right (by omega), show (L.getD src 0).toNat = 1 by omega,
      take_set_succ _ _ _ (by omega)]
    simp [zeroAfter, prepend, show src + 1 < frameLen orig by omega]
  case l9_to_l9_0 | l9_to_l5_0 => exact drop_set_of_drop _ h17
  case l9_to_l9_1 =>
    rw [h18, take_set_succ _ _ _ (by omega), take_drop_succ (d := 0) orig p cnt (by omega) h12,
      getD_of_drop_eq h17 (by omega)]
    simp [prepend]
  case l9_to_l5_1 =>
    rw [h18, take_set_succ _ _ _ (by omega), take_drop_succ (d := 0) orig p cnt (by omega) h12,
      getD_of_drop_eq h17 (by omega), show cnt - 1 = 0 by omega,
      show zeroAfter c e (frameLen orig) = [] by simp [zeroAfter]; omega]
    simp [prepend, show e = p + 1 by omega]
  case l9_ret_xc8_0 | l9_ret_xc8_1 | l9_ret_xc8_2 |
      l9_ret_xc8_3 =>
    have hdec : decodeFrame (orig.take (frameLen orig)) =
        (true, (L.set dst (L.getD p 0)).take (dst + 1)) := by
      rw [h18, take_set_succ _ _ _ (by omega), take_drop_succ (d := 0) orig p cnt (by omega) h12,
        getD_of_drop_eq h17 (by omega), show cnt - 1 = 0 by omega,
        show zeroAfter c e (frameLen orig) = [] by simp [zeroAfter]; omega,
        List.drop_eq_nil_of_le (as := orig.take (frameLen orig)) (by simp; omega)]
      simp [prepend, decodeFrame]
    have hd : ((L.set dst (L.getD p 0)).take (dst + 1)).length = dst + 1 := by simp; omega
    have hL' := drop_set_of_drop (L.getD p 0) h17
    rw [report_of (orig := orig) (by omega) hdec]
    first | (simp only [hd, take_append_drop_of hL']; done) | simp [show frameLen orig = e by omega]
  case l9_to_l5_b_0 =>
    exact drop_set_of_drop _ (drop_set_of_drop _ h17)
  case l9_to_l5_b_1 =>
    rw [h18, take_set_succ _ _ _ (by simp; omega), take_set_succ _ _ _ (by omega),
      take_drop_succ (d := 0) orig p cnt (by omega) h12, getD_of_drop_eq h17 (by omega),
      show cnt - 1 = 0 by omega, show zeroAfter c e (frameLen orig) = [0] by simp [zeroAfter]; omega]
    simp [prepend, show e = p + 1 by omega]
