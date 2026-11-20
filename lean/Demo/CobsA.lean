import Demo.CobsSpec
import Demo.Cobs.ImageA

namespace Demo.Cobs
open NoCompiler Demo.Cobs.ImageA

set_option maxHeartbeats 20000000 in
/-- `cobs_decode` as plain clang -O2 -march=rv64gc compiled it (demo/elf/cobs.a.elf).
    No block/loop tree: the cut points are read off the control-flow graph by
    hand. The decode loop is entered by a jump into its middle (0x111b8), past
    its exit test at 0x111b4; the cut point is 0x111b8, which every trip
    around the loop passes, with the copy loop's 0x111d8 and the scan's 0x11194. -/
theorem cobs_a : VerifiedC code cobs_decode_dom cobs_decode_entry spec := by
  rintro ⟨r, buf, orig⟩ s he ⟨ha0, ha1, ha2, hlen, hmem, hal, hdis⟩
  have hfl := frameLen_le orig
  nocompiler_auto_c cobs_decode_entry cobs_decode_size s he
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
  -- The verification conditions, by path (pure facts about the specification).
  case entry_ret_0x11216_0 | entry_ret_0x11216_1 | entry_ret_0x11216_2 | entry_ret_0x11216_3 =>
    rw [report_empty (by omega)] <;> first | rfl | trivial
  case «0x11194_to_0x111b8_0» =>
    exact (frameLen_eq_of_zero orig k h2 (BitVec.eq_of_toNat_eq ‹_ = 0›) h3).symm
  case «0x11194_to_0x111b8_1» | «0x11194_to_0x111b8_b_2» => simp [prepend]
  case «0x11194_ret_0x11226_0» | «0x11194_ret_0x11226_1» | «0x11194_ret_0x11226_2» |
      «0x11194_ret_0x11226_3» =>
    have hn : frameLen orig = 0 := by
      have := frameLen_eq_of_zero orig k h2 (BitVec.eq_of_toNat_eq ‹_ = 0›) h3; omega
    have := report_of (orig := orig) (by omega)
      (show decodeFrame (orig.take (frameLen orig)) = (true, []) by rw [hn]; simp [decodeFrame])
    simp [this, hn]
  case «0x11194_to_0x11194» => exact succ_le_frameLen orig k h2 (fun h => ‹¬(orig.getD k _).toNat = 0› (by rw [h]; rfl)) h3
  case «0x11194_to_0x111b8_b_0» | «0x11194_to_0x111b8_b_1» =>
    have := succ_le_frameLen orig k h2 (fun h => ‹¬(orig.getD k _).toNat = 0› (by rw [h]; rfl)) h3; omega
  case «0x111b8_ret_0x11230_0» | «0x111b8_ret_0x11230_1» | «0x111b8_ret_0x11230_2» |
      «0x111b8_ret_0x11230_3» =>
    have hr := report_of (orig := orig) (by omega)
      (by rw [inv_block h8 h9 h11 h12, ite_eq_left (by omega)])
    have hd : (L.take dst).length = dst := by simp; omega
    simp [hr, hd, prepend, take_append_drop_of h11]
  case «0x111b8_to_0x111d8» => rw [inv_block h8 h9 h11 h12, ite_eq_right (by omega), Nat.add_comm 1 src]
  case «0x111b8_ret_0x11226_0» | «0x111b8_ret_0x11226_1» | «0x111b8_ret_0x11226_2» |
      «0x111b8_ret_0x11226_3» =>
    have hc := code_pos h8 h9 h11
    have hdec : decodeFrame (orig.take (frameLen orig)) = (true, L.take dst) := by
      rw [inv_block h8 h9 h11 h12, ite_eq_right (by omega), show (L.getD src 0).toNat = 1 by omega,
        List.drop_eq_nil_of_le (as := orig.take (frameLen orig)) (by simp; omega)]
      simp [zeroAfter, prepend, decodeFrame]; (try omega)
    have hd : (L.take dst).length = dst := by simp; omega
    simp [report_of (orig := orig) (by omega) hdec, hd, take_append_drop_of h11,
      show frameLen orig = src + 1 by omega]
  case «0x111b8_to_0x111b8_0» => rw [drop_set_succ]; exact drop_succ_of_drop h11
  case «0x111b8_to_0x111b8_1» =>
    have hc := code_pos h8 h9 h11
    rw [inv_block h8 h9 h11 h12, ite_eq_right (by omega), show (L.getD src 0).toNat = 1 by omega,
      take_set_succ _ _ _ (by omega)]
    simp [zeroAfter, prepend, show src + 1 < frameLen orig by omega]
  case «0x111d8_to_0x111d8_0» | «0x111d8_to_0x111b8_0» => rw [drop_set_succ]; exact drop_succ_of_drop h17
  case «0x111d8_to_0x111d8_1» =>
    rw [h18, take_set_succ _ _ _ (by omega), take_drop_succ orig p cnt (by omega) h12,
      getD_of_drop_eq h17 (by omega)]
    simp [prepend]
  case «0x111d8_to_0x111b8_1» =>
    rw [h18, take_set_succ _ _ _ (by omega), take_drop_succ orig p cnt (by omega) h12,
      getD_of_drop_eq h17 (by omega), show cnt - 1 = 0 by omega,
      show zeroAfter c e (frameLen orig) = [] by simp [zeroAfter]; omega]
    simp [prepend, show e = p + 1 by omega]
  case «0x111d8_ret_0x11226_0» | «0x111d8_ret_0x11226_1» | «0x111d8_ret_0x11226_2» |
      «0x111d8_ret_0x11226_3» =>
    have hdec : decodeFrame (orig.take (frameLen orig)) =
        (true, (L.set dst (L.getD p 0)).take (dst + 1)) := by
      rw [h18, take_set_succ _ _ _ (by omega), take_drop_succ orig p cnt (by omega) h12,
        getD_of_drop_eq h17 (by omega), show cnt - 1 = 0 by omega,
        show zeroAfter c e (frameLen orig) = [] by simp [zeroAfter]; omega,
        List.drop_eq_nil_of_le (as := orig.take (frameLen orig)) (by simp; omega)]
      simp [prepend, decodeFrame]
    have hd : ((L.set dst (L.getD p 0)).take (dst + 1)).length = dst + 1 := by simp; omega
    have hL' := drop_set_succ L dst (L.getD p 0) ▸ drop_succ_of_drop h17
    rw [report_of (orig := orig) (by omega) hdec]
    first | (simp only [hd, take_append_drop_of hL']; done) | simp [show frameLen orig = e by omega]
  case «0x111d8_to_0x111b8_b_0» =>
    rw [drop_set_succ]
    exact drop_succ_of_drop (drop_set_succ L dst _ ▸ drop_succ_of_drop h17)
  case «0x111d8_to_0x111b8_b_1» =>
    rw [h18, take_set_succ _ _ _ (by simp; omega), take_set_succ _ _ _ (by omega),
      take_drop_succ orig p cnt (by omega) h12, getD_of_drop_eq h17 (by omega),
      show cnt - 1 = 0 by omega, show zeroAfter c e (frameLen orig) = [0] by simp [zeroAfter]; omega]
    simp [prepend, show e = p + 1 by omega]
