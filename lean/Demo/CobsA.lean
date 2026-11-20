import Demo.CobsSpec
import Demo.Cobs.ImageA

namespace Demo.Cobs
open NoCompiler NoCompiler.Vocab Demo.Cobs.ImageA

set_option maxHeartbeats 20000000 in
/-- `cobs_decode` as plain clang -O2 -march=rv64gc compiled it (examples/demo/elf/cobs.a.elf).
    No block/loop tree: the cut points are read off the control-flow graph by
    hand. The decode loop is entered by a jump into its middle (0x111b8), past
    its exit test at 0x111b4; the cut point is 0x111b8, which every trip
    around the loop passes, with the copy loop's 0x111d8 and the scan's 0x11194. -/
theorem cobs_a : VerifiedC code cobs_decode_dom cobs_decode_entry spec := by
  rintro ⟨r, buf, orig⟩ s he ⟨ha0, ha1, ha2, hlen, hmem, hal, hdis⟩
  have hfl : frameLen orig ≤ orig.length := List.findIdx_le_length
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
  case entry_ret_x86_0 | entry_ret_x86_1 | entry_ret_x86_2 | entry_ret_x86_3 =>
    rw [report_empty (by omega)] <;> first | rfl | trivial
  case x4_to_x28_0 =>
    exact (findIdx_eq_of_getD 0 h2 ((byte_beq_zero_iff _).2 ‹_ = 0›) h3).symm
  case x4_to_x28_1 | x4_to_x28_b_2 => simp [prepend]
  case x4_ret_x96_0 | x4_ret_x96_1 | x4_ret_x96_2 |
      x4_ret_x96_3 =>
    have hn : frameLen orig = 0 := by
      have : frameLen orig = k := findIdx_eq_of_getD 0 h2 ((byte_beq_zero_iff _).2 ‹_ = 0›) h3; omega
    have := report_of (orig := orig) (by omega)
      (show decodeFrame (orig.take (frameLen orig)) = (true, []) by rw [hn]; simp [decodeFrame])
    simp [this, hn]
  case x4_to_x4 => exact succ_le_findIdx_of_getD 0 h2 ((byte_beq_zero_false _).2 ‹_›) h3
  case x4_to_x28_b_0 | x4_to_x28_b_1 =>
    have : k + 1 ≤ frameLen orig := succ_le_findIdx_of_getD 0 h2 ((byte_beq_zero_false _).2 ‹_›) h3; omega
  case x28_ret_xa0_0 | x28_ret_xa0_1 | x28_ret_xa0_2 |
      x28_ret_xa0_3 =>
    have hr := report_of (orig := orig) (by omega)
      (by rw [inv_block h8 h9 h11 h12, ite_eq_left (by omega)])
    have hd : (L.take dst).length = dst := by simp; omega
    simp [hr, hd, prepend, take_append_drop_of h11]
  case x28_to_x48 => rw [inv_block h8 h9 h11 h12, ite_eq_right (by omega), Nat.add_comm 1 src]
  case x28_ret_x96_0 | x28_ret_x96_1 | x28_ret_x96_2 |
      x28_ret_x96_3 =>
    have hc := code_pos h8 h9 h11
    have hdec : decodeFrame (orig.take (frameLen orig)) = (true, L.take dst) := by
      rw [inv_block h8 h9 h11 h12, ite_eq_right (by omega), show (L.getD src 0).toNat = 1 by omega,
        List.drop_eq_nil_of_le (as := orig.take (frameLen orig)) (by simp; omega)]
      simp [zeroAfter, prepend, decodeFrame]; (try omega)
    have hd : (L.take dst).length = dst := by simp; omega
    simp [report_of (orig := orig) (by omega) hdec, hd, take_append_drop_of h11,
      show frameLen orig = src + 1 by omega]
  case x28_to_x28_0 => exact drop_set_of_drop _ h11
  case x28_to_x28_1 =>
    have hc := code_pos h8 h9 h11
    rw [inv_block h8 h9 h11 h12, ite_eq_right (by omega), show (L.getD src 0).toNat = 1 by omega,
      take_set_succ _ _ _ (by omega)]
    simp [zeroAfter, prepend, show src + 1 < frameLen orig by omega]
  case x48_to_x48_0 | x48_to_x28_0 => exact drop_set_of_drop _ h17
  case x48_to_x48_1 =>
    rw [h18, take_set_succ _ _ _ (by omega), take_drop_succ (d := 0) orig p cnt (by omega) h12,
      getD_of_drop_eq h17 (by omega)]
    simp [prepend]
  case x48_to_x28_1 =>
    rw [h18, take_set_succ _ _ _ (by omega), take_drop_succ (d := 0) orig p cnt (by omega) h12,
      getD_of_drop_eq h17 (by omega), show cnt - 1 = 0 by omega,
      show zeroAfter c e (frameLen orig) = [] by simp [zeroAfter]; omega]
    simp [prepend, show e = p + 1 by omega]
  case x48_ret_x96_0 | x48_ret_x96_1 | x48_ret_x96_2 |
      x48_ret_x96_3 =>
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
  case x48_to_x28_b_0 =>
    exact drop_set_of_drop _ (drop_set_of_drop _ h17)
  case x48_to_x28_b_1 =>
    rw [h18, take_set_succ _ _ _ (by simp; omega), take_set_succ _ _ _ (by omega),
      take_drop_succ (d := 0) orig p cnt (by omega) h12, getD_of_drop_eq h17 (by omega),
      show cnt - 1 = 0 by omega, show zeroAfter c e (frameLen orig) = [0] by simp [zeroAfter]; omega]
    simp [prepend, show e = p + 1 by omega]
