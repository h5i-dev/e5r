import Projects.thermostat.ZeroEntry
import Projects.thermostat.ZeroExit
namespace E5R.Thermostat.ZeroMemset
open E5R E5R.Thermostat

/-- Actual memset specialized to the aligned zero buffers used by main.
    No initial bytes are assumed; the end pointer must not wrap. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (n : Nat)
    (hp : c.pc = 0x80005638#32) (h10 : c.get 10 = p) (h11 : c.get 11 = 0#32)
    (h12 : c.get 12 = BitVec.ofNat 32 (4*n)) (hn : 4 ≤ n)
    (ha : p.toNat%4 = 0) (hm : Memory.Block B p (4*n)) (htop : p.toNat+4*n < 2^32) :
    ∃ d, DetSteps B img (19+3*n) ⟨c,ram⟩ ⟨d,WordZero.writes ram p n⟩ ∧
      d.pc = c.get 1 &&& ~~~1#32 ∧ d.sameCsr c ∧
      (∀ r : Reg, r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → d.get r = c.get r) ∧
      (∀ i : Fin (4*n), WordZero.writes ram p n (p+BitVec.ofNat 32 i.val) = 0#8) ∧
      (∀ x, (∀ i : Fin (4*n), x ≠ p+BitVec.ofNat 32 i.val) → WordZero.writes ram p n x = ram x) := by
  have hentry := ZeroEntry.contract B c ram p n hp h10 h11 h12 hn ha htop
  obtain ⟨hpcE,h12E,h13E,h14E,h15E,hregsE,hcsrE⟩ := ZeroEntry.fields c p n
  obtain ⟨cl,hloop,hpcL,h14L,hregsL,hcsrL⟩ := WordZero.loop B (ZeroEntry.setup c p n) ram p n
    (by omega) hpcE h14E h13E h15E ha hm htop
  have h12L : cl.get 12 = BitVec.ofNat 32 (4*n) := (hregsL 12 (by decide)).trans h12E
  have h13L : cl.get 13 = p+BitVec.ofNat 32 (4*n) := (hregsL 13 (by decide)).trans h13E
  have hexit := ZeroExit.contract B cl (WordZero.writes ram p n) (p+BitVec.ofNat 32 (4*n)) n hpcL h12L h13L (by omega)
  obtain ⟨hpcR,hregsR,hcsrR⟩ := ZeroExit.fields cl (p+BitVec.ofNat 32 (4*n))
  refine ⟨ZeroExit.finish cl (p+BitVec.ofNat 32 (4*n)),?_,?_,hcsrR.trans (hcsrL.trans hcsrE),?_,
    WordZero.zero_bytes ram p n htop,WordZero.frame ram p n⟩
  · have hr := (hentry.trans hloop).trans hexit
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr
  · rw [hpcR,hregsL 1 (by decide),hregsE 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  · intro r h12' h13' h14' h15' h16'
    exact (hregsR r h12' h14').trans ((hregsL r h14').trans (hregsE r h12' h13' h14' h15' h16'))
end E5R.Thermostat.ZeroMemset
