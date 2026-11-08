-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ModeFour
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.EqualLiteralQuiet
import Projects.thermostat.LetterBranchQuiet
import Projects.thermostat.ModeFinishQuiet
import Projects.thermostat.ModeSuffixQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.ModeFour
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (b : BitVec 8) (bs : List (BitVec 8))
    (hs : Bytes.Span B ram p (b::bs)) (hl : bs.length = 3) (hp : c.pc = 0x8000221c#32)
    (h8 : c.get 8 = p) (htag : c.get 10 = 255#32) (hstatus : c.get 11 = 400#32) :
    ∃ d n, n ≤ 20 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (ModeSpec.value (b::bs)) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨c1,t1,pc1,v1,k1,regs1,csr1⟩ := E5R.Thermostat.Literal.compare_equal_quiet B img 97#8 b BodySites.auto_first c ram p hp (by simp only [BodySites.auto_first,h8,BitVec.add_zero]) (Bytes.head hs).2 (Bytes.head hs).1
  have p8 : c1.get 8 = p := (regs1 8 (by decide) (by decide)).trans h8
  have tag1 : c1.get 10 = 255#32 := (regs1 10 (by decide) (by decide)).trans htag
  have status1 : c1.get 11 = 400#32 := (regs1 11 (by decide) (by decide)).trans hstatus
  by_cases ha : b = 97#8
  · have pc1' : c1.pc = 0x8000225c#32 := by simpa only [ite_eq_left ha,BodySites.auto_first] using pc1
    obtain ⟨d,n,hn,ht,hpc,hval,hregs,hcsr⟩ := E5R.Thermostat.ModeSuffix.auto_quiet B c1 ram p bs (Bytes.tail hs) hl pc1' p8 tag1 status1
    refine ⟨d,3+n,by omega,t1.trans ht,hpc,?_,?_,hcsr.trans csr1⟩
    · rw [ha,ModeSpec.auto_first];exact hval
    · intro r h1 h2 h3 h4;rw [hregs r h1 h2 h3 h4,regs1 r h3 h4]
  · have pc1' : c1.pc = 0x80002228#32 := by simpa only [ite_eq_right ha,BodySites.auto_first] using pc1
    obtain ⟨c2,t2,pc2,regs2,csr2⟩ := E5R.Thermostat.LetterBranch.contract_quiet B c1 ram 104#8 b BodySites.mode_heat pc1' v1
    have p8' : c2.get 8 = p := (regs2 8 (by decide)).trans p8
    have tag2 : c2.get 10 = 255#32 := (regs2 10 (by decide)).trans tag1
    have status2 : c2.get 11 = 400#32 := (regs2 11 (by decide)).trans status1
    by_cases hh : b = 104#8
    · have pc2' : c2.pc = 0x80002230#32 := by simpa only [ite_eq_left hh,BodySites.mode_heat] using pc2
      obtain ⟨d,n,hn,ht,hpc,hval,hregs,hcsr⟩ := E5R.Thermostat.ModeSuffix.heat_quiet B c2 ram p bs (Bytes.tail hs) hl pc2' p8' tag2 status2
      refine ⟨d,3+(2+n),by omega,t1.trans (t2.trans ht),hpc,?_,?_,(hcsr.trans csr2).trans csr1⟩
      · rw [hh,ModeSpec.heat_first];exact hval
      · intro r h1 h2 h3 h4;rw [hregs r h1 h2 h3 h4,regs2 r h4,regs1 r h3 h4]
    · have pc2' : c2.pc = 0x8000220a#32 := by simpa only [ite_eq_right hh,BodySites.mode_heat] using pc2
      obtain ⟨d,ht,hpc,hval,hregs,hcsr⟩ := E5R.Thermostat.ModeFinish.error_quiet B c2 ram pc2' tag2 status2
      refine ⟨d,9,by omega,t1.trans (t2.trans ht),hpc,?_,?_,(hcsr.trans csr2).trans csr1⟩
      · rw [ModeSpec.other_four b bs hl ha hh];exact hval
      · intro r h1 h2 h3 h4;rw [hregs r h1 h2 h3,regs2 r h4,regs1 r h3 h4]

end E5R.Thermostat.ModeFour
