-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.PathFive
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.EqualLiteralQuiet
import Projects.thermostat.LetterBranchQuiet
import Projects.thermostat.LiteralQuiet
import Projects.thermostat.PathLiteralsQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.PathFive
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (a b : BitVec 8) (bs : List (BitVec 8))
    (hs : Bytes.Span B ram p (a::b::bs)) (hl : bs.length = 3)
    (hp : c.pc = 0x800020ae#32) (h11 : c.get 11 = p) :
    ∃ d n, n ≤ 17 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = destination (a::b::bs) ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨c1,t1,pc1,v1,k1,regs1,csr1⟩ := E5R.Thermostat.Literal.compare_quiet B img 47#8 a BodySites.path_slash c ram p hp
    (by simp only [BodySites.path_slash,h11,BitVec.add_zero]) (Bytes.head hs).2 (Bytes.head hs).1
  have p11 : c1.get 11 = p := (regs1 11 (by decide) (by decide)).trans h11
  have hm_ne (h : a ≠ 47#8) : a::b::bs ≠ WireSpec.ascii "/mode" := by intro he;exact h (List.cons.inj he).1
  have ht_ne (h : a ≠ 47#8) : a::b::bs ≠ WireSpec.ascii "/temp" := by intro he;exact h (List.cons.inj he).1
  by_cases ha : a = 47#8
  · have pc1' : c1.pc = 0x800020ba#32 := by simpa only [ite_eq_left ha,BodySites.path_slash] using pc1
    obtain ⟨c2,t2,pc2,v2,k2,regs2,csr2⟩ := E5R.Thermostat.Literal.compare_equal_quiet B img 109#8 b BodySites.path_mode c1 ram (p+1#32) pc1'
      (by simpa only [BodySites.path_mode,p11]) (Bytes.head (Bytes.tail hs)).2 (Bytes.head (Bytes.tail hs)).1
    have p11' : c2.get 11 = p := (regs2 11 (by decide) (by decide)).trans p11
    have suffix : Bytes.Span B ram (p+2#32) bs := by
      simpa using Bytes.drop_span hs 2 (by simp)
    by_cases hb : b = 109#8
    · have pc2' : c2.pc = 0x80002136#32 := by simpa only [ite_eq_left hb,BodySites.path_mode] using pc2
      obtain ⟨d,n,hn,td,pcd,rd,cd⟩ := E5R.Thermostat.PathLiterals.mode_quiet B c2 ram p bs suffix hl pc2' p11'
      refine ⟨d,3+(3+n),by omega,t1.trans (t2.trans td),?_,?_,(cd.trans csr2).trans csr1⟩
      · have he : a::b::bs = WireSpec.ascii "/mode" ↔ bs = WireSpec.ascii "ode" := by
          rw [ha,hb];change 47#8::109#8::bs = 47#8::109#8::WireSpec.ascii "ode" ↔ _;simp
        have ht : a::b::bs ≠ WireSpec.ascii "/temp" := by intro he;have h := (List.cons.inj (List.cons.inj he).2).1;rw [hb] at h;contradiction
        simpa only [destination,he,ite_eq_right ht] using pcd
      · intro r h1 h2 h3;rw [rd r h1 h2 h3,regs2 r h2 h3,regs1 r h2 h3]
    · have pc2' : c2.pc = 0x800020c6#32 := by simpa only [ite_eq_right hb,BodySites.path_mode] using pc2
      obtain ⟨c3,t3,pc3,regs3,csr3⟩ := E5R.Thermostat.LetterBranch.contract_quiet B c2 ram 116#8 b BodySites.path_temp pc2' v2
      have p11'' : c3.get 11 = p := (regs3 11 (by decide)).trans p11'
      have hm : a::b::bs ≠ WireSpec.ascii "/mode" := by intro he;exact hb (List.cons.inj (List.cons.inj he).2).1
      by_cases htemp : b = 116#8
      · have pc3' : c3.pc = 0x800020ce#32 := by simpa only [ite_eq_left htemp,BodySites.path_temp] using pc3
        obtain ⟨d,n,hn,td,pcd,rd,cd⟩ := E5R.Thermostat.PathLiterals.temp_quiet B c3 ram p bs suffix hl pc3' p11''
        refine ⟨d,3+(3+(2+n)),by omega,t1.trans (t2.trans (t3.trans td)),?_,?_,((cd.trans csr3).trans csr2).trans csr1⟩
        · have he : a::b::bs = WireSpec.ascii "/temp" ↔ bs = WireSpec.ascii "emp" := by
            rw [ha,htemp];change 47#8::116#8::bs = 47#8::116#8::WireSpec.ascii "emp" ↔ _;simp
          simpa only [destination,ite_eq_right hm,he] using pcd
        · intro r h1 h2 h3;rw [rd r h1 h2 h3,regs3 r h3,regs2 r h2 h3,regs1 r h2 h3]
      · have ht : a::b::bs ≠ WireSpec.ascii "/temp" := by intro he;exact htemp (List.cons.inj (List.cons.inj he).2).1
        refine ⟨c3,8,by omega,t1.trans (t2.trans t3),?_,?_,(csr3.trans csr2).trans csr1⟩
        · simpa only [destination,ite_eq_right hm,ite_eq_right ht,ite_eq_right htemp,BodySites.path_temp] using pc3
        · intro r h1 h2 h3;rw [regs3 r h3,regs2 r h2 h3,regs1 r h2 h3]
  · refine ⟨c1,3,by omega,t1,?_,?_,csr1⟩
    · simpa only [destination,ite_eq_right (hm_ne ha),ite_eq_right (ht_ne ha),ite_eq_right ha,BodySites.path_slash] using pc1
    · intro r h1 h2 h3;exact regs1 r h2 h3

end E5R.Thermostat.PathFive
