import Projects.thermostat.RelayOffTail
import Projects.thermostat.RelaySites
import Projects.thermostat.RelaySpec
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.RelayOff
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p idx : Word) (a b z : BitVec 8)
    (hi : idx.toNat < 256) (h12 : c.get 12 = idx)
    (hs : Bytes.Span B ram p [a,b,z]) (hp : c.pc = 0x800021de#32) (h8 : c.get 8 = p)
    (htag : c.get 10 = 255#32) (hstatus : c.get 11 = 400#32) :
    ∃ d n, n ≤ 16 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (RelaySpec.body idx [a,b,z]) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → d.get r = c.get r) ∧ d.sameCsr c := by
  have spec := RelaySpec.three idx a b z
  obtain ⟨c1,t1,pc1,v1,k1,regs1,csr1⟩ := Literal.compare B img 111#8 a RelaySites.off0 c ram p hp (by simp only [RelaySites.off0,h8,BitVec.add_zero]) (Bytes.head hs).2 (Bytes.head hs).1
  by_cases ha : a = 111#8
  · have pc1' : c1.pc = 0x800021ea#32 := by simpa only [ite_eq_left ha,RelaySites.off0] using pc1
    have h8' : c1.get 8 = p := (regs1 8 (by decide) (by decide)).trans h8
    have hm := hs.memory ⟨1,by change 1 < 3;decide⟩
    have hb := hs.bytes ⟨1,by change 1 < 3;decide⟩
    obtain ⟨c2,t2,pc2,v2,k2,regs2,csr2⟩ := Literal.compare B img 102#8 b RelaySites.off1 c1 ram (p+1#32) pc1' (by simpa only [RelaySites.off1,h8']) hm hb
    by_cases hb' : b = 102#8
    · have pc2' : c2.pc = 0x800021f6#32 := by simpa only [ite_eq_left hb',RelaySites.off1] using pc2
      have h8'' : c2.get 8 = p := (regs2 8 (by decide) (by decide)).trans h8'
      have status2 : c2.get 11 = 400#32 := (regs2 11 (by decide) (by decide)).trans ((regs1 11 (by decide) (by decide)).trans hstatus)
      obtain ⟨d,n,hn,ht,hpc,hval,hregs,hcsr⟩ := RelayOffTail.contract B c2 ram p idx z pc2' h8'' k2 hi
        ((regs2 12 (by decide) (by decide)).trans ((regs1 12 (by decide) (by decide)).trans h12))
        ((regs2 10 (by decide) (by decide)).trans ((regs1 10 (by decide) (by decide)).trans htag)) status2 (hs.memory ⟨2,by change 2 < 3;decide⟩) (hs.bytes ⟨2,by change 2 < 3;decide⟩)
      refine ⟨d,3+(3+n),by omega,t1.trans (t2.trans ht),hpc,?_,?_,(hcsr.trans csr2).trans csr1⟩
      · rw [spec];simpa only [ha,hb',true_and] using hval
      · intro r h1 h2 h3 h4 h5 h6
        rw [hregs r h1 h2 h3 h4 h6,regs2 r h4 h5,regs1 r h4 h5]
    · have pc2' : c2.pc = 0x8000220a#32 := by simpa only [ite_eq_right hb',RelaySites.off1] using pc2
      have tag2 : c2.get 10 = 255#32 := (regs2 10 (by decide) (by decide)).trans ((regs1 10 (by decide) (by decide)).trans htag)
      have status2 : c2.get 11 = 400#32 := (regs2 11 (by decide) (by decide)).trans ((regs1 11 (by decide) (by decide)).trans hstatus)
      obtain ⟨d,ht,hpc,hval,hregs,hcsr⟩ := ModeFinish.error B c2 ram pc2' tag2 status2
      refine ⟨d,10,by omega,t1.trans (t2.trans ht),hpc,?_,?_,(hcsr.trans csr2).trans csr1⟩
      · rw [spec];simpa only [hb',and_false,false_and,ite_false] using hval
      · intro r h1 h2 h3 h4 h5 h6
        rw [hregs r h1 h2 h3,regs2 r h4 h5,regs1 r h4 h5]
  · have pc1' : c1.pc = 0x8000220a#32 := by simpa only [ite_eq_right ha,RelaySites.off0] using pc1
    obtain ⟨d,ht,hpc,hval,hregs,hcsr⟩ := ModeFinish.error B c1 ram pc1' ((regs1 10 (by decide) (by decide)).trans htag) ((regs1 11 (by decide) (by decide)).trans hstatus)
    refine ⟨d,7,by omega,t1.trans ht,hpc,?_,?_,hcsr.trans csr1⟩
    · rw [spec];simpa only [ha,false_and,ite_false] using hval
    · intro r h1 h2 h3 h4 h5 h6
      rw [hregs r h1 h2 h3,regs1 r h4 h5]
end E5R.Thermostat.RelayOff
