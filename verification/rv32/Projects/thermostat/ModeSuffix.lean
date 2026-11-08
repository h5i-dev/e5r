import Projects.thermostat.BodySuffix
import Projects.thermostat.ModeFinish
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ModeSuffix
open E5R E5R.Thermostat

theorem heat (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (hs : Bytes.Span B ram (p+1#32) xs) (hl : xs.length = 3) (hp : c.pc = 0x80002230#32)
    (h8 : c.get 8 = p) (htag : c.get 10 = 255#32) (hstatus : c.get 11 = 400#32) :
    ∃ d n, n ≤ 15 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (if xs = WireSpec.ascii "eat" then .ok (.mode .heat) else .error 400) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨c1,n,hn,ht,hpc,hregs,hcsr⟩ := BodySuffix.heat B c ram p xs hs hl hp h8
  by_cases he : xs = WireSpec.ascii "eat"
  · have hp1 : c1.pc = 0x80002254#32 := by simpa only [ite_eq_left he] using hpc
    obtain ⟨d,td,pcd,vald,regd,csrd⟩ := ModeFinish.heat B c1 ram hp1
    refine ⟨d,n+6,by omega,ht.trans td,pcd,by simpa only [ite_eq_left he] using vald,?_,csrd.trans hcsr⟩
    intro r h1 h2 h3 h4;rw [regd r h1 h2 h3,hregs r h3 h4]
  · have hp1 : c1.pc = 0x8000220a#32 := by simpa only [ite_eq_right he] using hpc
    obtain ⟨d,td,pcd,vald,regd,csrd⟩ := ModeFinish.error B c1 ram hp1 ((hregs 10 (by decide) (by decide)).trans htag) ((hregs 11 (by decide) (by decide)).trans hstatus)
    refine ⟨d,n+4,by omega,ht.trans td,pcd,by simpa only [ite_eq_right he] using vald,?_,csrd.trans hcsr⟩
    intro r h1 h2 h3 h4;rw [regd r h1 h2 h3,hregs r h3 h4]

theorem auto (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (hs : Bytes.Span B ram (p+1#32) xs) (hl : xs.length = 3) (hp : c.pc = 0x8000225c#32)
    (h8 : c.get 8 = p) (htag : c.get 10 = 255#32) (hstatus : c.get 11 = 400#32) :
    ∃ d n, n ≤ 15 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (if xs = WireSpec.ascii "uto" then .ok (.mode .auto) else .error 400) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨c1,n,hn,ht,hpc,hregs,hcsr⟩ := BodySuffix.auto B c ram p xs hs hl hp h8
  by_cases he : xs = WireSpec.ascii "uto"
  · have hp1 : c1.pc = 0x80002280#32 := by simpa only [ite_eq_left he] using hpc
    obtain ⟨d,td,pcd,vald,regd,csrd⟩ := ModeFinish.auto B c1 ram hp1
    refine ⟨d,n+6,by omega,ht.trans td,pcd,by simpa only [ite_eq_left he] using vald,?_,csrd.trans hcsr⟩
    intro r h1 h2 h3 h4;rw [regd r h1 h2 h3,hregs r h3 h4]
  · have hp1 : c1.pc = 0x8000220a#32 := by simpa only [ite_eq_right he] using hpc
    obtain ⟨d,td,pcd,vald,regd,csrd⟩ := ModeFinish.error B c1 ram hp1 ((hregs 10 (by decide) (by decide)).trans htag) ((hregs 11 (by decide) (by decide)).trans hstatus)
    refine ⟨d,n+4,by omega,ht.trans td,pcd,by simpa only [ite_eq_right he] using vald,?_,csrd.trans hcsr⟩
    intro r h1 h2 h3 h4;rw [regd r h1 h2 h3,hregs r h3 h4]
end E5R.Thermostat.ModeSuffix
