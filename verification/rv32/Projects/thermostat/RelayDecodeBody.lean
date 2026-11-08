import Projects.thermostat.RelayIntro
import Projects.thermostat.RelayOn
import Projects.thermostat.RelayOff
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.RelayDecodeBody
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p idx : Word) (xs : List (BitVec 8))
    (hs : Bytes.Span B ram p xs) (hi : idx.toNat < 256) (hp : c.pc = 0x800021aa#32)
    (h8 : c.get 8 = p) (h9 : c.get 9 = BitVec.ofNat 32 xs.length)
    (h11 : c.get 11 = idx) (htag : c.get 10 = 255#32) :
    ∃ d n, n ≤ 22 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (RelaySpec.body idx xs) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨c1,n,hn,ht,hpc,hidx,hstatus,hregs,hcsr⟩ := RelayIntro.contract B c ram xs.length idx hs.length hp h9 h11
  have p8 : c1.get 8 = p := (hregs 8 (by decide) (by decide) (by decide)).trans h8
  have tag1 : c1.get 10 = 255#32 := (hregs 10 (by decide) (by decide) (by decide)).trans htag
  by_cases h3 : xs.length = 3
  · have hp1 : c1.pc = 0x800021de#32 := by simpa only [ite_eq_left h3] using hpc
    have he := List.eq_getElem_of_length_eq_three xs h3
    obtain ⟨d,k,hk,td,pcd,vd,rd,cd⟩ := RelayOff.contract B c1 ram p idx xs[0] xs[1] xs[2] hi hidx (by rw [←he];exact hs) hp1 p8 tag1 hstatus
    refine ⟨d,n+k,by omega,ht.trans td,pcd,?_,?_,cd.trans hcsr⟩
    · simpa only [←he] using vd
    · intro r h1 h2 h3 h4 h5 h6;rw [rd r h1 h2 h3 h4 h5 h6,hregs r h2 h3 h4]
  · by_cases h2 : xs.length = 2
    · have hp1 : c1.pc = 0x800021bc#32 := by simpa only [ite_eq_right h3,ite_eq_left h2] using hpc
      obtain ⟨d,k,hk,td,pcd,vd,rd,cd⟩ := RelayOn.contract B c1 ram p idx xs hs h2 hi hp1 p8 hidx tag1 hstatus
      refine ⟨d,n+k,by omega,ht.trans td,pcd,vd,?_,cd.trans hcsr⟩
      intro r h1 h2 h3 h4 h5 h6;rw [rd r h1 h2 h3 h4 h5,hregs r h2 h3 h4]
    · have hp1 : c1.pc = 0x8000220a#32 := by simpa only [ite_eq_right h3,ite_eq_right h2] using hpc
      obtain ⟨d,td,pcd,vd,rd,cd⟩ := ModeFinish.error B c1 ram hp1 tag1 hstatus
      refine ⟨d,n+4,by omega,ht.trans td,pcd,?_,?_,cd.trans hcsr⟩
      · rw [RelaySpec.other idx xs h2 h3];exact vd
      · intro r h1 h2 h3 h4 h5 h6;rw [rd r h1 h2 h3,hregs r h2 h3 h4]
end E5R.Thermostat.RelayDecodeBody
