import Projects.thermostat.RelayFinish
import Projects.thermostat.ModeFinish
import Projects.thermostat.RelaySites
import Projects.thermostat.RelaySpec
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.RelayOn
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p idx : Word) (xs : List (BitVec 8))
    (hs : Bytes.Span B ram p xs) (hl : xs.length = 2) (hi : idx.toNat < 256)
    (hp : c.pc = 0x800021bc#32) (h8 : c.get 8 = p) (h12 : c.get 12 = idx)
    (htag : c.get 10 = 255#32) (hstatus : c.get 11 = 400#32) :
    ∃ d n, n ≤ 15 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (RelaySpec.body idx xs) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨c1,n,hn,ht,hpc,hregs,hcsr⟩ := Literal.check RelaySites.on1 RelaySites.on_prefix rfl rfl rfl
    (by decide) (by decide) B ram p xs c (by simpa only [BitVec.add_zero] using hs) hl hp h8
  change n ≤ 6 at hn
  have he : [111#8]++[110#8] = WireSpec.ascii "on" := rfl
  have hpc' : c1.pc = (if xs = WireSpec.ascii "on" then 0x800021d4#32 else 0x8000220a#32) := by
    simpa only [he,RelaySites.on1] using hpc
  have regs1 : ∀ r : Reg, r ≠ 13 → r ≠ 14 → c1.get r = c.get r := by
    intro r h1 h2;exact hregs r h1 h2 h1 h2
  by_cases hx : xs = WireSpec.ascii "on"
  · obtain ⟨d,td,pcd,vd,rd,cd⟩ := RelayFinish.on B c1 ram idx (by simpa only [ite_eq_left hx] using hpc') hi
      ((regs1 12 (by decide) (by decide)).trans h12)
    refine ⟨d,n+9,by omega,ht.trans td,pcd,?_,?_,cd.trans hcsr⟩
    · rw [RelaySpec.two idx xs hl];simpa only [ite_eq_left hx] using vd
    · intro r h1 h2 h3 h4 h5;rw [rd r h1 h2 h3 h4,regs1 r h4 h5]
  · obtain ⟨d,td,pcd,vd,rd,cd⟩ := ModeFinish.error B c1 ram (by simpa only [ite_eq_right hx] using hpc')
      ((regs1 10 (by decide) (by decide)).trans htag) ((regs1 11 (by decide) (by decide)).trans hstatus)
    refine ⟨d,n+4,by omega,ht.trans td,pcd,?_,?_,cd.trans hcsr⟩
    · rw [RelaySpec.two idx xs hl];simpa only [ite_eq_right hx] using vd
    · intro r h1 h2 h3 h4 h5;rw [rd r h1 h2 h3,regs1 r h4 h5]
end E5R.Thermostat.RelayOn
