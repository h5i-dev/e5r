-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.HeaderTry
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.HeaderEntryQuiet
import Projects.thermostat.HeaderNameQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.HeaderTry
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (table p q : Word)
    (raw query : List (BitVec 8)) (e : HeaderSpec.Entry) (hc : HeaderInput.Cell B ram table raw.length e)
    (hraw : Bytes.Span B ram p raw) (hquery : ReadBytes.Span B img ram q query) (hq : query.length = 13)
    (hp : c.pc = 0x800026e8#32) (h16 : c.get 16 = table) (h15 : c.get 15 = p) (h11 : c.get 11 = q)
    (h12 : c.get 12 = BitVec.ofNat 32 raw.length) (h13 : c.get 13 = 13#32) :
    ∃ d n, n ≤ 205 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if HeaderSpec.same (HeaderSpec.name raw e) query then 0x80002738#32 else 0x800026e2#32) ∧
      HeaderName.Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,n,hn,ta,apc,fields,aframe,acsr⟩ := E5R.Thermostat.HeaderEntry.contract_quiet B c ram table p q raw.length e hc hraw.length hp h16 h15 h11 h12 h13
  have hname := HeaderInput.name_length hc.bounds
  by_cases he : e.nameEnd-e.nameStart = 13
  · have apc' : a.pc = 0x80002706#32 := by simpa only [ite_eq_left he] using apc
    obtain ⟨a10,a14,a5⟩ := fields he
    have hnamelen : (HeaderSpec.name raw e).length = 13 := hname.trans he
    have hne : HeaderSpec.name raw e ≠ [] := by intro hz;rw [hz] at hnamelen;contradiction
    obtain ⟨d,k,hk,td,dpc,dframe,dcsr⟩ := E5R.Thermostat.HeaderName.contract_quiet B ram (HeaderSpec.name raw e) query (hnamelen.trans hq.symm) hne
      (p+BitVec.ofNat 32 e.nameStart) q (ReadBytes.of_ram (HeaderInput.name_span hraw hc.bounds)) hquery a apc' a10 a14
      (by simpa only [hnamelen] using a5)
    refine ⟨d,n+k,by rw [hnamelen] at hk;omega,ta.trans td,dpc,?_,dcsr.trans acsr⟩
    intro r h1 h2 h3 h4 h5 h6 h7
    exact (dframe r h1 h2 h3 h4 h5 h6 h7).trans (aframe r h1 h4 h5)
  · have hs : HeaderSpec.same (HeaderSpec.name raw e) query = false := by
      apply decide_eq_false
      intro heq
      have hh := congrArg List.length heq
      simp only [List.length_map,hname,hq] at hh
      exact he hh
    refine ⟨a,n,by omega,ta,?_,?_,acsr⟩
    · simpa only [ite_eq_right he,hs,Bool.false_eq_true,ite_false] using apc
    · intro r h1 h2 h3 h4 h5 h6 h7
      exact aframe r h1 h4 h5

end E5R.Thermostat.HeaderTry
