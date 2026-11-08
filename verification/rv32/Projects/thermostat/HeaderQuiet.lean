-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.Header
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.HeaderCountQuiet
import Projects.thermostat.HeaderNoneQuiet
import Projects.thermostat.HeaderScanQuiet
import Projects.thermostat.HeaderSetupQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.Header
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (req p q : Word)
    (raw query : List (BitVec 8)) (entries : List HeaderSpec.Entry)
    (h : Pre B ram req p raw entries) (hquery : ReadBytes.Span B img ram q query) (hq : query.length = 13)
    (hp : c.pc = 0x800026c0#32) (h10 : c.get 10 = req) (h11 : c.get 11 = q) (h12 : c.get 12 = 13#32) :
    ∃ d n, n ≤ 212*entries.length+13 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = c.get 1 &&& ~~~1 ∧
      HeaderResult.At B ram p raw d (HeaderSpec.find raw query entries) ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,ta,apc,a13,a14,aframe,acsr⟩ := E5R.Thermostat.HeaderCount.contract_quiet B c ram req entries.length h.table.bounded hp h10 h12 h.object h.aligned h.count
  have a1 : a.get 1 = c.get 1 := aframe 1 (by decide) (by decide) (by decide)
  by_cases hz : entries = []
  · subst entries
    have apc' : a.pc = 0x8000274e#32 := by simpa only [List.length_nil,ite_true] using apc
    obtain ⟨d,td,dpc,d10,dframe,dcsr⟩ := E5R.Thermostat.HeaderNone.contract_quiet B a ram apc'
    refine ⟨d,7,by simp,ta.trans td,by rw [dpc,a1],d10,?_,dcsr.trans acsr⟩
    intro r h5 h6 h7 h28 h29 hr
    exact (dframe r (outside r 10 hr (by decide))).trans
      (aframe r (outside r 12 hr (by decide)) (outside r 13 hr (by decide)) (outside r 14 hr (by decide)))
  · have hnz : entries.length ≠ 0 := by intro he;exact hz (List.eq_nil_of_length_eq_zero he)
    have apc' : a.pc = 0x800026ce#32 := by simpa only [ite_eq_right hnz] using apc
    have a10 : a.get 10 = req := (aframe 10 (by decide) (by decide) (by decide)).trans h10
    obtain ⟨b,tb,bpc,b15,b12,b16,b17,bframe,bcsr⟩ := E5R.Thermostat.HeaderSetup.contract_quiet B a ram req p raw.length entries.length
      h.table.bounded apc' a10 a14 h.object h.aligned h.pointer h.length
    have b11 : b.get 11 = q := (bframe 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((aframe 11 (by decide) (by decide) (by decide)).trans h11)
    have b13 : b.get 13 = 13#32 := (bframe 13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans a13
    have b1 : b.get 1 = c.get 1 := (bframe 1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans a1
    obtain ⟨d,n,hn,td,dpc,dresult,dframe,dcsr⟩ := E5R.Thermostat.HeaderScan.contract_quiet B ram p q raw query h.bytes hquery hq h.positive h.nowrap
      entries (req+32#32) h.table hz b bpc b16 b17 b15 b11 b12 b13
    refine ⟨d,11+n,by omega,(ta.trans tb).trans td,by rw [dpc,b1],dresult,?_,(dcsr.trans bcsr).trans acsr⟩
    intro r h5 h6 h7 h28 h29 hr
    exact (dframe r h5 h6 h7 (outside r 10 hr (by decide)) (outside r 11 hr (by decide)) (outside r 14 hr (by decide))
      (outside r 16 hr (by decide)) h28 h29).trans
      ((bframe r (outside r 12 hr (by decide)) (outside r 14 hr (by decide)) (outside r 15 hr (by decide))
        (outside r 16 hr (by decide)) (outside r 17 hr (by decide))).trans
        (aframe r (outside r 12 hr (by decide)) (outside r 13 hr (by decide)) (outside r 14 hr (by decide))))

end E5R.Thermostat.Header
namespace E5R.Thermostat.Header
theorem bytes_contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (req p q : Word)
    (raw query : List (BitVec 8)) (entries : List HeaderSpec.Entry)
    (h : Pre B ram req p raw entries) (hquery : ReadBytes.Span B img ram q query) (hq : query.length = 13)
    (hp : c.pc = 0x800026c0#32) (h10 : c.get 10 = req) (h11 : c.get 11 = q) (h12 : c.get 12 = 13#32) :
    ∃ d n, n ≤ 212*entries.length+13 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = c.get 1 &&& ~~~1 ∧
      HeaderResult.BytesAt B ram d (HeaderSpec.lookup raw query entries) ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨d,n,hn,ht,hpc,hresult,hframe,hcsr⟩ := E5R.Thermostat.Header.contract_quiet B c ram req p q raw query entries h hquery hq hp h10 h11 h12
  exact ⟨d,n,hn,ht,hpc,HeaderResult.as_lookup hresult,hframe,hcsr⟩

end E5R.Thermostat.Header
