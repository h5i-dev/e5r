-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CopyAlignedEntry
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.CopyAlignedDestinationQuiet
import Projects.thermostat.CopyAlignedSetupQuiet
import Projects.thermostat.CopyLongStartQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.CopyAlignedEntry
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp src dst : Word) (n bulk : Nat)
    (hp : c.pc=0x80005182#32) (hsp : c.get 2=sp+16#32) (h10 : c.get 10=dst) (h11 : c.get 11=src)
    (h12 : c.get 12=BitVec.ofNat 32 n) (hn : 16≤n) (hnb : n<2^32) (hb : 0<bulk) (hw : dst.toNat+bulk<2^32)
    (has : src.toNat%4=0) (had : dst.toNat%4=0)
    (hmask : BitVec.ofNat 32 n &&& 0xfffffffc#32 = BitVec.ofNat 32 bulk) :
    ∃ d, Quiet.Steps B img 17 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80005212#32 ∧ d.get 2=sp ∧ d.get 10=dst ∧
      d.get 11=src ∧ d.get 12=BitVec.ofNat 32 n ∧ d.get 13=dst+BitVec.ofNat 32 bulk ∧ d.get 14=dst ∧
      d.get 15=BitVec.ofNat 32 bulk ∧ d.get 16=src ∧
      (∀ r : Reg, CopyRegs.Preserved r → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,ta,apc,_,asp,_,ar,ac⟩ := E5R.Thermostat.CopyLongStart.contract_quiet B c ram sp n hsp h12 hn hnb hp
  have a10 : a.get 10=dst := (ar 10 (by decide) (by decide) (by decide)).trans h10
  have a11 : a.get 11=src := (ar 11 (by decide) (by decide) (by decide)).trans h11
  have a12 : a.get 12=BitVec.ofNat 32 n := (ar 12 (by decide) (by decide) (by decide)).trans h12
  obtain ⟨b,tb,bpc,b13,b14,br,bc⟩ := E5R.Thermostat.CopyAlignedDestination.contract_quiet B a ram dst a10 had apc
  have b11 := (br 11 (by decide) (by decide)).trans a11
  have b12 := (br 12 (by decide) (by decide)).trans a12
  obtain ⟨d,td,dpc,d11,d12,d15,_,d13,d16,dr,dc⟩ := E5R.Thermostat.CopyAlignedSetup.contract_quiet B b ram src dst n bulk hb hw b11 b12 b13 b14 has hmask bpc
  refine ⟨d,(ta.trans tb).trans td,dpc,?_,?_,d11,d12,d13,?_,d15,d16,?_,(dc.trans bc).trans ac⟩
  · exact (dr 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 2 (by decide) (by decide)).trans asp)
  · exact (dr 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 10 (by decide) (by decide)).trans a10)
  · exact (dr 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b14
  · intro reg hr
    have ne (q : Reg) (hq : q.val<18) (h1 : q≠1) (h8 : q≠8) (h9 : q≠9) := CopyRegs.ne_low reg q hr hq h1 h8 h9
    exact (dr reg (ne 11 (by decide) (by decide) (by decide) (by decide)) (ne 12 (by decide) (by decide) (by decide) (by decide))
      (ne 15 (by decide) (by decide) (by decide) (by decide)) (ne 5 (by decide) (by decide) (by decide) (by decide))
      (ne 13 (by decide) (by decide) (by decide) (by decide)) (ne 16 (by decide) (by decide) (by decide) (by decide))).trans
      ((br reg (ne 13 (by decide) (by decide) (by decide) (by decide)) (ne 14 (by decide) (by decide) (by decide) (by decide))).trans
        (ar reg (ne 6 (by decide) (by decide) (by decide) (by decide)) (ne 2 (by decide) (by decide) (by decide) (by decide)) (ne 13 (by decide) (by decide) (by decide) (by decide))))

end E5R.Thermostat.CopyAlignedEntry
