import Projects.thermostat.AsciiFoldCompare
set_option autoImplicit false
namespace E5R.Thermostat.AsciiFoldBranch
open E5R E5R.Thermostat

/-- Cached-byte counterpart of AsciiFoldCompare: four checked ALU instructions
    followed by the checked comparison branch. -/
theorem contract (B : Board) (img : List Segment) (c : Core) (ram : Word → BitVec 8)
    (pc length branchOffset : Word) (src tmp dst cmp : Reg) (swap : Bool) (byte literal : BitVec 8)
    (fold : AsciiFoldProgram.Certificate img pc src tmp dst swap length)
    (tmpZero : tmp.val≠0) (dstZero : dst.val≠0) (apart : src≠tmp) (cmpDst : cmp≠dst) (cmpTmp : cmp≠tmp)
    (hp : c.pc=pc) (value : c.get src=BitVec.ofNat 32 byte.toNat) (expected : c.get cmp=BitVec.ofNat 32 literal.toNat)
    (aligned : (pc+10#32+length).getLsbD 0=false) (targetAligned : (pc+10#32+length+branchOffset).getLsbD 0=false)
    (branch : fetchDecode img (pc+10#32+length)=some (.branch .ne dst cmp branchOffset,4#32)) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.lower byte≠literal then pc+10#32+length+branchOffset else pc+10#32+length+4#32) ∧
      d.get dst=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat ∧
      (∀ r : Reg, r≠tmp → r≠dst → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,folded,pa,av,ar,ac⟩ := AsciiFoldProgram.contract B img c ram pc src tmp dst swap length byte fold tmpZero dstZero apart hp value
  obtain ⟨d,tested,pd,dr,dc⟩ := QuietBranch.contract B img a ram (pc+10#32+length) 4#32 branchOffset .ne dst cmp
    (decide (HeaderSpec.lower byte≠literal)) pa aligned targetAligned branch
    (by rw [av,(ar cmp cmpTmp cmpDst).trans expected];exact AsciiFoldCompare.unequal byte literal)
  refine ⟨d,folded.trans tested,?_,(dr dst).trans av,?_,dc.trans ac⟩
  · simpa only [decide_eq_true_eq] using pd
  · intro r nt nd
    exact (dr r).trans (ar r nt nd)
end E5R.Thermostat.AsciiFoldBranch
