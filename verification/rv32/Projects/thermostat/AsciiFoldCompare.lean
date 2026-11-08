import Projects.thermostat.AsciiFoldProgram
import Projects.thermostat.QuietByteLoad
import Projects.thermostat.QuietBranch
set_option autoImplicit false
namespace E5R.Thermostat.AsciiFoldCompare
open E5R E5R.Thermostat

theorem unequal (byte literal : BitVec 8) :
    taken .ne (BitVec.ofNat 32 (HeaderSpec.lower byte).toNat) (BitVec.ofNat 32 literal.toNat)=decide (HeaderSpec.lower byte≠literal) := by
  change decide (BitVec.ofNat 32 (HeaderSpec.lower byte).toNat≠BitVec.ofNat 32 literal.toNat)=_
  simp only [ne_eq,Literal.byte_injective]

/-- Six actual checked instructions: LBU, four-instruction ASCII fold, BNE.
    This is a program-logic composition theorem, not a semantic call summary. -/
theorem contract (B : Board) (img : List Segment) (c : Core) (ram : Word → BitVec 8)
    (pc base offset length branchOffset : Word) (baseReg byteReg tmp cmp : Reg) (swap : Bool)
    (byte literal : BitVec 8)
    (hp : c.pc=pc) (aligned : pc.getLsbD 0=false)
    (byteZero : byteReg.val≠0) (tmpZero : tmp.val≠0) (apart : byteReg≠tmp)
    (cmpByte : cmp≠byteReg) (cmpTmp : cmp≠tmp)
    (source : c.get baseReg=base) (expected : c.get cmp=BitVec.ofNat 32 literal.toNat)
    (memory : B.inRam (base+offset) 1=true) (data : ram (base+offset)=byte)
    (load : fetchDecode img pc=some (.load .b false byteReg baseReg offset,4#32))
    (fold : AsciiFoldProgram.Certificate img (pc+4#32) byteReg tmp byteReg swap length)
    (branchAligned : (pc+4#32+10#32+length).getLsbD 0=false)
    (targetAligned : (pc+4#32+10#32+length+branchOffset).getLsbD 0=false)
    (branch : fetchDecode img (pc+4#32+10#32+length)=some (.branch .ne byteReg cmp branchOffset,4#32)) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.lower byte≠literal then pc+4#32+10#32+length+branchOffset else pc+4#32+10#32+length+4#32) ∧
      d.get byteReg=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat ∧
      (∀ r : Reg, r≠byteReg → r≠tmp → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,read,pa,av,ar,ac⟩ := QuietByteLoad.contract B img c ram pc base offset byteReg baseReg byte hp aligned byteZero load source memory data
  obtain ⟨b,folded,pb,bv,br,bc⟩ := AsciiFoldProgram.contract B img a ram (pc+4#32) byteReg tmp byteReg swap length byte fold tmpZero byteZero apart pa av
  have cmpValue : b.get cmp=BitVec.ofNat 32 literal.toNat := (br cmp cmpTmp cmpByte).trans ((ar cmp cmpByte).trans expected)
  obtain ⟨d,tested,pd,dr,dc⟩ := QuietBranch.contract B img b ram (pc+4#32+10#32+length) 4#32 branchOffset .ne byteReg cmp
    (decide (HeaderSpec.lower byte≠literal)) pb branchAligned targetAligned branch (by rw [bv,cmpValue];exact unequal byte literal)
  refine ⟨d,(read.trans folded).trans tested,?_,(dr byteReg).trans bv,?_,dc.trans (bc.trans ac)⟩
  · simpa only [decide_eq_true_eq] using pd
  · intro r neqByte neqTmp
    exact (dr r).trans ((br r neqTmp neqByte).trans (ar r neqByte))
end E5R.Thermostat.AsciiFoldCompare
