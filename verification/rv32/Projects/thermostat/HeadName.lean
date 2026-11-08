import Projects.thermostat.HeadNameInit
import Projects.thermostat.HeadNameChecked
import Projects.thermostat.HeadNameMemory
namespace E5R.Thermostat.HeadName
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Actual nonempty header line name and colon validation, from real setup. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start finish length : Nat)
    (hp : c.pc=0x80002fbc#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 start)
    (h21 : c.get 21=BitVec.ofNat 32 (finish-start)) (h22 : c.get 22=0#32-BitVec.ofNat 32 length)
    (h25 : c.get 25=BitVec.ofNat 32 (finish-start)+0xffffffff#32) (hc : HeadNameClass.Constants c)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (hnext : ramRead ram (sp+16#32) .w=buf+1#32) (hbefore : ramRead ram (sp+12#32) .w=BitVec.ofNat 32 length+0xffffffff#32)
    (hmask : ramRead ram (sp+32#32) .w=9409#32) (h26 : c.get 26=BitVec.ofNat 32 finish)
    (mem : Memory.Block B buf length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) (hi : start<finish) (hn : finish≤length) (hlen : length≤2048) :
    let g := bytes ram buf
    let k := scan isTchar g start finish
    ∃ n d after, 12<n ∧ n≤17+25*(finish-start) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=(if HeadNameChecked.good g start k finish then 0x80003068#32 else 0x8000342c#32) ∧
      (after=ram ∨ after=ramWrite ram (sp+4#32) (BitVec.ofNat 32 k) .w) ∧
      (HeadNameChecked.good g start k finish → ramRead after (sp+4#32) .w=BitVec.ofNat 32 k ∧ HeadNameState.At d sp buf start k finish length) ∧
      (∀ r : Reg, r≠10 → r≠14 → r≠15 → r≠13 → r≠20 → r≠12 → r≠31 → r≠30 → r≠19 → r≠25 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,setup,pc,state,frame,csr⟩ := HeadNameInit.contract B c ram sp buf start finish length hp h2 h24 h21 h22 h25 hc hraw hbuf hnext hbefore stack ha hi hn hlen
  obtain ⟨n,d,after,nlo,nhi,parse,endPC,effect,good,frame2,csr2⟩ := HeadNameChecked.contract B a ram sp buf start finish length pc state
    ((frame 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h24) ((frame 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h26) hmask stack ha hi hn hlen mem
  refine ⟨12+n,d,after,by omega,by omega,setup.trans parse,endPC,effect,?_,?_,csr2.trans csr⟩
  · intro accepted
    obtain ⟨stored,state2⟩ := good accepted
    exact ⟨by rw [stored];exact ramRead_ramWrite_w _ _ _,state2⟩
  · intro r h10 h14 h15 h13 h20 h12 h31 h30 h19 h25
    exact (frame2 r h30 h19 h12 h14 h10 h25 h31).trans (frame r h10 h14 h15 h13 h20 h12 h31)
end E5R.Thermostat.HeadName
