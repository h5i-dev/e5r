import Projects.thermostat.HeadPrologue
import Projects.thermostat.HeadScanStart
namespace E5R.Thermostat.HeadReady
open E5R E5R.Thermostat

/-- Actual ELF entry to the first scan cutpoint, using the main caller's
    configuration and bounded RX allocation. The zero-length case takes the
    real incomplete/full dispatch cutpoint instead of entering the byte loop. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (length : Nat)
    (hp : c.pc=0x80002c46#32) (h2 : c.get 2=sp+384#32) (h13 : c.get 13=sp+3664#32)
    (h12 : c.get 12=BitVec.ofNat 32 length) (hlen : length≤2048)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0)
    (hmax : ramRead ram (sp+3664#32) .w=1024#32) :
    ∃ steps d, 18≤steps ∧ steps≤22 ∧
      Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,HeadStackSave.memory ram sp c.get⟩ ∧
      d.pc=(if length=0 then 0x80002ce6#32 else 0x80002c90#32) ∧
      d.get 2=sp ∧ d.get 14=BitVec.ofNat 32 (min length 1024) ∧ d.get 16=1024#32 ∧
      (length≠0 → d.get 9=0#32 ∧ d.get 15=10#32 ∧ d.get 17=13#32) ∧
      (∀ r : Reg, r≠2 → r≠9 → r≠14 → r≠15 → r≠16 → r≠17 → d.get r=c.get r) ∧
      ViewFrame.Region ram (HeadStackSave.memory ram sp c.get) (sp+516#32) 2048 ∧ d.sameCsr c := by
  obtain ⟨a,e,hlo,hi,prologue,pc,stack,limit,max,frame,csr⟩ := HeadPrologue.contract B c ram sp length hp h2 h13 h12 hlen hm ha hmax
  obtain ⟨b,d,blo,bhi,setup,pc2,initial,frame2,csr2⟩ :=
    HeadScanStart.contract B e (HeadStackSave.memory ram sp c.get) (min length 1024) pc limit (by omega)
  refine ⟨a+b,d,by omega,by omega,prologue.trans setup,?_,?_,?_,?_,?_,?_,?_,csr2.trans csr⟩
  · have iff : (min length 1024=0)=(length=0) := by simp
    simpa only [iff] using pc2
  · exact (frame2 2 (by decide) (by decide) (by decide)).trans stack
  · exact (frame2 14 (by decide) (by decide) (by decide)).trans limit
  · exact (frame2 16 (by decide) (by decide) (by decide)).trans max
  · intro nonempty
    exact initial (by simpa using nonempty)
  · intro r h2 h9 h14 h15 h16 h17
    exact (frame2 r h9 h15 h17).trans (frame r h2 h14 h16)
  · exact HeadStackMemory.region ram sp c.get 516 2048 (by decide) (by decide)
end E5R.Thermostat.HeadReady
