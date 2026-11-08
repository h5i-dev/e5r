import Projects.thermostat.MainQuerySetup
import Projects.thermostat.MainQueryLoop
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.MainQuery
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r∉[7,11,12,13,14,15,28] → d.get r=c.get r

/-- The actual stack method-span loads and target split, with unchanged RAM.
    Readability is required only for the original nonempty target. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp rx ms me : Word)
    (bytes : Nat → BitVec 8) (start finish : Nat)
    (ordered : start<finish) (bound : finish≤2048)
    (memory : ∀ k, k<finish → B.inRam (rx+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, k<finish → ram (rx+BitVec.ofNat 32 k)=bytes k)
    (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
    (hp : c.pc=0x80000bd0#32) (h2 : c.get 2=sp) (h21 : c.get 21=rx)
    (h29 : c.get 29=BitVec.ofNat 32 start) (h30 : c.get 30=BitVec.ofNat 32 finish)
    (h10 : c.get 10=rx+BitVec.ofNat 32 start) (h15 : c.get 15=63#32)
    (hms : ramRead ram (sp+28#32) .w=ms) (hme : ramRead ram (sp+24#32) .w=me) :
    ∃ n d, n≤5*(finish-start)+12 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000d50#32 ∧
      d.get 7=ms ∧ d.get 11=me ∧
      d.get 28=BitVec.ofNat 32 (MainQuerySpec.pathLength (fun k => (bytes k).toNat) start finish) ∧
      d.get 12=rx+BitVec.ofNat 32 (MainQuerySpec.queryStart (fun k => (bytes k).toNat) start finish) ∧
      d.get 13=BitVec.ofNat 32 (MainQuerySpec.queryLength (fun k => (bytes k).toNat) start finish) ∧
      Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,setup,pa,a14,a12,a28,a7,a11,ar,ac⟩ := MainQuerySetup.contract B c ram sp rx _ _ ms me h2 h21 h29 h30 hms hme stack aligned hp
  have preserve (r : Reg) (safe : r∈[10,15,29,30]) : a.get r=c.get r := by
    have neq : ∀ r : Reg, r∈[10,15,29,30] → r≠14 ∧ r≠12 ∧ r≠28 ∧ r≠7 ∧ r≠11 := by decide +kernel
    obtain ⟨x,y,z,u,v⟩ := neq r safe
    exact ar r x y z u v
  have length : a.get 28=BitVec.ofNat 32 (finish-start) :=
    a28.trans (BitVec.ofNat_sub_ofNat_of_le finish start (by omega) (by omega))
  have zero : a.get 14=BitVec.ofNat 32 (start-start) := by simpa only [Nat.sub_self] using a14
  obtain ⟨n,d,nb,loop,pd,d28,d12,d13,dr,dc⟩ := MainQueryLoop.contract B a ram rx bytes start start finish (by omega) ordered bound memory data pa
    ((preserve 10 (by decide)).trans h10) a12 zero ((preserve 15 (by decide)).trans h15) length
    ((preserve 29 (by decide)).trans h29) ((preserve 30 (by decide)).trans h30)
  refine ⟨6+n,d,by omega,setup.trans loop,pd,(dr 7 (by decide)).trans a7,(dr 11 (by decide)).trans a11,d28,d12,d13,?_,dc.trans ac⟩
  intro r safe
  simp only [List.mem_cons,List.mem_singleton,not_or] at safe
  have loopSafe : r∉[12,13,14,15,28] := by
    simp only [List.mem_cons,List.mem_singleton,not_or]
    exact safe.2.2
  exact (dr r loopSafe).trans (ar r safe.2.2.2.2.1 safe.2.2.1 safe.2.2.2.2.2.2.1 safe.1 safe.2.1)
end E5R.Thermostat.MainQuery
