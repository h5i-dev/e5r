import Projects.thermostat.Proof
import Projects.thermostat.MainMethodByteTest
import Projects.thermostat.MainMethodByteMath
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.MainMethodChain
open E5R E5R.Thermostat
abbrev Check := Nat × Nat
abbrev failed : Word := 0x80001160#32

/-- An instruction-level certificate for one three-instruction comparison.
    These fields are all checked against the immutable executable image. -/
structure Node (pc : Word) (check : Check) where
  branchOffset : Word
  literal : check.2≤255
  aligned : pc.getLsbD 0=false
  aligned1 : (pc+4#32).getLsbD 0=false
  aligned2 : (pc+8#32).getLsbD 0=false
  target : pc+8#32+branchOffset=failed
  load : fetchDecode img pc=some (.load .b false 16 15 (BitVec.ofNat 32 check.1),4#32)
  lit : fetchDecode img (pc+4#32)=some (.opimm .add 17 0 (BitVec.ofNat 32 check.2),4#32)
  branch : fetchDecode img (pc+8#32)=some (.branch .ne 16 17 branchOffset,4#32)

inductive Certified : List Check → Word → Word → Prop
  | nil (pc) : Certified [] pc pc
  | cons {check rest pc finish} : Node pc check → Certified rest (pc+12#32) finish → Certified (check::rest) pc finish

def accepts : List Check → (Nat → Nat) → Bool
  | [],_ => true
  | check::rest,g => decide (g check.1=check.2) && accepts rest g

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠16 → r≠17 → d.get r=c.get r

theorem Frame.trans {a b c : Core} (h : Frame a b) (k : Frame b c) : Frame a c :=
  fun r x y => (k r x y).trans (h r x y)

/-- Soundness of checked comparison-chain generation. There are no semantic
    summaries in the certificate: its leaves contain only actual decodes. -/
theorem contract (B : Board) (ram : Word → BitVec 8) (base : Word) (bytes : Nat → BitVec 8)
    {checks pc finish} (cert : Certified checks pc finish)
    (memory : ∀ check∈checks, B.inRam (base+BitVec.ofNat 32 check.1) 1=true)
    (data : ∀ check∈checks, ram (base+BitVec.ofNat 32 check.1)=bytes check.1)
    (c : Core) (hp : c.pc=pc) (h15 : c.get 15=base) :
    ∃ n d, n≤3*checks.length ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if accepts checks (fun i => (bytes i).toNat) then finish else failed) ∧ Frame c d ∧ d.sameCsr c := by
  induction cert generalizing c with
  | nil pc =>
    exact ⟨0,c,by simp,.refl _,hp,fun _ _ _ => rfl,rfl⟩
  | @cons check rest pc finish node _ ih =>
    have targetAligned : (pc+8#32+node.branchOffset).getLsbD 0=false := by rw [node.target];decide
    obtain ⟨a,step,pa,a16,a17,ar,ac⟩ := MainMethodByteTest.contract B img c ram pc base (BitVec.ofNat 32 check.1) (BitVec.ofNat 32 check.2) node.branchOffset (bytes check.1) .ne (decide ((bytes check.1).toNat≠check.2)) hp h15
      (memory check (by simp)) (data check (by simp)) node.aligned node.aligned1 node.aligned2 targetAligned node.load node.lit node.branch
      (MainMethodByteMath.neTest _ _ node.literal)
    by_cases equal : (bytes check.1).toNat=check.2
    · have notUnequal : ¬(bytes check.1).toNat≠check.2 := by omega
      have next : a.pc=pc+12#32 := by simpa only [notUnequal,decide_false,Bool.false_eq_true,ite_false] using pa
      obtain ⟨n,d,nb,tail,pd,dr,dc⟩ := ih (fun k hk => memory k (by simp [hk])) (fun k hk => data k (by simp [hk])) a next ((ar 15 (by decide) (by decide)).trans h15)
      refine ⟨3+n,d,by simp only [List.length_cons];omega,step.trans tail,?_,Frame.trans ar dr,dc.trans ac⟩
      simpa only [accepts,equal,decide_true,Bool.true_and] using pd
    · have pcFail : a.pc=failed := by simpa only [show decide ((bytes check.1).toNat≠check.2)=true from decide_eq_true equal,ite_true,node.target] using pa
      refine ⟨3,a,by simp only [List.length_cons];omega,step,?_,ar,ac⟩
      simpa only [accepts,equal,decide_false,Bool.false_and,Bool.false_eq_true,ite_false] using pcFail
end E5R.Thermostat.MainMethodChain
