import Projects.thermostat.MainMethodChain
import Projects.thermostat.MainMethodLast
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.MainMethodSuffix
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠14 → r≠15 → r≠16 → r≠17 → d.get r=c.get r

def SelectFrame (c d : Core) : Prop := ∀ r : Reg, r≠14 → r≠16 → r≠17 → d.get r=c.get r

/-- Composition uses an actual Quiet instruction proof for the selection
    fragment, never a standalone semantic assumption about the application. -/
theorem contract (B : Board) (ram : Word → BitVec 8) (base : Word) (bytes : Nat → BitVec 8)
    (len last literal candidate : Nat) (checks : List MainMethodChain.Check) (pc selected : Word)
    (cert : MainMethodChain.Certified checks pc selected)
    (checksBound : ∀ check∈checks, check.1<len) (lastBound : last<len) (literalBound : literal≤255)
    (memory : ∀ k, k<len → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, k<len → ram (base+BitVec.ofNat 32 k)=bytes k)
    (selection : ∀ a : Core, a.pc=selected → ∃ n b, n≤4 ∧ Quiet.Steps B img n ⟨a,ram⟩ ⟨b,ram⟩ ∧
      b.pc=0x80001154#32 ∧ b.get 14=BitVec.ofNat 32 candidate ∧ b.get 16=BitVec.ofNat 32 literal ∧
      b.get 17=BitVec.ofNat 32 last ∧ SelectFrame a b ∧ b.sameCsr a)
    (c : Core) (hp : c.pc=pc) (h15 : c.get 15=base) (h14 : c.get 14=6#32) :
    ∃ n d, n≤3*checks.length+8 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001160#32 ∧
      d.get 14=(if MainMethodChain.accepts checks (fun i => (bytes i).toNat) && decide ((bytes last).toNat=literal) then BitVec.ofNat 32 candidate else 6#32) ∧
      Frame c d ∧ d.sameCsr c := by
  obtain ⟨first,a,nb,trace,pa,ar,ac⟩ := MainMethodChain.contract B ram base bytes cert
    (fun k hk => memory k.1 (checksBound k hk)) (fun k hk => data k.1 (checksBound k hk)) c hp h15
  cases accept : MainMethodChain.accepts checks (fun i => (bytes i).toNat) with
  | false =>
    have pcFail : a.pc=0x80001160#32 := by simpa only [accept,Bool.false_eq_true,ite_false] using pa
    refine ⟨first,a,by omega,trace,pcFail,?_,fun r _ _ x y => ar r x y,ac⟩
    simpa only [accept,Bool.false_and,Bool.false_eq_true,ite_false] using (ar 14 (by decide) (by decide)).trans h14
  | true =>
    have pcSelect : a.pc=selected := by simpa only [accept,ite_true] using pa
    obtain ⟨middle,b,mb,select,pb,b14,b16,b17,br,bc⟩ := selection a pcSelect
    have b15 : b.get 15=base := (br 15 (by decide) (by decide) (by decide)).trans ((ar 15 (by decide) (by decide)).trans h15)
    obtain ⟨lastCount,d,_,lb,finish,pd,d14,dr,dc⟩ := MainMethodLast.contract B b ram base (BitVec.ofNat 32 last) (BitVec.ofNat 32 candidate) literal (bytes last) pb b15 b17 b14 b16 literalBound (memory last lastBound) (data last lastBound)
    refine ⟨first+middle+lastCount,d,by omega,(trace.trans select).trans finish,pd,?_,?_,dc.trans (bc.trans ac)⟩
    · simpa only [accept,Bool.true_and,decide_eq_true_eq] using d14
    · intro r h14 h15 h16 h17
      exact (dr r h14 h15).trans ((br r h14 h16 h17).trans (ar r h16 h17))
end E5R.Thermostat.MainMethodSuffix
