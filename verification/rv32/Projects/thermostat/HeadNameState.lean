import Projects.thermostat.HeadNameClass
import Projects.thermostat.HeadFieldsMath
namespace E5R.Thermostat.HeadNameState
open E5R E5R.Thermostat

structure At (c : Core) (sp buf : Word) (start pos finish length : Nat) : Prop where
  stack : c.get 2=sp
  base : c.get 20=buf+BitVec.ofNat 32 start
  count : c.get 14=BitVec.ofNat 32 (pos-start)
  last : c.get 15=BitVec.ofNat 32 (finish-start-1)
  relative : c.get 13=BitVec.ofNat 32 start-BitVec.ofNat 32 length
  ptr : c.get 10=buf+BitVec.ofNat 32 (pos+1)
  inverse : c.get 25=BitVec.ofNat 32 (finish-pos-1)
  remaining : c.get 31=BitVec.ofNat 32 (length-pos-1)
  constants : HeadNameClass.Constants c

theorem preserve {c d : Core} {sp buf : Word} {start pos finish length : Nat} (h : At c sp buf start pos finish length)
    (frame : ∀ r : Reg, r≠30 → r≠19 → r≠12 → d.get r=c.get r) : At d sp buf start pos finish length := by
  exact ⟨(frame 2 (by decide) (by decide) (by decide)).trans h.stack,
    (frame 20 (by decide) (by decide) (by decide)).trans h.base,
    (frame 14 (by decide) (by decide) (by decide)).trans h.count,
    (frame 15 (by decide) (by decide) (by decide)).trans h.last,
    (frame 13 (by decide) (by decide) (by decide)).trans h.relative,
    (frame 10 (by decide) (by decide) (by decide)).trans h.ptr,
    (frame 25 (by decide) (by decide) (by decide)).trans h.inverse,
    (frame 31 (by decide) (by decide) (by decide)).trans h.remaining,
    HeadNameClass.preserve h.constants frame⟩

theorem index (start pos : Nat) (h : start≤pos) :
    BitVec.ofNat 32 start+BitVec.ofNat 32 (pos-start)=BitVec.ofNat 32 pos := by
  rw [←BitVec.ofNat_add,Nat.add_sub_of_le h]

theorem last_test (start pos finish : Nat) (hs : start≤pos) (hi : pos<finish) (hn : finish≤2048) :
    taken .eq (BitVec.ofNat 32 (finish-start-1)) (BitVec.ofNat 32 (pos-start))=decide (pos+1=finish) := by
  simp only [taken]
  have a : (BitVec.ofNat 32 (finish-start-1)).toNat=finish-start-1 := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have b : (BitVec.ofNat 32 (pos-start)).toNat=pos-start := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have eq : BitVec.ofNat 32 (finish-start-1)=BitVec.ofNat 32 (pos-start) ↔ pos+1=finish := by
    constructor
    · intro e;have ee := congrArg BitVec.toNat e;rw [a,b] at ee;omega
    · intro e;congr 1;omega
  apply Bool.eq_iff_iff.mpr
  simpa only [beq_iff_eq,decide_eq_true_eq] using eq
end E5R.Thermostat.HeadNameState
