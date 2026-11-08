import Projects.thermostat.MainQueryLoad
import Projects.thermostat.MainQueryHitBranch
import Projects.thermostat.MainQueryIncrement
import Projects.thermostat.MainQueryContinueBranch
import Projects.thermostat.MainQueryFound
import Projects.thermostat.MainQueryAbsent
import Projects.thermostat.MainQueryMath
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainQueryLoop
open E5R E5R.Thermostat MainQueryMath

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (rx : Word) (bytes : Nat → BitVec 8)
    (start i finish : Nat) (lo : start≤i) (inside : i<finish) (bound : finish≤2048)
    (memory : ∀ k, k<finish → B.inRam (rx+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, k<finish → ram (rx+BitVec.ofNat 32 k)=bytes k)
    (hp : c.pc=0x80000be0#32)
    (h10 : c.get 10=rx+BitVec.ofNat 32 start)
    (h12 : c.get 12=rx+BitVec.ofNat 32 i+1#32)
    (h14 : c.get 14=BitVec.ofNat 32 (i-start)) (h15 : c.get 15=63#32)
    (h28 : c.get 28=BitVec.ofNat 32 (finish-start))
    (h29 : c.get 29=BitVec.ofNat 32 start) (h30 : c.get 30=BitVec.ofNat 32 finish) :
    ∃ n d, n≤5*(finish-i)+6 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000d50#32 ∧
      d.get 28=BitVec.ofNat 32 (MainQuerySpec.position (fun k => (bytes k).toNat) i finish-start) ∧
      d.get 12=rx+BitVec.ofNat 32 (if MainQuerySpec.position (fun k => (bytes k).toNat) i finish<finish then MainQuerySpec.position (fun k => (bytes k).toNat) i finish+1 else start) ∧
      d.get 13=BitVec.ofNat 32 (MainQuerySpec.queryLength (fun k => (bytes k).toNat) i finish) ∧
      Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,load,pa,a13,ar,ac⟩ := MainQueryLoad.contract B c ram (rx+BitVec.ofNat 32 i) (bytes i) h12 (memory i inside) (data i inside) hp
  have aFrame : Frame c a := by
    intro r safe
    simp only [List.mem_cons,List.mem_singleton,not_or] at safe
    exact ar r safe.2.1
  have a15 : a.get 15=63#32 := (ar 15 (by decide)).trans h15
  obtain ⟨b,branch,pb,br,bc⟩ := MainQueryHitBranch.contract B a ram (BitVec.ofNat 32 (bytes i).toNat) 63#32 (decide ((bytes i).toNat=63)) pa a13 a15 (question _)
  have bFrame : Frame a b := fun r _ => br r
  by_cases hit : (bytes i).toNat=63
  · have atHit : b.pc=0x80000d44#32 := by simpa only [hit,decide_true,ite_true] using pb
    have b29 : b.get 29=BitVec.ofNat 32 start := (br 29).trans ((ar 29 (by decide)).trans h29)
    have b30 : b.get 30=BitVec.ofNat 32 finish := (br 30).trans ((ar 30 (by decide)).trans h30)
    have b14 : b.get 14=BitVec.ofNat 32 (i-start) := (br 14).trans ((ar 14 (by decide)).trans h14)
    obtain ⟨d,found,pd,d13,d15,d28,dr,dc⟩ := MainQueryFound.contract B b ram (BitVec.ofNat 32 start) (BitVec.ofNat 32 finish) (BitVec.ofNat 32 (i-start)) b29 b30 b14 atHit
    have dFrame : Frame b d := by
      intro r safe
      simp only [List.mem_cons,List.mem_singleton,not_or] at safe
      exact dr r safe.2.1 safe.2.2.2.1 safe.2.2.2.2.1
    have pos : MainQuerySpec.position (fun k => (bytes k).toNat) i finish=i := MainQuerySpec.found _ _ _ inside hit
    refine ⟨6,d,by omega,(load.trans branch).trans found,pd,?_,?_,?_,(aFrame.trans bFrame).trans dFrame,dc.trans (bc.trans ac)⟩
    · simpa only [pos] using d28
    · simp only [pos,inside,ite_true]
      have ptr := (dr 12 (by decide) (by decide) (by decide)).trans ((br 12).trans ((ar 12 (by decide)).trans h12))
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using ptr
    · simp only [MainQuerySpec.queryLength,pos,inside,ite_true]
      exact d13.trans (found_length start i finish lo inside bound)
  · have atSkip : b.pc=0x80000be8#32 := by simpa only [hit,decide_false,Bool.false_eq_true,ite_false] using pb
    have b12 : b.get 12=rx+BitVec.ofNat 32 i+1#32 := (br 12).trans ((ar 12 (by decide)).trans h12)
    have b14 : b.get 14=BitVec.ofNat 32 (i-start) := (br 14).trans ((ar 14 (by decide)).trans h14)
    obtain ⟨p,inc,pp,p14,p12,pr,pcsr⟩ := MainQueryIncrement.contract B b ram _ _ b14 b12 atSkip
    have pFrame : Frame b p := by
      intro r safe
      simp only [List.mem_cons,List.mem_singleton,not_or] at safe
      exact pr r safe.2.2.1 safe.1
    have p28 : p.get 28=BitVec.ofNat 32 (finish-start) := (pr 28 (by decide) (by decide)).trans ((br 28).trans ((ar 28 (by decide)).trans h28))
    obtain ⟨e,again,pe,er,ec⟩ := MainQueryContinueBranch.contract B p ram _ _ (decide (i+1<finish)) pp p28 p14 (MainQueryMath.again start i finish lo inside bound)
    have eFrame : Frame p e := fun r _ => er r
    have trace : Quiet.Steps B img 5 ⟨c,ram⟩ ⟨e,ram⟩ := ((load.trans branch).trans inc).trans again
    have frame : Frame c e := ((aFrame.trans bFrame).trans pFrame).trans eFrame
    have csr : e.sameCsr c := ec.trans (pcsr.trans (bc.trans ac))
    have pos : MainQuerySpec.position (fun k => (bytes k).toNat) i finish=MainQuerySpec.position (fun k => (bytes k).toNat) (i+1) finish := MainQuerySpec.step _ _ _ inside hit
    by_cases more : i+1<finish
    · have atNext : e.pc=0x80000be0#32 := by simpa only [more,decide_true,ite_true] using pe
      have e12 : e.get 12=rx+BitVec.ofNat 32 (i+1)+1#32 := by
        have eq := (er 12).trans p12
        simpa only [BitVec.ofNat_add,BitVec.add_assoc] using eq
      have e14 : e.get 14=BitVec.ofNat 32 (i+1-start) := (er 14).trans (p14.trans (offset_next start i lo))
      obtain ⟨n,d,nb,next,pd,d28,d12,d13,df,dc⟩ := contract B e ram rx bytes start (i+1) finish (by omega) more bound memory data atNext
        ((frame 10 (by decide)).trans h10) e12 e14
        ((er 15).trans ((pr 15 (by decide) (by decide)).trans ((br 15).trans ((ar 15 (by decide)).trans h15))))
        ((er 28).trans p28) ((frame 29 (by decide)).trans h29) ((frame 30 (by decide)).trans h30)
      refine ⟨5+n,d,by omega,trace.trans next,pd,?_,?_,?_,frame.trans df,dc.trans csr⟩
      · simpa only [pos] using d28
      · simpa only [pos] using d12
      · simpa only [MainQuerySpec.queryLength,pos] using d13
    · have eq : i+1=finish := by omega
      have atEnd : e.pc=0x80000bf0#32 := by simpa only [more,decide_false,Bool.false_eq_true,ite_false] using pe
      obtain ⟨d,exit,pd,d13,d12,dr,dc⟩ := MainQueryAbsent.contract B e ram (rx+BitVec.ofNat 32 start) ((frame 10 (by decide)).trans h10) atEnd
      have df : Frame e d := by
        intro r safe
        simp only [List.mem_cons,List.mem_singleton,not_or] at safe
        exact dr r safe.2.1 safe.1
      have endpos : MainQuerySpec.position (fun k => (bytes k).toNat) i finish=finish := by rw [pos,eq,MainQuerySpec.end_at]
      refine ⟨8,d,by omega,trace.trans exit,pd,?_,?_,?_,frame.trans df,dc.trans csr⟩
      · rw [endpos]
        exact (dr 28 (by decide) (by decide)).trans ((er 28).trans p28)
      · simpa only [endpos,show ¬finish<finish by omega,ite_false] using d12
      · simpa only [MainQuerySpec.queryLength,endpos,show ¬finish<finish by omega,ite_false] using d13
termination_by finish-i
 decreasing_by omega
end E5R.Thermostat.MainQueryLoop
