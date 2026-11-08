import Projects.thermostat.HeadClNumberGuard
import Projects.thermostat.HeadClDigitLoad
import Projects.thermostat.HeadClDigitBranch
import Projects.thermostat.HeadClAccumulate
import Projects.thermostat.HeadClOverflowRaw
import Projects.thermostat.HeadClOverflowBranch
import Projects.thermostat.HeadHeaderPayloadLarge
import Projects.thermostat.HeadLineScanSpec
namespace E5R.Thermostat.HeadClNumberStep
open E5R E5R.Thermostat HeadLineScanSpec

def status (acc : Nat) (byte : BitVec 8) : Word :=
  if DecimalSpec.digit byte ∧ 1024<HeadClNumberMath.next acc byte then 413#32 else 400#32

def good (acc : Nat) (byte : BitVec 8) : Prop :=
  DecimalSpec.digit byte=true ∧ HeadClNumberMath.next acc byte≤1024
instance (acc : Nat) (byte : BitVec 8) : Decidable (good acc byte) := by unfold good;infer_instance

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (pos length acc : Nat)
    (hp : c.pc=0x80003206#32) (h1 : c.get 1=400#32) (h2 : c.get 2=sp)
    (h10 : c.get 10=buf+BitVec.ofNat 32 pos) (h31 : c.get 31=BitVec.ofNat 32 (length-pos))
    (h14 : c.get 14=BitVec.ofNat 32 acc) (h13 : c.get 13=0#32) (h16 : c.get 16=10#32)
    (hlimit : ramRead ram (sp+8#32) .w=1024#32) (inside : pos<length) (bound : length≤2048) (accepted : acc≤1024)
    (memory : Memory.Block B buf length) (stack : Memory.Block B sp 56) (aligned : sp.toNat%4=0) :
    let byte := ram (buf+BitVec.ofNat 32 pos)
    ∃ n d, 6≤n ∧ n≤26 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if good acc byte then 0x80003256#32 else 0x8000342c#32) ∧ d.get 1=status acc byte ∧
      (DecimalSpec.digit byte=true → d.get 14=BitVec.ofNat 32 (HeadClNumberMath.next acc byte) ∧ d.get 13=0#32) ∧
      (∀ r : Reg, r≠1 → r≠30 → r≠12 → r≠29 → r≠14 → r≠13 → d.get r=c.get r) ∧ d.sameCsr c := by
  let byte := ram (buf+BitVec.ofNat 32 pos)
  change ∃ n d, 6≤n ∧ n≤26 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
    d.pc=(if good acc byte then 0x80003256#32 else 0x8000342c#32) ∧ d.get 1=status acc byte ∧
    (DecimalSpec.digit byte=true → d.get 14=BitVec.ofNat 32 (HeadClNumberMath.next acc byte) ∧ d.get 13=0#32) ∧
    (∀ r : Reg, r≠1 → r≠30 → r≠12 → r≠29 → r≠14 → r≠13 → d.get r=c.get r) ∧ d.sameCsr c
  have nonzero : taken .eq (BitVec.ofNat 32 (length-pos)) (0 : Word)=false := by
    change taken .eq (BitVec.ofNat 32 (length-pos)) (BitVec.ofNat 32 0)=false
    rw [Usize.eq _ _ (by omega) (by decide)]
    simp only [show length-pos≠0 by omega,decide_false]
  obtain ⟨a,t0,p0,fa,sa⟩ := HeadClNumberGuard.contract B c ram _ (0 : Word) false hp h31 (Core.get_zero c) nonzero
  have p0' : a.pc=0x8000320a#32 := by simpa using p0
  obtain ⟨b,t1,p1,v30,v12,v29,fb,sb⟩ := HeadClDigitLoad.contract B a ram _ (BitVec.ofNat 32 byte.toNat)
    ((fa 10).trans h10) rfl (Memory.block_access memory (by decide) (by omega)) p0'
  obtain ⟨e,t2,p2,fe,se⟩ := HeadClDigitBranch.contract B b ram _ _ _ p1 v12 v29 (HeadClNumberMath.digit_test byte)
  have source (r : Reg) (h30 : r≠30) (h12 : r≠12) (h29 : r≠29) : e.get r=c.get r :=
    (fe r).trans ((fb r h30 h12 h29).trans (fa r))
  cases digit : DecimalSpec.digit byte with
  | false =>
    have noGood : ¬good acc byte := by simp only [good,digit,Bool.false_eq_true,false_and,not_false_eq_true]
    have endPC : e.pc=0x8000342c#32 := by simpa only [digit,Bool.not_false,ite_true] using p2
    change ∃ n d, _
    refine ⟨6,e,by decide,by decide,by simpa using (t0.trans t1).trans t2,?_,?_,?_,?_,se.trans (sb.trans sa)⟩
    · simpa only [noGood,ite_false] using endPC
    · simpa only [status,digit,Bool.false_eq_true,false_and,ite_false] using (source 1 (by decide) (by decide) (by decide)).trans h1
    · intro impossible;exact False.elim (Bool.false_ne_true impossible)
    · intro r _ h30 h12 h29 _ _;exact source r h30 h12 h29
  | true =>
    have atAccum : e.pc=0x8000321e#32 := by simpa only [digit,Bool.not_true,Bool.false_eq_true,ite_false] using p2
    have actualByte : e.get 30=BitVec.ofNat 32 byte.toNat := (fe 30).trans v30
    obtain ⟨z,t3,p3,low,high,fz,sz⟩ := HeadClAccumulate.contract B e ram acc byte atAccum
      ((source 14 (by decide) (by decide) (by decide)).trans h14)
      ((source 13 (by decide) (by decide) (by decide)).trans h13)
      ((source 16 (by decide) (by decide) (by decide)).trans h16) actualByte accepted digit
    obtain ⟨z2,t4,p4,v12',v29',fz2,sz2⟩ := HeadClOverflowRaw.contract B z ram sp 0#32 _ 1024#32
      ((fz 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((source 2 (by decide) (by decide) (by decide)).trans h2))
      high low hlimit stack aligned p3
    obtain ⟨d,t5,p5,fd,sd⟩ := HeadClOverflowBranch.contract B z2 ram _ (0 : Word) _ p4 v12' (Core.get_zero z2)
      (HeadClNumberMath.overflow_test (HeadClNumberMath.next acc byte) (HeadClNumberMath.next_bound acc byte accepted digit))
    have sourceD (r : Reg) (h30 : r≠30) (h12 : r≠12) (h29 : r≠29) (h14 : r≠14) (h13 : r≠13) : d.get r=c.get r :=
      (fd r).trans ((fz2 r h12 h29).trans ((fz r h12 h29 h14 h30 h13).trans (source r h30 h12 h29)))
    have dl : d.get 14=BitVec.ofNat 32 (HeadClNumberMath.next acc byte) := (fd 14).trans ((fz2 14 (by decide) (by decide)).trans low)
    have dh : d.get 13=0#32 := (fd 13).trans ((fz2 13 (by decide) (by decide)).trans high)
    by_cases tooLarge : 1024<HeadClNumberMath.next acc byte
    · have noGood : ¬good acc byte := by unfold good;omega
      have atLarge : d.pc=0x800034ce#32 := by simpa only [tooLarge,decide_true,ite_true] using p5
      obtain ⟨endCore,t6,p6,status413,fend,send⟩ := HeadHeaderPayloadLarge.contract B d ram atLarge
      change ∃ n d, _
      refine ⟨26,endCore,by decide,by decide,by simpa using ((((t0.trans t1).trans t2).trans t3).trans t4).trans (t5.trans t6),?_,?_,?_,?_,send.trans (sd.trans (sz2.trans (sz.trans (se.trans (sb.trans sa)))))⟩
      · simpa only [noGood,ite_false] using p6
      · simpa only [status,digit,tooLarge,true_and,ite_true] using status413
      · intro _;exact ⟨(fend 14 (by decide)).trans dl,(fend 13 (by decide)).trans dh⟩
      · intro r h1 h30 h12 h29 h14 h13
        exact (fend r h1).trans (sourceD r h30 h12 h29 h14 h13)
    · have isGood : good acc byte := ⟨digit,by omega⟩
      have endPC : d.pc=0x80003256#32 := by simpa only [tooLarge,decide_false,Bool.false_eq_true,ite_false] using p5
      change ∃ n d, _
      refine ⟨24,d,by decide,by decide,by simpa using ((((t0.trans t1).trans t2).trans t3).trans t4).trans t5,?_,?_,fun _ => ⟨dl,dh⟩,?_,sd.trans (sz2.trans (sz.trans (se.trans (sb.trans sa))))⟩
      · simpa only [isGood,ite_true] using endPC
      · simpa only [status,digit,tooLarge,and_false,ite_false] using (sourceD 1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1
      · intro r _ h30 h12 h29 h14 h13;exact sourceD r h30 h12 h29 h14 h13
end E5R.Thermostat.HeadClNumberStep
