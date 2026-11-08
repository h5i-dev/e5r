import Projects.thermostat.HeadClPreflight
import Projects.thermostat.HeadClEmptyBranch
import Projects.thermostat.HeadClNumberInit
import Projects.thermostat.HeadClNumber
namespace E5R.Thermostat.HeadClValue
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def outcome (g : Nat → Nat) (f : Fields) (vs ve le : Nat) : Num :=
  if HeadClPreflight.Bad f ve le then .bad 400 else contentLength g vs ve 1024

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (vs ve le length : Nat) (f : Fields)
    (hp : c.pc=0x800031dc#32) (h1 : c.get 1=400#32) (h2 : c.get 2=sp)
    (h23 : c.get 23=(if f.te then 1#32 else 0#32)) (h15 : c.get 15=BitVec.ofNat 32 vs)
    (h26 : c.get 26=BitVec.ofNat 32 le) (h11 : c.get 11=BitVec.ofNat 32 le) (h16 : c.get 16=10#32)
    (scratch : ramRead ram (sp+0#32) .w=BitVec.ofNat 32 le-BitVec.ofNat 32 ve)
    (hbuf : ramRead ram (sp+44#32) .w=buf) (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length)
    (hlimit : ramRead ram (sp+8#32) .w=1024#32) (fields : HeadFieldsView.At ram sp f)
    (ordered : vs≤ve ∧ ve≤le ∧ le≤length) (bound : length≤2048) (memory : Memory.Block B buf length)
    (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0) :
    let result := outcome (bytes ram buf) f vs ve le
    ∃ n d after, 7≤n ∧ n≤20+30*(ve-vs) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      HeadClNumber.Post ram after sp d result ∧ HeadFieldsView.At after sp (HeadClNumber.updated f result) ∧
      (∀ r : Reg, r≠1 → r≠30 → r≠12 → r≠29 → r≠14 → r≠13 → r≠11 → r≠10 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  have stack56 : Memory.Block B sp 56 := by
    simpa only [BitVec.add_zero] using (Memory.sub_block stack (off := 0) (m := 56) (by decide) (by decide))
  have stack327 : Memory.Block B sp 327 := by
    simpa only [BitVec.add_zero] using (Memory.sub_block stack (off := 0) (m := 327) (by decide) (by decide))
  obtain ⟨a,preflight,pc,frame,csr⟩ := HeadClPreflight.contract B c ram sp f ve le hp h2 h23 scratch fields ordered.2.1 (by omega) stack327 aligned
  by_cases bad : HeadClPreflight.Bad f ve le
  · have result : outcome g f vs ve le=.bad 400 := by simp only [outcome,bad,ite_true]
    have endPC : a.pc=0x8000342c#32 := by simpa only [bad,ite_true] using pc
    change ∃ n d after, _
    rw [show outcome (bytes ram buf) f vs ve le=.bad 400 from result]
    exact ⟨7,a,ram,by decide,by omega,preflight,⟨endPC,(frame 1 (by decide) (by decide)).trans h1,rfl⟩,fields,
      fun r _ _ h12 _ _ _ _ h10 _ => frame r h10 h12,csr⟩
  · have veEq : ve=le := by
      by_cases neq : ve≠le
      · exact False.elim (bad (Or.inr (Or.inr neq)))
      · omega
    have nextPC : a.pc=0x800031f2#32 := by simpa only [bad,ite_false] using pc
    have test : taken .geu (BitVec.ofNat 32 vs) (BitVec.ofNat 32 le)=decide (le≤vs) := by
      change (!decide ((BitVec.ofNat 32 vs).toNat<(BitVec.ofNat 32 le).toNat))=_
      rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : vs<2^32),Nat.mod_eq_of_lt (by omega : le<2^32)]
      rw [←decide_not]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq];omega
    obtain ⟨b,emptyCheck,pc2,frame2,csr2⟩ := HeadClEmptyBranch.contract B a ram _ _ _ nextPC
      ((frame 15 (by decide) (by decide)).trans h15) ((frame 26 (by decide) (by decide)).trans h26) test
    have source (r : Reg) (h10 : r≠10) (h12 : r≠12) : b.get r=c.get r := (frame2 r).trans (frame r h10 h12)
    by_cases empty : le≤vs
    · have result : outcome g f vs ve le=.bad 400 := by
        simp only [outcome,bad,ite_false,contentLength,show ve≤vs by omega,ite_true]
      have endPC : b.pc=0x8000342c#32 := by simpa only [empty,decide_true,ite_true] using pc2
      change ∃ n d after, _
      rw [show outcome (bytes ram buf) f vs ve le=.bad 400 from result]
      exact ⟨8,b,ram,by decide,by omega,by simpa using preflight.trans emptyCheck,
        ⟨endPC,(source 1 (by decide) (by decide)).trans h1,rfl⟩,fields,
        fun r _ _ h12 _ _ _ _ h10 _ => source r h10 h12,csr2.trans csr⟩
    · have inside : vs<ve := by omega
      have startPC : b.pc=0x800031f6#32 := by simpa only [empty,decide_false,Bool.false_eq_true,ite_false] using pc2
      obtain ⟨e,init,pc3,v14,v13,v10,v11,v30,v31,frame3,csr3⟩ := HeadClNumberInit.contract B b ram sp buf (BitVec.ofNat 32 vs) (BitVec.ofNat 32 le) (BitVec.ofNat 32 length)
        ((source 2 (by decide) (by decide)).trans h2) ((source 15 (by decide) (by decide)).trans h15)
        ((source 11 (by decide) (by decide)).trans h11) hbuf hraw stack56 aligned startPC
      have count : e.get 11=BitVec.ofNat 32 (ve-vs) := by
        rw [v11,BitVec.ofNat_sub_ofNat_of_le le vs (by omega) (by omega),←veEq]
      have raw : e.get 31=BitVec.ofNat 32 (length-vs) := by
        rw [v31,BitVec.ofNat_sub_ofNat_of_le length vs (by omega) (by omega)]
      obtain ⟨n,d,after,lo,hi,number,result,view,frame4,csr4⟩ := HeadClNumber.contract B e ram sp buf vs ve length 0 f pc3
        ((frame3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((source 1 (by decide) (by decide)).trans h1))
        ((frame3 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((source 2 (by decide) (by decide)).trans h2))
        v10 raw count v14 v13
        ((frame3 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((source 16 (by decide) (by decide)).trans h16))
        hlimit inside (by omega) bound (by decide) memory stack aligned fields
      have spec : outcome g f vs ve le=clLoop g ve 1024 0 vs := by
        simp only [outcome,bad,ite_false,contentLength,show ¬ve≤vs by omega,ite_false]
      change ∃ n d after, _
      rw [show outcome (bytes ram buf) f vs ve le=clLoop (bytes ram buf) ve 1024 0 vs from spec]
      refine ⟨7+1+7+n,d,after,by omega,by omega,((preflight.trans emptyCheck).trans init).trans number,result,view,?_,csr4.trans (csr3.trans (csr2.trans csr))⟩
      intro r h1 h30 h12 h29 h14 h13 h11 h10 h31
      exact (frame4 r h1 h30 h12 h29 h14 h13 h11 h10 h31).trans ((frame3 r h14 h13 h10 h11 h30 h31).trans (source r h10 h12))
end E5R.Thermostat.HeadClValue
