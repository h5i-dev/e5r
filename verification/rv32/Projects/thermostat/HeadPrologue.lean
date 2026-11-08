import Projects.thermostat.HeadStackMemory
import Projects.thermostat.HeadMax
import Projects.thermostat.HeadMin
namespace E5R.Thermostat.HeadPrologue
open E5R E5R.Thermostat

/-- The real parser prologue saves all thirteen ABI registers, allocates
    exactly 384 stack bytes, reads the initialized max_head=1024, and computes
    the bounded scan length. Input bytes and output storage are still untouched. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (length : Nat)
    (hp : c.pc=0x80002c46#32) (h2 : c.get 2=sp+384#32) (h13 : c.get 13=sp+3664#32)
    (h12 : c.get 12=BitVec.ofNat 32 length) (hlen : length≤2048)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0)
    (hmax : ramRead ram (sp+3664#32) .w=1024#32) :
    ∃ steps d, 17≤steps ∧ steps≤18 ∧
      Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,HeadStackSave.memory ram sp c.get⟩ ∧
      d.pc=0x80002c88#32 ∧ d.get 2=sp ∧ d.get 14=BitVec.ofNat 32 (min length 1024) ∧ d.get 16=1024#32 ∧
      (∀ r : Reg, r≠2 → r≠14 → r≠16 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,save,pc1,stack,frame1,csr1⟩ := HeadStackSave.contract B c ram sp c.get h2 (fun _ _ => rfl)
    (by simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := 384) (by decide) (by decide)) ha hp
  let saved := HeadStackSave.memory ram sp c.get
  have max : ramRead saved (sp+3664#32) .w=1024#32 :=
    (HeadStackMemory.word ram sp c.get 3664 (by decide) (by decide)).trans hmax
  obtain ⟨b,read,pc2,v16,v14,frame2,csr2⟩ := HeadMax.contract B a saved (sp+3664#32) (BitVec.ofNat 32 length)
    ((frame1 13 (by decide)).trans h13) ((frame1 12 (by decide)).trans h12)
    (Memory.block_access hm (off := 3664) (by decide) (by decide)) (Memory.word_aligned sp 916 ha) max pc1
  have test : taken .ltu (BitVec.ofNat 32 length) 1024#32=decide (length<1024) := by
    simp only [taken,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : length<2^32)]
  obtain ⟨n,d,hlo,hn,select,pc3,limit,frame3,csr3⟩ := HeadMin.contract B b saved (BitVec.ofNat 32 length)
    (decide (length<1024)) pc2 ((frame2 12 (by decide) (by decide)).trans ((frame1 12 (by decide)).trans h12)) v14 v16 test
  refine ⟨14+2+n,d,by omega,by omega,(save.trans read).trans select,pc3,?_,?_,?_,?_,csr3.trans (csr2.trans csr1)⟩
  · exact (frame3 2 (by decide)).trans ((frame2 2 (by decide) (by decide)).trans stack)
  · by_cases short : length<1024
    · simpa only [short,decide_true,ite_true,Nat.min_eq_left (by omega : length≤1024)] using limit
    · simpa only [short,decide_false,Bool.false_eq_true,ite_false,Nat.min_eq_right (by omega : 1024≤length)] using limit
  · exact (frame3 16 (by decide)).trans v16
  · intro r h2 h14 h16
    exact (frame3 r h14).trans ((frame2 r h16 h14).trans (frame1 r h2))
end E5R.Thermostat.HeadPrologue
