import Projects.thermostat.ResponseFieldCheck
import Projects.thermostat.ResponseFieldAdvance
set_option maxRecDepth 5000
namespace E5R.Thermostat.ResponseFieldLoop
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠29 → r≠30 → r≠31 → d.get r=c.get r

/-- Actual MIME field-value validation. Every checked RAM/ROM byte follows
    either the HTAB path or the non-control/non-DEL path; no MMIO is hidden. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src : Word) (xs : List (BitVec 8))
    (hne : xs≠[]) (hlen : xs.length≤16) (hp : c.pc=0x80003eb0#32)
    (h29 : c.get 29=src) (h30 : c.get 30=BitVec.ofNat 32 xs.length)
    (h6 : c.get 6=9#32) (h7 : c.get 7=32#32) (h28 : c.get 28=127#32)
    (hs : ReadBytes.Span B img ram src xs) (hf : ResponseHeadSpec.Field xs) :
    ∃ d n, n≤7*xs.length ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003ec2#32 ∧
      d.get 29=src+BitVec.ofNat 32 xs.length ∧ d.get 30=0#32 ∧ Frame c d ∧ d.sameCsr c := by
  induction xs generalizing c src with
  | nil => contradiction
  | cons v vs ih =>
    obtain ⟨a,k,hk,ta,pa,a31,ar,ac⟩ := ResponseFieldCheck.contract B c ram src v hp h29 h6 h7 h28 (ReadBytes.head hs) (hf v (by simp))
    obtain ⟨b,tb,pb,b30,b29,br,bc⟩ := ResponseFieldAdvance.contract B a ram src (v::vs).length (by simp) hlen
      ((ar 29 (by decide)).trans h29) ((ar 30 (by decide)).trans h30) pa
    have bf : Frame c b := fun r h29 h30 h31 => (br r h30 h29).trans (ar r h31)
    by_cases hz : vs=[]
    · subst vs
      refine ⟨b,k+3,?_,ta.trans tb,?_,b29,?_,bf,bc.trans ac⟩
      · simp only [List.length_cons,List.length_nil];omega
      · simpa only [List.length_cons,List.length_nil,ite_true] using pb
      · simpa only [List.length_cons,List.length_nil] using b30
    · have hn1 : (v::vs).length≠1 := by
        have hpvs := List.length_pos_iff.mpr hz
        simp only [List.length_cons];omega
      have hs' := ReadBytes.tail hs
      have hf' : ResponseHeadSpec.Field vs := fun w hw => hf w (List.mem_cons_of_mem v hw)
      have b30' : b.get 30=BitVec.ofNat 32 vs.length := by
        simpa only [List.length_cons,Nat.add_sub_cancel] using b30
      obtain ⟨d,n,hn,td,pd,d29,d30,dr,dc⟩ := ih b (src+1#32) hz (by simp only [List.length_cons] at hlen;omega)
        (by simpa only [ite_eq_right hn1] using pb) b29 b30'
        ((bf 6 (by decide) (by decide) (by decide)).trans h6)
        ((bf 7 (by decide) (by decide) (by decide)).trans h7)
        ((bf 28 (by decide) (by decide) (by decide)).trans h28) hs' hf'
      refine ⟨d,(k+3)+n,?_,(ta.trans tb).trans td,pd,?_,d30,?_,dc.trans (bc.trans ac)⟩
      · simp only [List.length_cons];omega
      · rw [d29,BitVec.add_assoc,←BitVec.ofNat_add,List.length_cons,Nat.add_comm 1 vs.length]
      · intro r h29 h30 h31
        exact (dr r h29 h30 h31).trans (bf r h29 h30 h31)
end E5R.Thermostat.ResponseFieldLoop
