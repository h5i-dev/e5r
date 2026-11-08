import Projects.thermostat.MainCloseCount
import Projects.thermostat.MainCloseSetup
import Projects.thermostat.MainCloseHeaderLoop
import Projects.thermostat.MainCloseResult
import Projects.thermostat.Header
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.MainCloseBody
open E5R E5R.Thermostat

def Stable (c d : Core) : Prop := ∀ r : Reg, r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=27 → d.get r=c.get r

/-- Complete actual wants_close body, before stack restoration. Its Boolean
    result is derived from every bounded raw header, not supplied by the caller. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (req rawPtr : Word)
    (raw : List (BitVec 8)) (entries : List HeaderSpec.Entry)
    (h : Header.Pre B ram req rawPtr raw entries) (limit : raw.length≤2048)
    (hp : c.pc=0x8000240a#32) (h10 : c.get 10=req) :
    ∃ n d, n≤(77+86*raw.length)*entries.length+26 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=0x8000267e#32 ∧ d.get 10=(if MainCloseSpec.wantsClose raw entries then 1#32 else 0#32) ∧ Stable c d ∧ d.sameCsr c := by
  obtain ⟨a,sa,pa,a11,ar,ac⟩ := MainCloseCount.contract B c ram req entries.length h.table.bounded hp h10 h.object h.aligned h.count
  by_cases empty : entries=[]
  · subst entries
    have ap : a.pc=0x8000267c#32 := by simpa only [List.length_nil,ite_true] using pa
    obtain ⟨n,d,nb,sd,pd,d10,dr,dc⟩ := MainCloseResult.contract B a ram false ap
    refine ⟨4+n,d,by simp only [List.length_nil,Nat.mul_zero];omega,sa.trans sd,pd,?_,?_,dc.trans ac⟩
    · simpa only [MainCloseSpec.wantsClose,List.any_nil,Bool.false_eq_true,ite_false] using d10
    · intro r safe;rcases safe with rfl|rfl|rfl|rfl|rfl <;> exact ((dr _ (by decide)).trans (ar _ (by decide) (by decide)))
  · have nonzero : entries.length≠0 := fun eq => empty (List.eq_nil_of_length_eq_zero eq)
    have ap : a.pc=0x80002418#32 := by simpa only [nonzero,ite_false] using pa
    have a10 : a.get 10=req := (ar 10 (by decide) (by decide)).trans h10
    obtain ⟨b,sb,pb,b13,b11,b16,b12,b17,b5,b6,b7,b28,b29,b30,b31,b8,b9,b18,b19,b21,b20,br,bc⟩ := MainCloseSetup.contract B a ram req rawPtr raw.length entries.length h.table.bounded a10 a11 h.object h.aligned h.pointer h.length ap
    obtain ⟨m,e,mb,se,pe,er,ec⟩ := MainCloseHeaderLoop.contract B ram rawPtr raw h.bytes limit entries (req+32#32) h.table empty b pb b13 b17 b12 b16 b5
      ⟨b6,b7,b28,b29,b30,b31⟩ ⟨⟨b6,b19,b7,b20⟩,b8,b9,b18,b21,b29⟩
    obtain ⟨k,d,kb,sd,pd,d10,dr,dc⟩ := MainCloseResult.contract B e ram (MainCloseSpec.wantsClose raw entries) pe
    refine ⟨4+20+m+k,d,by omega,((sa.trans sb).trans se).trans sd,pd,d10,?_,dc.trans (ec.trans (bc.trans ac))⟩
    intro r safe;rcases safe with rfl|rfl|rfl|rfl|rfl <;> exact (dr _ (by decide)).trans ((er _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (ar _ (by decide) (by decide))))
end E5R.Thermostat.MainCloseBody
