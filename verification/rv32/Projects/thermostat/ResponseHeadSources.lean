import Projects.thermostat.ResponseHeadLiterals
import Projects.thermostat.ResponseHeadPlan
namespace E5R.Thermostat.ResponseHeadSources
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def ctName (ct : List (BitVec 8)) : Word := if ct=[] then 1#32 else ResponseHeadLiterals.pointer 1
def ctEnd (ct : List (BitVec 8)) : Word := if ct=[] then 1#32 else ResponseHeadLiterals.pointer 0
def clName (status : Nat) : Word := if ResponseHeadSpec.hasBody status then ResponseHeadLiterals.pointer 2 else 1#32
def clEnd (status : Nat) : Word := if ResponseHeadSpec.hasBody status then ResponseHeadLiterals.pointer 0 else 1#32
def connection (close : Bool) : Word := if close then ResponseHeadLiterals.pointer 3 else 1#32

theorem empty (ram : Word → BitVec 8) (p : Word) : ReadBytes.Span B img ram p [] := by
  refine ⟨by decide,?_,?_⟩
  · have := p.isLt;change p.toNat+0≤2^32;omega
  · intro i;have := i.isLt;simp at this

theorem disjoint_empty (p dst : Word) : WordRegions.Disjoint p 0 dst 192 := by
  intro i;have := i.isLt;omega

theorem ct_name (ram : Word → BitVec 8) (dst : Word) (ct : List (BitVec 8)) (hm : Memory.Block B dst 192) :
    ReadBytes.Span B img ram (ctName ct) (ResponseHeadPlan.ctName ct) ∧
    WordRegions.Disjoint (ctName ct) (ResponseHeadPlan.ctName ct).length dst 192 := by
  by_cases ht : ct=[]
  · simp only [ctName,ResponseHeadPlan.ctName,ht,ite_true,List.length_nil]
    exact ⟨empty ram _,disjoint_empty _ _⟩
  · simp only [ctName,ResponseHeadPlan.ctName,ht,ite_false]
    exact ⟨ResponseHeadLiterals.span ram 1,ResponseHeadLiterals.disjoint dst 192 hm 1⟩

theorem ct_end (ram : Word → BitVec 8) (dst : Word) (ct : List (BitVec 8)) (hm : Memory.Block B dst 192) :
    ReadBytes.Span B img ram (ctEnd ct) (ResponseHeadPlan.ctEnd ct) ∧
    WordRegions.Disjoint (ctEnd ct) (ResponseHeadPlan.ctEnd ct).length dst 192 := by
  by_cases ht : ct=[]
  · simp only [ctEnd,ResponseHeadPlan.ctEnd,ht,ite_true,List.length_nil]
    exact ⟨empty ram _,disjoint_empty _ _⟩
  · simp only [ctEnd,ResponseHeadPlan.ctEnd,ht,ite_false]
    exact ⟨ResponseHeadLiterals.span ram 0,ResponseHeadLiterals.disjoint dst 192 hm 0⟩

theorem cl_name (ram : Word → BitVec 8) (dst : Word) (status : Nat) (hm : Memory.Block B dst 192) :
    ReadBytes.Span B img ram (clName status) (ResponseHeadPlan.clName status) ∧
    WordRegions.Disjoint (clName status) (ResponseHeadPlan.clName status).length dst 192 ∧
    ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status) <<< 4=BitVec.ofNat 32 (ResponseHeadPlan.clName status).length := by
  cases hb : ResponseHeadSpec.hasBody status
  · simp only [clName,ResponseHeadPlan.clName,hb,Bool.false_eq_true,ite_false,List.length_nil]
    exact ⟨empty ram _,disjoint_empty _ _,by rfl⟩
  · simp only [clName,ResponseHeadPlan.clName,hb,ite_true]
    exact ⟨ResponseHeadLiterals.span ram 2,ResponseHeadLiterals.disjoint dst 192 hm 2,by rfl⟩

theorem cl_end (ram : Word → BitVec 8) (dst : Word) (status : Nat) (hm : Memory.Block B dst 192) :
    ReadBytes.Span B img ram (clEnd status) (ResponseHeadPlan.clEnd status) ∧
    WordRegions.Disjoint (clEnd status) (ResponseHeadPlan.clEnd status).length dst 192 ∧
    ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status) <<< 1=BitVec.ofNat 32 (ResponseHeadPlan.clEnd status).length := by
  cases hb : ResponseHeadSpec.hasBody status
  · simp only [clEnd,ResponseHeadPlan.clEnd,hb,Bool.false_eq_true,ite_false,List.length_nil]
    exact ⟨empty ram _,disjoint_empty _ _,by rfl⟩
  · simp only [clEnd,ResponseHeadPlan.clEnd,hb,ite_true]
    exact ⟨ResponseHeadLiterals.span ram 0,ResponseHeadLiterals.disjoint dst 192 hm 0,by rfl⟩

theorem connection_data (ram : Word → BitVec 8) (dst : Word) (close : Bool) (hm : Memory.Block B dst 192) :
    ReadBytes.Span B img ram (connection close) (ResponseHeadSpec.connection close) ∧
    WordRegions.Disjoint (connection close) (ResponseHeadSpec.connection close).length dst 192 ∧
    ((0 : Word)-ResponseHeadBodyMath.boolWord close) &&& 19#32=BitVec.ofNat 32 (ResponseHeadSpec.connection close).length := by
  cases close
  · exact ⟨empty ram _,disjoint_empty _ _,by rfl⟩
  · exact ⟨ResponseHeadLiterals.span ram 3,ResponseHeadLiterals.disjoint dst 192 hm 3,by rfl⟩
end E5R.Thermostat.ResponseHeadSources
