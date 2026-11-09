import Projects.thermostat.ResponseHeadSources
import Projects.thermostat.StackAccess
set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.StackResponseHeadSources
open E5R E5R.Thermostat ResponseHeadSources
abbrev B := StackBoard.board
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
    exact ⟨(StackAccess.rom_span (ResponseHeadLiterals.span ram 1) (ResponseHeadLiterals.outside 1)),ResponseHeadLiterals.disjoint dst 192 (StackAccess.block hm) 1⟩

theorem ct_end (ram : Word → BitVec 8) (dst : Word) (ct : List (BitVec 8)) (hm : Memory.Block B dst 192) :
    ReadBytes.Span B img ram (ctEnd ct) (ResponseHeadPlan.ctEnd ct) ∧
    WordRegions.Disjoint (ctEnd ct) (ResponseHeadPlan.ctEnd ct).length dst 192 := by
  by_cases ht : ct=[]
  · simp only [ctEnd,ResponseHeadPlan.ctEnd,ht,ite_true,List.length_nil]
    exact ⟨empty ram _,disjoint_empty _ _⟩
  · simp only [ctEnd,ResponseHeadPlan.ctEnd,ht,ite_false]
    exact ⟨(StackAccess.rom_span (ResponseHeadLiterals.span ram 0) (ResponseHeadLiterals.outside 0)),ResponseHeadLiterals.disjoint dst 192 (StackAccess.block hm) 0⟩

theorem cl_name (ram : Word → BitVec 8) (dst : Word) (status : Nat) (hm : Memory.Block B dst 192) :
    ReadBytes.Span B img ram (clName status) (ResponseHeadPlan.clName status) ∧
    WordRegions.Disjoint (clName status) (ResponseHeadPlan.clName status).length dst 192 ∧
    ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status) <<< 4=BitVec.ofNat 32 (ResponseHeadPlan.clName status).length := by
  cases hb : ResponseHeadSpec.hasBody status
  · simp only [clName,ResponseHeadPlan.clName,hb,Bool.false_eq_true,ite_false,List.length_nil]
    exact ⟨empty ram _,disjoint_empty _ _,by rfl⟩
  · simp only [clName,ResponseHeadPlan.clName,hb,ite_true]
    exact ⟨(StackAccess.rom_span (ResponseHeadLiterals.span ram 2) (ResponseHeadLiterals.outside 2)),ResponseHeadLiterals.disjoint dst 192 (StackAccess.block hm) 2,by rfl⟩

theorem cl_end (ram : Word → BitVec 8) (dst : Word) (status : Nat) (hm : Memory.Block B dst 192) :
    ReadBytes.Span B img ram (clEnd status) (ResponseHeadPlan.clEnd status) ∧
    WordRegions.Disjoint (clEnd status) (ResponseHeadPlan.clEnd status).length dst 192 ∧
    ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status) <<< 1=BitVec.ofNat 32 (ResponseHeadPlan.clEnd status).length := by
  cases hb : ResponseHeadSpec.hasBody status
  · simp only [clEnd,ResponseHeadPlan.clEnd,hb,Bool.false_eq_true,ite_false,List.length_nil]
    exact ⟨empty ram _,disjoint_empty _ _,by rfl⟩
  · simp only [clEnd,ResponseHeadPlan.clEnd,hb,ite_true]
    exact ⟨(StackAccess.rom_span (ResponseHeadLiterals.span ram 0) (ResponseHeadLiterals.outside 0)),ResponseHeadLiterals.disjoint dst 192 (StackAccess.block hm) 0,by rfl⟩

theorem connection_data (ram : Word → BitVec 8) (dst : Word) (close : Bool) (hm : Memory.Block B dst 192) :
    ReadBytes.Span B img ram (connection close) (ResponseHeadSpec.connection close) ∧
    WordRegions.Disjoint (connection close) (ResponseHeadSpec.connection close).length dst 192 ∧
    ((0 : Word)-ResponseHeadBodyMath.boolWord close) &&& 19#32=BitVec.ofNat 32 (ResponseHeadSpec.connection close).length := by
  cases close
  · exact ⟨empty ram _,disjoint_empty _ _,by rfl⟩
  · exact ⟨(StackAccess.rom_span (ResponseHeadLiterals.span ram 3) (ResponseHeadLiterals.outside 3)),ResponseHeadLiterals.disjoint dst 192 (StackAccess.block hm) 3,by rfl⟩
end E5R.Thermostat.StackResponseHeadSources
