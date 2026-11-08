import Projects.thermostat.MainRequestPrefixFrame
import Projects.thermostat.MainRequestTailCore
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.MainRequestBuildCore
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp rx : Word) (start finish used : Nat)
    (method path pathLen query queryLen tag pad low ms me ts te minor : Word) :=
  MainRequestTailCore.memory (MainRequestPrefixCore.memory ram sp rx start finish method path pathLen query queryLen tag pad low ms me ts te) sp minor rx (BitVec.ofNat 32 used)

/-- Every real instruction of Request construction, both slice guards, the
    complete264-byte memcpy and complete36-byte memset. Initial RAM is arbitrary
    apart from the three explicitly read high-payload halfwords and minor word. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp rx : Word) (start finish used : Nat)
    (method path pathLen query queryLen tag pad low ms me ts te minor : Word)
    (hp : c.pc=0x80001160#32) (h2 : c.get 2=sp) (h8 : c.get 8=sp+3204#32)
    (h20 : c.get 20=BitVec.ofNat 32 start) (h25 : c.get 25=BitVec.ofNat 32 finish) (h24 : c.get 24=BitVec.ofNat 32 used)
    (h21 : c.get 21=rx) (h14 : c.get 14=method) (h10 : c.get 10=path) (h28 : c.get 28=pathLen)
    (h12 : c.get 12=query) (h13 : c.get 13=queryLen) (h9 : c.get 9=tag) (h31 : c.get 31=pad)
    (h27 : c.get 27=low) (h7 : c.get 7=ms) (h11 : c.get 11=me) (h29 : c.get 29=ts) (h30 : c.get 30=te)
    (hminor : ramRead ram (sp+40#32) .w=minor)
    (ordered : start≤finish) (available : finish≤used) (bound : used≤2048)
    (payload : MainServeNextPayloadWords.At ram sp) (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 460 ⟨c,ram⟩ ⟨d,memory ram sp rx start finish used method path pathLen query queryLen tag pad low ms me ts te minor⟩ ∧
      d.pc=0x80001246#32 ∧ d.get 9=minor ∧ d.get 20=BitVec.ofNat 32 start+rx ∧
      (∀ r∈MainRequestSaved.regs, r≠20 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,prefixSteps,pa,a20,ar,ac⟩ := MainRequestPrefixCore.contract B c ram sp rx start finish used method path pathLen query queryLen tag pad low ms me ts te
    hp h2 h8 h20 h25 h24 h21 h14 h10 h28 h12 h13 h9 h31 h27 h7 h11 h29 h30 ordered available bound payload stack aligned
  let first := MainRequestPrefixCore.memory ram sp rx start finish method path pathLen query queryLen tag pad low ms me ts te
  have word : ramRead first (sp+40#32) .w=minor := by
    have region := MainRequestPrefixFrame.contract ram sp rx start finish method path pathLen query queryLen tag pad low ms me ts te 40 4 (by decide) (Or.inl (by decide))
    have kept := ViewFrame.word region 0 (by decide)
    simp only [BitVec.add_zero] at kept
    exact kept.trans hminor
  obtain ⟨d,tail,pd,d9,dr,dc⟩ := MainRequestTailCore.contract B a first sp minor rx (BitVec.ofNat 32 used) pa
    ((ar 2 (by decide) (by decide)).trans h2) ((ar 8 (by decide) (by decide)).trans h8)
    ((ar 21 (by decide) (by decide)).trans h21) ((ar 24 (by decide) (by decide)).trans h24) word stack aligned
  refine ⟨d,prefixSteps.trans tail,pd,d9,(dr 20 (by decide)).trans a20,?_,dc.trans ac⟩
  intro r safe n20
  have subset : ∀ r : Reg, r∈MainRequestSaved.regs → r∈MainSavedGpr.regs := by decide +kernel
  exact (dr r safe).trans (ar r (subset r safe) n20)
end E5R.Thermostat.MainRequestBuildCore
