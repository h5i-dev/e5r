import Projects.thermostat.MainRequestBodyGuards
import Projects.thermostat.MainRequestFront
import Projects.thermostat.MainRequestHighLoad
import Projects.thermostat.MainRequestStoreFrames
import Projects.thermostat.MainRequestHeadCopy
import Projects.thermostat.MainRequestPayloadHalves
import Projects.thermostat.MainSavedGpr
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.MainRequestPrefixCore
open E5R E5R.Thermostat

def body (ram : Word → BitVec 8) (sp rx : Word) (start finish : Nat) (method : Word) :=
  MainRequestBodyStores.memory ram sp (BitVec.ofNat 32 start+rx) (BitVec.ofNat 32 finish-BitVec.ofNat 32 start) method

def metadata (ram : Word → BitVec 8) (sp rx : Word) (start finish : Nat)
    (method path pathLen query queryLen tag pad low ms me ts te : Word) :=
  MainRequestMetadataStores.memory (body ram sp rx start finish method) sp path pathLen query queryLen tag pad low ms me ts te

def memory (ram : Word → BitVec 8) (sp rx : Word) (start finish : Nat)
    (method path pathLen query queryLen tag pad low ms me ts te : Word) :=
  MainRequestHeadCopy.memory (metadata ram sp rx start finish method path pathLen query queryLen tag pad low ms me ts te) sp

/-- Actual body guards, all Request/Head field stores, and real264-byte header
    copy, including both signed high-payload half loads and cached method byte. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp rx : Word) (start finish used : Nat)
    (method path pathLen query queryLen tag pad low ms me ts te : Word)
    (hp : c.pc=0x80001160#32) (h2 : c.get 2=sp) (h8 : c.get 8=sp+3204#32)
    (h20 : c.get 20=BitVec.ofNat 32 start) (h25 : c.get 25=BitVec.ofNat 32 finish) (h24 : c.get 24=BitVec.ofNat 32 used)
    (h21 : c.get 21=rx) (h14 : c.get 14=method) (h10 : c.get 10=path) (h28 : c.get 28=pathLen)
    (h12 : c.get 12=query) (h13 : c.get 13=queryLen) (h9 : c.get 9=tag) (h31 : c.get 31=pad)
    (h27 : c.get 27=low) (h7 : c.get 7=ms) (h11 : c.get 11=me) (h29 : c.get 29=ts) (h30 : c.get 30=te)
    (ordered : start≤finish) (available : finish≤used) (bound : used≤2048)
    (payload : MainServeNextPayloadWords.At ram sp) (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 388 ⟨c,ram⟩ ⟨d,memory ram sp rx start finish method path pathLen query queryLen tag pad low ms me ts te⟩ ∧
      d.pc=0x800011e2#32 ∧ d.get 20=BitVec.ofNat 32 start+rx ∧
      (∀ r∈MainSavedGpr.regs, r≠20 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨g,guards,pg,gr,gc⟩ := MainRequestBodyGuards.contract B c ram start finish used hp h20 h25 h24 ordered available bound
  have halves := MainRequestPayloadHalves.contract ram sp payload
  obtain ⟨a,front,pa,a15,a20,a16,a17,ar,ac⟩ := MainRequestFront.contract B g ram sp (BitVec.ofNat 32 start) (BitVec.ofNat 32 finish) rx
    ((gr 8).trans h8) stack aligned ((gr 20).trans h20) ((gr 25).trans h25) ((gr 21).trans h21) halves.1 halves.2.1 pg
  have fromC (r : Reg) (n15 : r≠15) (n20 : r≠20) (n16 : r≠16) (n17 : r≠17) : a.get r=c.get r := (ar r n15 n20 n16 n17).trans (gr r)
  have a8 : a.get 8=sp+3204#32 := (fromC 8 (by decide) (by decide) (by decide) (by decide)).trans h8
  have a14 : a.get 14=method := (fromC 14 (by decide) (by decide) (by decide) (by decide)).trans h14
  obtain ⟨b,stores,pb,br,bc⟩ := MainRequestBodyStores.contract B a ram sp _ _ method a8 stack aligned a20 a15 a14 pa
  let r1 := body ram sp rx start finish method
  have b8 : b.get 8=sp+3204#32 := (br 8).trans a8
  have hhalf : extend .h true (ramRead r1 (sp+4516#32) .h)=0#32 := by
    have region := MainRequestStoreFrames.body ram sp (BitVec.ofNat 32 start+rx) (BitVec.ofNat 32 finish-BitVec.ofNat 32 start) method 4516 2 (by decide) (Or.inr (by decide)) (Or.inr (by decide))
    have raw := MainHalfMemory.frame region 0 (by decide)
    simp only [BitVec.add_zero] at raw
    change ramRead r1 (sp+4516#32) .h=ramRead ram (sp+4516#32) .h at raw
    exact (congrArg (extend .h true) raw).trans payload.2
  obtain ⟨e,high,pe,e14,er,ec⟩ := MainRequestHighLoad.contract B b r1 sp b8 stack aligned hhalf pb
  have before (r : Reg) (n14 : r≠14) : e.get r=a.get r := (er r n14).trans (br r)
  have original (r : Reg) (n14 : r≠14) (n15 : r≠15) (n20 : r≠20) (n16 : r≠16) (n17 : r≠17) : e.get r=c.get r :=
    (before r n14).trans (fromC r n15 n20 n16 n17)
  obtain ⟨f,metaSteps,pf,f10,fr,fc⟩ := MainRequestMetadataStores.contract B e r1 sp path pathLen query queryLen tag pad low ms me ts te
    ((before 8 (by decide)).trans a8) stack aligned
    ((original 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2)
    ((original 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h10)
    ((original 28 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h28)
    ((original 12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h12)
    ((original 13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h13)
    ((before 16 (by decide)).trans a16) ((before 17 (by decide)).trans a17) e14
    ((original 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h9)
    ((original 31 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h31)
    ((original 27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h27)
    ((original 7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h7)
    ((original 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h11)
    ((original 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h29)
    ((original 30 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h30) pe
  have f2 : f.get 2=sp := (fr 2 (by decide)).trans ((original 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2)
  obtain ⟨d,copy,pd,d2,ds,dc⟩ := MainRequestHeadCopy.contract B f _ sp pf f2 stack aligned
  have af : MainSavedGpr.Frame a f := by
    intro r safe
    have ne : ∀ r : Reg, r∈MainSavedGpr.regs → r≠10 ∧ r≠14 := by decide +kernel
    obtain ⟨n10,n14⟩ := ne r safe
    exact (fr r n10).trans (before r n14)
  have fd : MainSavedGpr.Frame f d := MainSavedGpr.returned ds (d2.trans f2.symm)
  have ad := MainSavedGpr.trans af fd
  refine ⟨d,((((guards.trans front).trans stores).trans high).trans metaSteps).trans copy,pd,(ad 20 (by decide)).trans a20,?_,dc.trans (fc.trans (ec.trans (bc.trans (ac.trans gc))))⟩
  intro r safe n20
  have ne : ∀ r : Reg, r∈MainSavedGpr.regs → r≠15 ∧ r≠16 ∧ r≠17 := by decide +kernel
  obtain ⟨n15,n16,n17⟩ := ne r safe
  exact (ad r safe).trans (fromC r n15 n20 n16 n17)
end E5R.Thermostat.MainRequestPrefixCore
